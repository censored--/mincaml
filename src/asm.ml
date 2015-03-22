(* MIPS assembly with a few virtual instructions *)

type id_or_imm = V of Id.t | C of int
type t = (* 命令の列 *)
  | Ans of exp
  | Let of (Id.t * Type.t) * exp * t
and exp = (* 一つ一つの命令に対応する式 *)
  | Nop
  | Li of int
  | FLi of float
  | SetL of Id.l
  | Mr of Id.t
  | Neg of Id.t
  | Add of Id.t * id_or_imm
  | Sub of Id.t * id_or_imm
  | Mul of Id.t * id_or_imm
  | Div of Id.t * id_or_imm
  | Sll of Id.t * id_or_imm
  | Srl of Id.t * id_or_imm
  | Sra of Id.t * id_or_imm
  | Slw of Id.t * id_or_imm(*16bit左シフトして格納*)
  | Lw of Id.t * id_or_imm
  | Sw of Id.t * Id.t * id_or_imm
  | FMov of Id.t 
  | FNeg of Id.t
  | FInv of Id.t
  | FAdd of Id.t * Id.t
  | FSub of Id.t * Id.t
  | FMul of Id.t * Id.t
  | FDiv of Id.t * Id.t
  | Lfd of Id.t * id_or_imm
  | Stfd of Id.t * Id.t * id_or_imm
  | Comment of string
  (* virtual instructions *)
  | IfEq of Id.t * id_or_imm * t * t
  | IfLE of Id.t * id_or_imm * t * t
  | IfGE of Id.t * id_or_imm * t * t
  | IfFEq of Id.t * Id.t * t * t
  | IfFLE of Id.t * Id.t * t * t
  (* closure address, integer arguments, and float arguments *)
  | CallCls of Id.t * Id.t list * Id.t list
  | CallDir of Id.l * Id.t list * Id.t list
  | Save of Id.t * Id.t (* レジスタ変数の値をスタック変数へ保存 *)
  | Restore of Id.t (* スタック変数から値を復元 *)
type fundef =
    { name : Id.l; args : Id.t list; fargs : Id.t list; body : t; ret : Type.t }
(* プログラム全体 = トップレベル関数 + メインの式 *)
type prog = Prog of fundef list * t

type fundata = {argreg:Id.t list; fargreg:Id.t list; retreg: Id.t; mutable usereg: S.t}



(* shorthand of Let for float *)
(* fletd : Id.t * exp * t -> t *)
let fletd (x, e1, e2) = Let ((x, Type.Float (-1)), e1, e2)
(* shorthand of Let for unit *)
(* seq : exp * t -> t *)
let seq (e1, e2) = Let ((Id.gentmp Type.Unit, Type.Unit), e1, e2)

let regs = [|"%v0";"%v1";"%a0";"%a1";"%a2";"%a3";"%t0";"%t1";"%t2"; 
  "%t3";"%t4";"%t5"; "%t6"; "%t7"; "%s0"; "%s1"; "%s2"; 
  "%s3"; "%s4"; "%s5"; "%s6"; "%s7"; "%t8";"%t9"; "%k0"; "%k1"; "%fp"|]
(* let regs = Array.init 26 (fun i -> Printf.sprintf "_R_%d" i) *)
let fregs = Array.init 32 (fun i -> Printf.sprintf "%%f%d" i)
let allregs = Array.to_list regs
let allfregs = Array.to_list fregs
let reg_cl = "%fp" (* closure address *)
let reg_sw = regs.(Array.length regs - 2) (* temporary for swap *)
let reg_fsw = fregs.(Array.length fregs - 1) (* temporary for swap *)
let reg_rp = "ra"(*$31*)
let reg_hp = "%gp"(*$28*)
let reg_fp = "fp"(*$29*)
let reg_sp = "sp"(*$30*)
let reg_clo= "k1"
let reg_tmp= "at"(*$1*)
let reg_rt = [|"%v0";"%v1"|]
let regs_arg= [|"%a0";"%a1";"%a2";"%a3";"%t0";"%t1";"%t2"; 
  "%t3";"%t4";"%t5"; "%t6"; "%t7"; "%t8"; "%t9"; "%s0"; "%s1"; "%s2"; 
  "%s3"; "%s4"; "%s5"; "%s6"; "%s7"|]

let funlist 
  = ref (M.add_list 
	   [("min_caml_print_int",{argreg=["%a0"];fargreg=[];retreg="%dummy";usereg= S.of_list []});
	    ("_min_caml_main",{argreg=[];fargreg=[];retreg="%dummy";usereg = S.of_list(allregs@allfregs)})]
	    M.empty)

let get_fundata name = M.find name !funlist



(* is_reg : Id.t -> bool *)
let is_reg x = x.[0] = '%'

(* remove_and_uniq : S.t -> Id.t list -> Id.t list *)
let rec remove_and_uniq xs = function 
  | [] -> []
  | x :: ys when S.mem x xs -> remove_and_uniq xs ys
  | x :: ys -> x :: remove_and_uniq (S.add x xs) ys

(* free variables in the order of use (for spilling) *)
(* fv_id_or_imm : id_or_imm -> Id.t list *)
let fv_id_or_imm = function V (x) -> [x] | _ -> []
(* fv_exp : Id.t list -> t -> S.t list *)
let rec fv_exp = function
  | Nop | Li (_) | FLi (_) | SetL (_) | Comment (_) | Restore (_) -> []
  | Mr (x) | Neg (x) | FMov (x) | FNeg (x) | FInv (x)| Save (x, _) -> [x]
  | Add (x, y') | Sub (x, y') | Mul (x, y') | Div (x, y')
  | Slw (x, y') | Lfd (x, y') | Lw (x, y')
  | Sll (x, y') | Srl (x, y') | Sra (x, y') ->
      x :: fv_id_or_imm y'
  | FAdd (x, y) | FSub (x, y) | FMul (x, y) | FDiv (x, y) ->
      [x;y]
  | Sw (x, y, z') | Stfd (x, y, z') -> x :: y :: fv_id_or_imm z'
  | IfEq (x, y', e1, e2) | IfLE (x, y', e1, e2) | IfGE (x, y', e1, e2) -> 
      x :: fv_id_or_imm y' @ remove_and_uniq S.empty (fv e1 @ fv e2)
  | IfFEq (x, y, e1, e2) | IfFLE (x, y, e1, e2) ->
      x :: y :: remove_and_uniq S.empty (fv e1 @ fv e2)
  | CallCls (x, ys, zs) -> x :: ys @ zs
  | CallDir (_, ys, zs) -> ys @ zs
and fv = function 
  | Ans (exp) -> fv_exp exp
  | Let ((x, t), exp, e) ->
      fv_exp exp @ remove_and_uniq (S.singleton x) (fv e)

(* fv : t -> Id.t list *)
let fv e = remove_and_uniq S.empty (fv e)

(* concat : t -> Id.t * Type.t -> t -> t *)
let rec concat e1 xt e2 = match e1 with
  | Ans (exp) -> Let (xt, exp, e2)
  | Let (yt, exp, e1') -> Let (yt, exp, concat e1' xt e2)

(* align : int -> int *)
let align i = if i mod 2 = 0 then i else i + 1

let pp_i fmt = function
  |V(x)-> Format.fprintf fmt "V(%a)" Id.pp x
  |C(x)-> Format.fprintf fmt "C(%d)" x

(*{argreg:Id.t list; fargreg:Id.t list; retreg: Id.t; usereg: S.t}*)
let fprint_funlist fmt () = 
  Format.fprintf fmt "[fundata]@.";
  
  M.fold
    (fun name {argreg=args; fargreg=fargs; retreg=ret; usereg=regs} _->
     Format.fprintf fmt "(%s,\t{argreg = %s;\n\t\tfargreg = %s;\n\t\tretreg = %s;\n\t\tusereg = %s})@."
    name (Id.t_list_to_string args) (Id.t_list_to_string fargs) ret (S.to_string regs))
    !funlist ()

let eprint_funlist () = Format.eprintf "%a" fprint_funlist ()


(*{ name : Id.l; args : Id.t list; fargs : Id.t list; body : t; ret : Type.t }*)
let rec p_f fmt = function
  |[]->()
  |[{name=x;args=y;fargs=z;body=w;ret=u}]->
    Format.fprintf fmt "{funname = %a,@. args =[%a],@. fargs=[%a],@. body=@.%a, ret=%a}@."
		   Id.pp_l x Id.p_list y Id.p_list z p_t w Type.pp u
  |{name=x;args=y;fargs=z;body=w;ret=u}::xs->
    Format.fprintf fmt "{name = %a,@. args =%a,@. fargs=%a,@. body=@.%a, ret=%a}@.%a"
		   Id.pp_l x Id.p_list y Id.p_list z p_t w Type.pp u p_f xs

and p_t fmt = function
  |Ans(x)->
    Format.fprintf fmt "asm \t%a" p_e x
  |Let((x,y),z,w)-> 
    Format.fprintf fmt "let %a:%a  = %a\tin\n%a"
		   Id.pp x Type.pp y p_e z p_t w
and p_e fmt = function
  | Nop -> 
     Format.fprintf fmt "nop"
  | Li(x)-> 
     Format.fprintf fmt "li   %d" x  
  | FLi(x)-> 
     Format.fprintf fmt "fli  %f" x
  | SetL(x)-> 
     Format.fprintf fmt "setl %a" Id.pp_l x
  | Mr(x)-> 
     Format.fprintf fmt "mr   %a" Id.pp x
  | Neg(x)-> 
     Format.fprintf fmt "neg  %a" Id.pp x
  | Add(x,y)-> 
     Format.fprintf fmt "add  %a, %a" Id.pp x pp_i y
  | Sub(x,y)-> 
     Format.fprintf fmt "sub  %a, %a" Id.pp x pp_i y
  | Mul(x,y)-> 
     Format.fprintf fmt "mult %a, %a" Id.pp x pp_i y
  | Div(x,y)-> 
     Format.fprintf fmt "div  %a, %a" Id.pp x pp_i y
  | Sll(x,y)-> 
     Format.fprintf fmt "sll %a, %a" Id.pp x pp_i y
  | Srl(x,y)-> 
     Format.fprintf fmt "srl %a, %a" Id.pp x pp_i y
  | Sra(x,y)-> 
     Format.fprintf fmt "sra %a, %a" Id.pp x pp_i y
  | Slw(x,y)-> 
     Format.fprintf fmt "slw  %a, %a" Id.pp x pp_i y
  | Lw(x,y)-> 
     Format.fprintf fmt "lw   %a, %a" Id.pp x pp_i y 
  | Sw(x,y,z)->
     Format.fprintf fmt "sw  %a, %a, %a" Id.pp x Id.pp y pp_i z
  | FMov(x)->
     Format.fprintf fmt "fmov %a" Id.pp x
  | FNeg(x)->
     Format.fprintf fmt "fneg %a" Id.pp x
  | FInv(x)->
     Format.fprintf fmt "finv %a" Id.pp x
  | FAdd(x,y)->
     Format.fprintf fmt "fadd %a, %a" Id.pp x Id.pp y
  | FSub(x,y)->
     Format.fprintf fmt "fsub %a, %a" Id.pp x Id.pp y
  | FMul(x,y)->
     Format.fprintf fmt "fmul %a, %a" Id.pp x Id.pp y
  | FDiv(x,y)->
     Format.fprintf fmt "fdiv %a, %a" Id.pp x Id.pp y
  | Lfd(x,y)->
     Format.fprintf fmt "lfd  %a, %a" Id.pp x pp_i y
  | Stfd(x,y,z)->
     Format.fprintf fmt "stfd %a, %a, %a" Id.pp x Id.pp y pp_i z
  | Comment(x)->
     Format.fprintf fmt "#%s" x
  (* virtual instructions *)
  | IfEq(x,y,z,w)->
     Format.fprintf fmt "beq  %a, %a, then@."Id.pp x pp_i y;
     Format.fprintf fmt "then:@.\t%a@.else:@.\t%a" p_t z p_t w
  | IfLE(x,y,z,w)->
     Format.fprintf fmt "ble  %a, %a, then@."Id.pp x pp_i y;
     Format.fprintf fmt "then:@.\t%a@.else:@.\t%a" p_t z p_t w
  | IfGE(x,y,z,w)->
     Format.fprintf fmt "bge  %a, %a, then@."Id.pp x pp_i y;
     Format.fprintf fmt "then:@.\t%a@.else:@.\t%a" p_t z p_t w
  | IfFEq(x,y,z,w)->
     Format.fprintf fmt "bfeq %a, %a, then@."Id.pp x Id.pp y;
     Format.fprintf fmt "then:@.\t%a@.else:@.\t%a" p_t z p_t w
  | IfFLE(x,y,z,w)->
     Format.fprintf fmt "bfeq %a, %a, then@."Id.pp x Id.pp y;
     Format.fprintf fmt "then:@.\t%a@.else:@.\t%a" p_t z p_t w
  (* closure address, integer arguments, and float arguments *)
  | CallCls(x,y,z)->
     Format.fprintf fmt "CallCls %a, [%a], [%a]"
		    Id.pp x Id.p_list y Id.p_list z
  | CallDir(x,y,z)->
     Format.fprintf fmt "CallDir %a, [%a], [%a]"
		    Id.pp_l x Id.p_list y Id.p_list z
  | Save(x,y)->(* レジスタ変数の値をスタック変数へ保存 *)
     Format.fprintf fmt "save %a, %a" Id.pp x Id.pp y
  | Restore(x)->(* スタック変数から値を復元 *)
     Format.fprintf fmt "restore %a" Id.pp x


let p (Prog (fundefs,e)) = 
  Format.fprintf Format.err_formatter 
		 "Asm:@.[top-level functions definition]@.%a@.[main formula]@.%a@."
		 p_f fundefs p_t e

let string_of_id_or_imm = function
  |V x -> x 
  |C x -> string_of_int x
