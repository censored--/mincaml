open Format

type t = 
  | Li of (Id.t * Type.t) * int
  | FLi of (Id.t * Type.t) * float
  | SetL of (Id.t * Type.t) *  Id.l
  | Mr of (Id.t * Type.t) * Id.t
  | Neg of (Id.t * Type.t) * Id.t
  | Add of (Id.t * Type.t) * Id.t * Asm.id_or_imm
  | Sub of (Id.t * Type.t) * Id.t * Asm.id_or_imm
  | Mul of (Id.t * Type.t) * Id.t * Asm.id_or_imm
  | Div of (Id.t * Type.t) * Id.t * Asm.id_or_imm
  | Sll of (Id.t * Type.t) * Id.t * Asm.id_or_imm
  | Srl of (Id.t * Type.t) * Id.t * Asm.id_or_imm
  | Sra of (Id.t * Type.t) * Id.t * Asm.id_or_imm
  | Slw of (Id.t * Type.t) * Id.t * Asm.id_or_imm(*16bit左シフトして格納*)
  | Lw of (Id.t * Type.t) * Id.t * Asm.id_or_imm
  | Sw of (Id.t * Type.t) * Id.t * Id.t * Asm.id_or_imm
  | FMov of (Id.t * Type.t) * Id.t 
  | FNeg of (Id.t * Type.t) * Id.t
  | FInv of (Id.t * Type.t) * Id.t
  | FAdd of (Id.t * Type.t) * Id.t * Id.t
  | FSub of (Id.t * Type.t) * Id.t * Id.t
  | FMul of (Id.t * Type.t) * Id.t * Id.t
  | FDiv of (Id.t * Type.t) * Id.t * Id.t
  | Lfd of (Id.t * Type.t) * Id.t * Asm.id_or_imm
  | Stfd of (Id.t * Type.t) * Id.t * Id.t * Asm.id_or_imm
  (* virtual instructions *)
  | IfEq of (Id.t * Type.t) * Id.t * Asm.id_or_imm * Id.t * Id.t  (*if文での最後2つの引数はthenブロックとelseブロックのID*)
  | IfLE of (Id.t * Type.t) * Id.t * Asm.id_or_imm * Id.t * Id.t
  | IfGE of (Id.t * Type.t) * Id.t * Asm.id_or_imm * Id.t * Id.t
  | IfFEq of (Id.t * Type.t) * Id.t * Id.t * Id.t * Id.t
  | IfFLE of (Id.t * Type.t) * Id.t * Id.t * Id.t * Id.t
  (* closure address, integer arguments, and float arguments *)
  | CallCls of (Id.t * Type.t) * Id.t * Id.t list * Id.t list
  | CallDir of (Id.t * Type.t) * Id.l * Id.t list * Id.t list
  | Save of (Id.t * Type.t) * Id.t * Id.t (* レジスタ変数の値をスタック変数へ保存 *)
  | Restore of (Id.t * Type.t) * Id.t (* スタック変数から値を復元 *)


(*命令*)
type statement = {
  mutable s_id      : Id.t;  (*命令のId*)
  mutable s_parent  : Id.t;  (*属するブロックのId*)
  mutable inst    :  t;    (*命令の内容*)
  mutable pred    : Id.t;  (*前の命令*)
  mutable succ    : Id.t;  (*次の命令*)
  mutable v_livein  : S.t;(*入り口での生存変数名*)
  mutable v_liveout : S.t;(*出口での生存変数名*)
}

(*基本ブロック*)
and block = {
  mutable b_id: Id.t;
  mutable b_parent : Id.l;
  mutable stmts : statement M.t;
  mutable s_head : Id.t;
  mutable s_tail : Id.t;
  mutable preds : Id.t list;
  mutable succs : Id.t list;
  mutable s_livein : S.t;
  mutable s_liveout : S.t;
}

(*関数*)
and fundef = {
  mutable name : Id.l;
  mutable args : Id.t list;
  mutable fargs : Id.t list;
  mutable ret : Type.t;
  mutable blocks : block M.t;
  mutable b_head : Id.t;
  mutable use_regs : Id.t list;(*registers to be stored before executing this function*)
}

type prog = Prog of fundef list * fundef

(*debug print functions*)

let string_of_S set =
  let s = S.elements set in
  let rec s_of_S = function
    |x::xs-> x^";"^s_of_S xs
    |[]->"" in s_of_S s

let p_t fmt = function
  | Li ((x,t),y)->eprintf "Li((%s,%a),%d)" x Type.pp t y
  | FLi((x,t),y)->eprintf "FLi((%s,%a),%f)" x Type.pp t y
  | SetL((x,t),y)->eprintf "FLi((%s,%a),%a)" x Type.pp t Id.pp_l y
  | Mr((x,t),y)->eprintf "Mr((%s,%a),%s)" x Type.pp t y
  | Neg((x,t),y)->eprintf "Mr((%s,%a),%s)" x Type.pp t y
  | Add((x,t),y,z)->eprintf "Add((%s,%a),%s,%s)" x Type.pp t y (Asm.string_of_id_or_imm z)
  | Sub((x,t),y,z)->eprintf "Sub((%s,%a),%s,%s)" x Type.pp t y (Asm.string_of_id_or_imm z)
  | Mul((x,t),y,z)->eprintf "Mul((%s,%a),%s,%s)" x Type.pp t y (Asm.string_of_id_or_imm z)
  | Div((x,t),y,z)->eprintf "Div((%s,%a),%s,%s)" x Type.pp t y (Asm.string_of_id_or_imm z)
  | Sll((x,t),y,z)->eprintf "Sll((%s,%a),%s,%s)" x Type.pp t y (Asm.string_of_id_or_imm z)
  | Srl((x,t),y,z)->eprintf "Srl((%s,%a),%s,%s)" x Type.pp t y (Asm.string_of_id_or_imm z)
  | Sra((x,t),y,z)->eprintf "Sra((%s,%a),%s,%s)" x Type.pp t y (Asm.string_of_id_or_imm z)
  | Slw((x,t),y,z)->eprintf "Slw((%s,%a),%s,%s)" x Type.pp t y (Asm.string_of_id_or_imm z)
  | Lw((x,t),y,z)->eprintf "Lw((%s,%a),%s,%s)" x Type.pp t y (Asm.string_of_id_or_imm z)
  | Sw((x,t),y,z,w)->eprintf "Sw((%s,%a),%s,%s,%s)" x Type.pp t y z (Asm.string_of_id_or_imm w)
  | FMov((x,t),y)->eprintf "FMov((%s,%a),%s)" x Type.pp t y
  | FNeg((x,t),y)->eprintf "FNeg((%s,%a),%s)" x Type.pp t y
  | FInv((x,t),y) ->eprintf "FInv((%s,%a),%s)" x Type.pp t y
  | FAdd((x,t),y,z) ->eprintf "FAdd((%s,%a),%s,%s)" x Type.pp t y z
  | FSub((x,t),y,z) ->eprintf "FSub((%s,%a),%s,%s)" x Type.pp t y z
  | FMul((x,t),y,z) ->eprintf "FMul((%s,%a),%s,%s)" x Type.pp t y z
  | FDiv((x,t),y,z) ->eprintf "FDiv((%s,%a),%s,%s)" x Type.pp t y z
  | Lfd((x,t),y,z)->eprintf "Lfd((%s,%a),%s,%s)" x Type.pp t y (Asm.string_of_id_or_imm z)
  | Stfd((x,t),y,z,w)->eprintf"Stfd((%s,%a),%s,%s,%s)"x Type.pp t y z (Asm.string_of_id_or_imm w)
  | IfEq((x,t),y,z,w,v)->eprintf "IfEq((%s,%a),%s,%s,%s,%s)" x Type.pp t y (Asm.string_of_id_or_imm z) w v
  | IfLE((x,t),y,z,w,v)->eprintf "IfLE((%s,%a),%s,%s,%s,%s)" x Type.pp t y (Asm.string_of_id_or_imm z) w v
  | IfGE((x,t),y,z,w,v)->eprintf "IfGE((%s,%a),%s,%s,%s,%s)" x Type.pp t y (Asm.string_of_id_or_imm z) w v
  | IfFEq((x,t),y,z,w,v)->eprintf "IfFEq((%s,%a),%s,%s,%s,%s)" x Type.pp t y z w v
  | IfFLE((x,t),y,z,w,v)->eprintf "IfFLE((%s,%a),%s,%s,%s,%s)" x Type.pp t y z w v
  | CallCls((x,t),y,z,w)->eprintf "CallCls((%s,%a),%s,[%a],[%a])" x Type.pp t y Id.p_list z Id.p_list w
  | CallDir((x,t),y,z,w)->eprintf "CallDir((%s,%a),%a,[%a],[%a])" x Type.pp t Id.pp_l y Id.p_list z Id.p_list w
  | Save((x,t),y,z)->eprintf "Save((%s,%a),%s,%s)" x Type.pp t y z
  | Restore((x,t),y)->eprintf "Restore((%s,%a),%s)" x Type.pp t y

let print_t x = eprintf "%a@." p_t x

let p_statement fmt { s_id=sd;  s_parent = sp; inst = inst; pred = pd; succ = sc; v_livein = vi; v_liveout = vo} =
  Format.eprintf "[s_id]%s\t[instruction]%a\t[pred]%s\t[succ]%s\n\t\t\t\t[livein]%s\t[liveout]%s@."
		 sd p_t inst pd sc (string_of_S vi) (string_of_S vo)

let print_statement x = p_statement Format.err_formatter x

let p_block fmt {b_id = bi;b_parent = Id.L bp; stmts = sm; s_head = sh; s_tail = st; preds = pd; succs = sc; s_livein = sli; s_liveout = slo} =
  let rec string_of_list = function
    |x::xs->x^", "^string_of_list xs
    |[]->"" in
  let rec p_stmts fmt = function
    |x::xs->eprintf "\t\t"; p_statement fmt x; p_stmts fmt xs
    |[]->() in
  Format.fprintf fmt "[b_id]%s\n\t[statements]\n%a\n\t[b_parent]%s\n\t[s_head]%s\t[s_tail]%s\n\t[succs]%s\n\t[live in]%s\t[live out] %s"
		 bi p_stmts (List.map snd (M.bindings sm)) bp sh st (string_of_list sc) 
		 (string_of_list (S.elements sli)) (string_of_list (S.elements slo))

let print_block x = eprintf "%a@." p_block x

let print_fundef {name= Id.L n;args=a;fargs = f;ret = r;blocks = blks; b_head = b;use_regs = u} =
    Format.eprintf "[name]%s\t[b_head]%s@." n b;
    let rec print_blks x = match x with
      |(x1,x2)::xs->Format.eprintf "%a@." p_block x2;print_blks xs
      |_->Format.eprintf "@." in
    print_blks (M.bindings blks)

let print (Prog(fundefs,fundef)) =
  let rec p = function
    |f::fs-> print_fundef f;p fs
    |[]->() in
  p fundefs; print_fundef fundef

let statement_id = ref 100000
let block_id = ref 100000
let gen_statement_id () = statement_id:= !statement_id + 1; "s_"^string_of_int (!statement_id) 
let gen_block_id () = block_id:= !block_id + 1; "b_"^string_of_int (!block_id) 


(*xという基本ブロックをpreds,succs情報と共に作成*)
let new_block x p s = 
  let block = {b_id = x;
	       b_parent = Id.L "";
	       stmts = M.empty;
	       s_head = "";
	       s_tail = "";
	       preds = p;
	       succs = s;
	       s_livein = S.empty;
	       s_liveout = S.empty} in
  block

let add_block b f =
  (*let Id.L x = f.name in Format.eprintf "newblock: %s in %s@." b.b_id x;*)
  List.iter (fun x -> let pred = M.find x f.blocks in if not (List.mem b.b_id pred.succs) then pred.succs <- b.b_id::pred.succs) b.preds;
  b.b_parent <- f.name;
  f.blocks<- M.add b.b_id b f.blocks

let add_statement e b =
  let sid = gen_statement_id () in
  let s = {s_id = sid;
	   s_parent = b.b_id;
	   inst = e;
	   pred = "";
	   succ = "";
	   v_livein = S.empty;
	   v_liveout = S.empty} in
  if M.is_empty b.stmts 
  then (b.s_head <- sid;
	b.s_tail <- sid)
  else (s.pred <- b.s_tail;
	b.s_tail <- sid;
	assert (M.mem s.pred b.stmts);
	(M.find s.pred b.stmts).succ <- sid);
  b.stmts <- M.add sid s b.stmts  

let replace stmt a b  =
  let rp x =  if x = a then b else x in
  let rpcv x = match x with 
    |Asm.V x->Asm.V (rp x) 
    | e -> e in
  match stmt.inst with
  | Li ((x,t),y)->Li((rp x,t),y)
  | FLi((x,t),y)->FLi((rp x,t),y)
  | SetL((x,t),y)-> SetL((rp x,t),y)
  | Mr ((x,t),y)->Mr ((rp x,t),rp y)
  | Neg ((x,t),y)->Neg ((rp x,t),rp y)
  | Add ((x,t),y,z)->Add ((rp x, t),rp y,rpcv z)
  | Sub ((x,t),y,z)->Sub ((rp x, t),rp y,rpcv z)
  | Mul ((x,t),y,z)->Mul ((rp x, t),rp y,rpcv z)
  | Div ((x,t),y,z)->Div ((rp x, t),rp y,rpcv z)
  | Sll ((x,t),y,z)->Sll ((rp x, t),rp y,rpcv z)
  | Srl ((x,t),y,z)->Srl ((rp x, t),rp y,rpcv z)
  | Sra ((x,t),y,z)->Sra ((rp x, t),rp y,rpcv z)
  | Slw ((x,t),y,z)->Slw ((rp x, t),rp y,rpcv z)
  | Lw ((x,t),y,z)->Lw ((rp x, t),rp y,rpcv z)
  | Sw ((x,t),y,z,w)-> Sw((rp x,t),rp y, rp z, rpcv w)
  | FMov ((x,t),y)-> FMov ((rp x,t), rp y)
  | FNeg ((x,t),y)-> FNeg ((rp x,t), rp y)
  | FInv ((x,t),y)-> FInv ((rp x,t), rp y)
  | FAdd ((x,t),y,z)-> FAdd ((rp x,t),rp y,rp z)
  | FSub ((x,t),y,z)-> FSub ((rp x,t),rp y,rp z)
  | FMul ((x,t),y,z)-> FMul ((rp x,t),rp y,rp z)
  | FDiv ((x,t),y,z)-> FDiv ((rp x,t),rp y,rp z)
  | Lfd ((x,t),y,z)-> Lfd((rp x,t),rp y,rpcv z)
  | Stfd ((x,t),y,z,w)-> Stfd((rp x,t),rp y,rp z,rpcv w)
  | IfEq ((x,t),y,z,w,v)->IfEq((rp x,t),rp y,rpcv z,w,v)
  | IfLE ((x,t),y,z,w,v)->IfLE((rp x,t),rp y,rpcv z,w,v)
  | IfGE ((x,t),y,z,w,v)->IfGE((rp x,t),rp y,rpcv z,w,v) 
  | IfFEq ((x,t),y,z,w,v)->IfFEq((rp x,t),rp y,rp z,w,v)
  | IfFLE ((x,t),y,z,w,v)->IfFLE((rp x,t),rp y,rp z,w,v)
  | CallCls ((x,t),y,z,w)->CallCls((rp x,t),rp y,List.map rp z,List.map rp w)
  | CallDir ((x,t),y,z,w)->CallDir ((rp x,t),y,List.map rp z,List.map rp w)
  | Save ((x,t),y,z)->Save((x,t),rp y,z)
  | Restore ((x,t),y)->Restore((rp x,t),y)

let rec g fundef blk dest = 
  function
  | Asm.Ans exp->
     let newblk = g' fundef blk dest exp in
     add_block newblk fundef;
     newblk
  | Asm.Let ((x,t),exp,y)->
     let nextblk = g' fundef blk (x,t) exp in
     g fundef nextblk dest y

and g' (fundef : fundef) blk xt e = 
  match  e with
  | Asm.Nop-> blk
  | Asm.Li   x   ->add_statement (Li  (xt,x))  blk;blk
  | Asm.FLi  x   ->add_statement (FLi (xt,x))  blk;blk
  | Asm.SetL x   ->add_statement (SetL(xt,x))  blk;blk
  | Asm.Mr   x   ->add_statement (Mr  (xt,x))  blk;blk
  | Asm.Neg  x   ->add_statement (Neg (xt,x))  blk;blk
  | Asm.Add (x,y)->add_statement (Add(xt,x,y)) blk;blk
  | Asm.Sub (x,y)->add_statement (Sub(xt,x,y)) blk;blk
  | Asm.Mul (x,y)->add_statement (Mul(xt,x,y)) blk;blk
  | Asm.Div (x,y)->add_statement (Div(xt,x,y)) blk;blk
  | Asm.Sll (x,y)->add_statement (Sll(xt,x,y)) blk;blk
  | Asm.Srl (x,y)->add_statement (Srl(xt,x,y)) blk;blk
  | Asm.Sra (x,y)->add_statement (Sra(xt,x,y)) blk;blk
  | Asm.Slw (x,y)->add_statement (Slw(xt,x,y)) blk;blk
  | Asm.Lw  (x,y)->add_statement (Lw (xt,x,y)) blk;blk
  | Asm.Sw  (x,y,z)->add_statement (Sw (xt,x,y,z)) blk;blk
  | Asm.FMov x   ->add_statement (FMov(xt,x))  blk;blk
  | Asm.FNeg x   ->add_statement (FNeg(xt,x))  blk;blk
  | Asm.FInv x   ->add_statement (FInv(xt,x))  blk;blk
  | Asm.FAdd(x,y)->add_statement (FAdd(xt,x,y))blk;blk
  | Asm.FSub(x,y)->add_statement (FSub(xt,x,y))blk;blk
  | Asm.FMul(x,y)->add_statement (FMul(xt,x,y))blk;blk
  | Asm.FDiv(x,y)->add_statement (FDiv(xt,x,y))blk;blk
  | Asm.Lfd (x,y)->add_statement (Lfd(xt,x,y))blk;blk
  | Asm.Stfd(x,y,z)->add_statement(Stfd(xt,x,y,z))blk;blk
  | Asm.Comment _->blk
  (* virtual instructions *)
  | Asm.IfEq (x,y,e1,e2)->
     let bt = gen_block_id () in
     let bf = gen_block_id () in
     let bn = gen_block_id () in
     add_statement (IfEq(xt,x,y,bt,bf)) blk;
     add_block blk fundef;
     let b_true  = new_block bt [blk.b_id] [] in
     let bl_true = g fundef b_true xt e1 in
     let b_false = new_block bf [blk.b_id] [] in
     let bl_false= g fundef b_false xt e2 in
     let b_next  = new_block bn [bl_true.b_id;bl_false.b_id] [] in
     b_next
  | Asm.IfLE (x,y,e1,e2)->
     let bt = gen_block_id () in
     let bf = gen_block_id () in
     let bn = gen_block_id () in
     add_statement (IfLE(xt,x,y,bt,bf)) blk;
     add_block blk fundef;
     let b_true  = new_block bt [blk.b_id] [] in
     let bl_true = g fundef b_true xt e1 in
     let b_false = new_block bf [blk.b_id] [] in
     let bl_false= g fundef b_false xt e2 in
     let b_next  = new_block bn [bl_true.b_id;bl_false.b_id] [] in
     b_next
  | Asm.IfGE (x,y,e1,e2)->
     let bt = gen_block_id () in
     let bf = gen_block_id () in
     let bn = gen_block_id () in
     add_statement (IfGE(xt,x,y,bt,bf)) blk;
     add_block blk fundef;
     let b_true  = new_block bt [blk.b_id] [] in
     let bl_true = g fundef b_true xt e1 in
     let b_false = new_block bf [blk.b_id] [] in
     let bl_false= g fundef b_false xt e2 in
     let b_next  = new_block bn [bl_true.b_id;bl_false.b_id] [] in
     b_next
  | Asm.IfFEq (x,y,e1,e2)->
     let bt = gen_block_id () in
     let bf = gen_block_id () in
     let bn = gen_block_id () in
     add_statement (IfFEq(xt,x,y,bt,bf)) blk;
     add_block blk fundef;
     let b_true  = new_block bt [blk.b_id] [] in
     let bl_true = g fundef b_true xt e1 in
     let b_false = new_block bf [blk.b_id] [] in
     let bl_false= g fundef b_false xt e2 in
     let b_next  = new_block bn [bl_true.b_id;bl_false.b_id] [] in
     b_next
  | Asm.IfFLE (x,y,e1,e2)->
     let bt = gen_block_id () in
     let bf = gen_block_id () in
     let bn = gen_block_id () in
     add_statement (IfFLE(xt,x,y,bt,bf)) blk;
     add_block blk fundef;
     let b_true  = new_block bt [blk.b_id] [] in
     let bl_true = g fundef b_true xt e1 in
     let b_false = new_block bf [blk.b_id] [] in
     let bl_false= g fundef b_false xt e2 in
     let b_next  = new_block bn [bl_true.b_id;bl_false.b_id] [] in
     b_next
  (* closure address, integer arguments, and float arguments *)
  | Asm.CallCls _->assert false
  | Asm.CallDir (x,y,z)->add_statement (CallDir(xt,x,y,z)) blk; blk
  | Asm.Save (x,y)->(* レジスタ変数の値をスタック変数へ保存*)
     add_statement (Save(xt,x,y)) blk; blk
  | Asm.Restore x->(* スタック変数から値を復元 *)
     add_statement (Restore(xt,x)) blk; blk

let h {Asm.name = Id.L x; Asm.args = ys; Asm.fargs = zs; Asm.body = e; Asm.ret = t} =
  let block = new_block (gen_block_id ()) [] [] in
  let fundef = {name = Id.L x;
		args = ys; 
		fargs = zs;
		ret = t;
		blocks = M.empty; 
		b_head = block.b_id; 
		use_regs = []} in
  let ret_reg = try (M.find x !Asm.funlist).Asm.retreg with Not_found->"%dummy" in
  (*try*) let _ = g fundef block (ret_reg,t) e in fundef
  (*with |_-> assert false*)

let f (Asm.Prog(fundefs,e)) =
  let fundefs' = List.map h fundefs in
  Prog (fundefs',h {Asm.name = Id.L "_min_caml_main"; Asm.args=[];Asm.fargs=[];Asm.body=e;Asm.ret=Type.Unit})





