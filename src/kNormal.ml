(* give names to intermediate values (K-normalization) *)

let fdiv = ref false
let finv_software = ref false

type t = (* K正規化後の式 (caml2html: knormal_t) *)
  | Unit
  | Int of int
  | Float of float
  | Neg of Id.t
  | Add of Id.t * Id.t
  | Sub of Id.t * Id.t
  | Mul of Id.t * Id.t
  | Div of Id.t * Id.t
  | Lsl of Id.t * Id.t
  | Lsr of Id.t * Id.t
  | Asr of Id.t * Id.t
  | FNeg of Id.t
  | FInv of Id.t
  | FAdd of Id.t * Id.t
  | FSub of Id.t * Id.t
  | FMul of Id.t * Id.t
  | FDiv of Id.t * Id.t
  | IfEq of Id.t * Id.t * t * t (* 比較 + 分岐 (caml2html: knormal_branch) *)
  | IfLE of Id.t * Id.t * t * t (* 比較 + 分岐 *)
  | Let of (Id.t * Type.t) * t * t
  | Var of Id.t
  | LetRec of fundef * t
  | App of Id.t * Id.t list
  | Tuple of Id.t list
  | LetTuple of (Id.t * Type.t) list * Id.t * t
  | Get of Id.t * Id.t
  | Put of Id.t * Id.t * Id.t
  | ExtArray of Id.t
  | ExtFunApp of Id.t * Id.t list
  | ExtTuple of Id.t
and fundef = { name : Id.t * Type.t; args : (Id.t * Type.t) list; body : t }

let rec fv = function (* 式に出現する（自由な）変数 (caml2html: knormal_fv) *)
  | Unit | Int(_) | Float(_) | ExtArray(_) | ExtTuple(_) -> S.empty
  | Neg(x) | FNeg(x) | FInv(x) -> S.singleton x
  | Add(x, y) | Sub(x, y) | Mul(x, y) | Div(x, y)
  | FAdd(x, y)| FSub(x, y)| FMul(x, y)| FDiv(x, y)
  | Lsl(x, y) | Lsr(x, y) | Asr(x, y) | Get(x, y) -> S.of_list [x; y]
  | IfEq(x, y, e1, e2) | IfLE(x, y, e1, e2) -> S.add x (S.add y (S.union (fv e1) (fv e2)))
  | Let((x, t), e1, e2) -> S.union (fv e1) (S.remove x (fv e2))
  | Var(x) -> S.singleton x
  | LetRec({ name = (x, t); args = yts; body = e1 }, e2) ->
      let zs = S.diff (fv e1) (S.of_list (List.map fst yts)) in
      S.diff (S.union zs (fv e2)) (S.singleton x)
  | App(x, ys) -> S.of_list (x :: ys)
  | Tuple(xs) | ExtFunApp(_, xs) -> S.of_list xs
  | Put(x, y, z) -> S.of_list [x; y; z]
  | LetTuple(xs, y, e) -> S.add y (S.diff (fv e) (S.of_list (List.map fst xs)))

let insert_let (e, t) k = (* letを挿入する補助関数 (caml2html: knormal_insert) *)
  match e with
  | Var(x) -> k x
  | _ ->
      let x = Id.gentmp t in
      let e', t' = k x in
      Let((x, t), e, e'), t'

let rec g env = function (* K正規化ルーチン本体 (caml2html: knormal_g) *)
  | Syntax.Unit -> Unit, Type.Unit
  | Syntax.Bool(b,l) -> Int(if b then 1 else 0), Type.Int l (* 論理値true, falseを整数1, 0に変換 (caml2html: knormal_bool) *)
  | Syntax.Int(i,l) -> Int(i), Type.Int l
  | Syntax.Float(d,l) -> Float(d), Type.Float l
  | Syntax.Not(e,l) -> g env (Syntax.If(e, Syntax.Bool(false,l), Syntax.Bool(true,l),l))
  | Syntax.Neg(e,l) ->
      insert_let (g env e)
	(fun x -> Neg(x), Type.Int l)
  | Syntax.Add(e1, e2,l) -> (* 足し算のK正規化 (caml2html: knormal_add) *)
     let (e,t) = g env e1 in 
     insert_let (e,t)
	(fun x -> insert_let (g env e2)
	    (fun y -> match t with
		      |Type.Int _  -> Add(x, y), Type.Int   l
		      |Type.Float _->FAdd(x, y), Type.Float l))
  | Syntax.Sub(e1, e2,l) ->
      insert_let (g env e1)
	(fun x -> insert_let (g env e2)
	    (fun y -> Sub(x, y), Type.Int l))
  | Syntax.Mul(e1, e2,l) -> (* 足し算のK正規化 (caml2html: knormal_add) *)
      insert_let (g env e1)
	(fun x -> insert_let (g env e2)
	    (fun y -> Mul(x, y), Type.Int l))
  | Syntax.Div(e1, e2,l) ->
      insert_let (g env e1)
	(fun x -> insert_let (g env e2)
	    (fun y -> Div(x, y), Type.Int l))
  | Syntax.Lsl(e1, e2,l) -> (* シフトのK正規化 (caml2html: knormal_add) *)
      insert_let (g env e1)
	(fun x -> insert_let (g env e2)
	    (fun y -> Lsl(x, y), Type.Int l))
  | Syntax.Lsr(e1, e2,l) ->
      insert_let (g env e1)
	(fun x -> insert_let (g env e2)
	    (fun y -> Lsr(x, y), Type.Int l))
  | Syntax.Asr(e1, e2,l) ->
      insert_let (g env e1)
	(fun x -> insert_let (g env e2)
	    (fun y -> Asr(x, y), Type.Int l))
  | Syntax.FNeg(e,l) ->
      insert_let (g env e)
	(fun x -> FNeg(x), Type.Float l)
  | Syntax.FInv(e,l) ->
     if !finv_software then
       insert_let (g env e)
	(fun x -> ExtFunApp("finv",[x]),
		  Type.Fun([Type.Float l],Type.Float l,l))
     else
      insert_let (g env e)
	(fun x -> FInv(x), Type.Float l)
  | Syntax.FAdd(e1, e2,l) ->
      insert_let (g env e1)
	(fun x -> insert_let (g env e2)
	    (fun y -> FAdd(x, y), Type.Float l))
  | Syntax.FSub(e1, e2,l) ->
      insert_let (g env e1)
	(fun x -> insert_let (g env e2)
	    (fun y -> FSub(x, y), Type.Float l))
  | Syntax.FMul(e1, e2,l) ->
      insert_let (g env e1)
	(fun x -> insert_let (g env e2)
	    (fun y -> FMul(x, y), Type.Float l))
  | Syntax.FDiv(e1, e2,l) ->
       if !fdiv then
	 insert_let (g env e1)
		    (fun x -> insert_let (g env e2)
		     (fun y -> FDiv(x, y), Type.Float l))
       else if !finv_software then
       	 insert_let (g env e1)
	 (fun x -> insert_let
	   (g env (Syntax.App(Syntax.Var("finv",l),[e2],l)))
	   (fun y -> FMul(x, y), Type.Float l))
       else
       	 insert_let (g env e1)
	   (fun x -> insert_let (g env (Syntax.FInv(e2,l)))
	   (fun y -> FMul(x, y), Type.Float l))
  | Syntax.Eq(_,_,l) | Syntax.LE(_,_,l) as cmp ->
      g env (Syntax.If(cmp, Syntax.Bool(true,l), Syntax.Bool(false,l),l))
  | Syntax.If(Syntax.Not(e1,l1), e2, e3,l2) -> g env (Syntax.If(e1, e3, e2,l2)) (* notによる分岐を変換 (caml2html: knormal_not) *)
  | Syntax.If(Syntax.Eq(e1, e2,l1), e3, e4,l2) ->
      insert_let (g env e1)
	(fun x -> insert_let (g env e2)
	    (fun y ->
	      let e3', t3 = g env e3 in
	      let e4', t4 = g env e4 in
	      IfEq(x, y, e3', e4'), t3))
  | Syntax.If(Syntax.LE(e1, e2,l1), e3, e4,l2) ->
      insert_let (g env e1)
	(fun x -> insert_let (g env e2)
	    (fun y ->
	      let e3', t3 = g env e3 in
	      let e4', t4 = g env e4 in
	      IfLE(x, y, e3', e4'), t3))
  | Syntax.If(e1, e2, e3,l) -> g env (Syntax.If(Syntax.Eq(e1, Syntax.Bool(false,l),l), e3, e2,l))(* 比較のない分岐を変換(caml2html: knormal_if)*)
  | Syntax.Let((x, t), e1, e2,l) ->
      let e1', t1 = g env e1 in
      let e2', t2 = g (M.add x t env) e2 in
      Let((x, t), e1', e2'), t2
  | Syntax.Var(x,l) when M.mem x env -> Var(x), M.find x env
  | Syntax.Var(x,l) -> (* 外部配列の参照 (caml2html: knormal_extarray) *)
      (match M.find x !Typing.extenv with
      | Type.Array(_) as t -> ExtArray x, t
      | Type.Tuple(_) as t -> ExtTuple x, t
      | _ -> failwith (Printf.sprintf "line %d:external variable %s does not have an array type" l x))
  | Syntax.LetRec({ Syntax.name = (x, t); Syntax.args = yts; Syntax.body = e1 }, e2,l) ->
      let env' = M.add x t env in
      let e2', t2 = g env' e2 in
      let e1', t1 = g (M.add_list yts env') e1 in
      LetRec({ name = (x, t); args = yts; body = e1' }, e2'), t2
  | Syntax.App(Syntax.Var(f,l1), e2s,l2) when not (M.mem f env) -> (* 外部関数の呼び出し (caml2html: knormal_extfunapp) *)
      (match M.find f !Typing.extenv with
      | Type.Fun(_, t,l) ->
	  let rec bind xs = function (* "xs" are identifiers for the arguments *)
	    | [] -> ExtFunApp(f, xs), t
	    | e2 :: e2s ->
		insert_let (g env e2)
		  (fun x -> bind (xs @ [x]) e2s) in
	  bind [] e2s (* left-to-right evaluation *)
      | _ -> assert false)
  | Syntax.App(e1, e2s,l) ->
      (match g env e1 with
      | _, Type.Fun(_, t,l) as g_e1 ->
	  insert_let g_e1
	    (fun f ->
	      let rec bind xs = function (* "xs" are identifiers for the arguments *)
		| [] -> App(f, xs), t
		| e2 :: e2s ->
		    insert_let (g env e2)
		      (fun x -> bind (xs @ [x]) e2s) in
	      bind [] e2s) (* left-to-right evaluation *)
      | _ -> assert false)
  | Syntax.Tuple(es,l) ->
      let rec bind xs ts = function (* "xs" and "ts" are identifiers and types for the elements *)
	| [] -> Tuple(xs), Type.Tuple(ts,l)
	| e :: es ->
	    let _, t as g_e = g env e in
	    insert_let g_e
	      (fun x -> bind (xs @ [x]) (ts @ [t]) es) in
      bind [] [] es
  | Syntax.LetTuple(xts, e1, e2,l) ->
      insert_let (g env e1)
	(fun y ->
	  let e2', t2 = g (M.add_list xts env) e2 in
	  LetTuple(xts, y, e2'), t2)
  | Syntax.Array(e1, e2,l1) ->
      insert_let (g env e1)
	(fun x ->
	  let _, t2 as g_e2 = g env e2 in
	  insert_let g_e2
		     (fun y ->
		      let l =
			match t2 with
			| Type.Float _-> "create_float_array"
			| _ -> "create_array" in
		      ExtFunApp(l, [x; y]), Type.Array(t2,l1)))
  | Syntax.Get(e1, e2, l1) ->
      (match g env e1 with
      |	_, Type.Array(t,l) as g_e1 ->
	  insert_let g_e1
	    (fun x -> insert_let (g env e2)
		(fun y -> Get(x, y), t))
      | _ -> assert false)
  | Syntax.Put(e1, e2, e3, l1) ->
      insert_let (g env e1)
	(fun x -> insert_let (g env e2)
	    (fun y -> insert_let (g env e3)
		(fun z -> Put(x, y, z), Type.Unit)))

let f e fd finv =fdiv:=fd;finv_software:=finv; fst (g M.empty e)

let rec p_t fmt= function
  | Unit -> Format.fprintf fmt "()"
  | Int i -> Format.fprintf fmt "%d" i
  | Float f -> Format.fprintf fmt "%f" f
  | Neg x    ->Format.fprintf fmt "-(%a)" Id.pp x
  | Add (x,y)->Format.fprintf fmt "%a + %a" Id.pp x Id.pp y
  | Sub (x,y)->Format.fprintf fmt "%a - %a" Id.pp x Id.pp y
  | Mul (x,y)->Format.fprintf fmt "%a * %a" Id.pp x Id.pp y
  | Div (x,y)->Format.fprintf fmt "%a / %a" Id.pp x Id.pp y
  | Lsl (x,y)->Format.fprintf fmt "%a lsl %a" Id.pp x Id.pp y
  | Lsr (x,y)->Format.fprintf fmt "%a lsr %a" Id.pp x Id.pp y
  | Asr (x,y)->Format.fprintf fmt "%a asr %a" Id.pp x Id.pp y
  | FNeg x    ->Format.fprintf fmt "-.(%a)" Id.pp x
  | FInv x    ->Format.fprintf fmt "1.0/.(%a)" Id.pp x
  | FAdd (x,y)->Format.fprintf fmt "%a +. %a" Id.pp x Id.pp y
  | FSub (x,y)->Format.fprintf fmt "%a -. %a" Id.pp x Id.pp y
  | FMul (x,y)->Format.fprintf fmt "%a *. %a" Id.pp x Id.pp y
  | FDiv (x,y)->Format.fprintf fmt "%a /. %a" Id.pp x Id.pp y
  | IfEq (x,y,z,w)->
     Format.fprintf fmt "if %a = %a @.then %a@.else %a" 
		    Id.pp x Id.pp y p_t z p_t w
  | IfLE (x,y,z,w)->
     Format.fprintf fmt "if %a <= %a @.then %a@.else %a" 
		    Id.pp x Id.pp y p_t z p_t w
  | Let ((x,y),z,w)->
     Format.fprintf fmt "let %a:%a\t= %a\tin@.%a" 
		    Id.pp x Type.pp y p_t z p_t w
  | Var x ->Format.fprintf fmt "%a" Id.pp x
  | LetRec (x,y)->
     Format.fprintf fmt "let rec %a\tin@.%a@." p_f x p_t y
  | LetTuple(x,y,z)->
     Format.fprintf fmt "let (%a)\t= %a\tin@.%a"
		(p_tlit ",") x Id.pp y p_t z
  | App (x,y)->
     Format.fprintf fmt "%a %a" Id.pp x (p_tli " ") y
  | Tuple x->
     Format.fprintf fmt "(%a)" (p_tli ",") x
  | Get (x,y)->Format.fprintf fmt "%a.(%a)" Id.pp x Id.pp y
  | Put(x,y,z)->
     Format.fprintf fmt "%a.(%a)<-%a" Id.pp x Id.pp y Id.pp z
  | ExtArray x->
     Format.fprintf fmt "%a" Id.pp x
  | ExtFunApp(x,y)->
      Format.fprintf fmt "%a %a" Id.pp x (p_tli " ") y
  | ExtTuple x->
     Format.fprintf fmt "%a" Id.pp x

and p_f fmt { name = (x,y) ; args = z; body = w } =
  Format.fprintf fmt "(%a %a):%a\t=@.%a"
		 Id.pp x (p_tlit " ") z Type.pp y p_t w

and p_tli c fmt = function
  |[]->()
  |[x]->Format.fprintf fmt "%a" Id.pp x
  |x::xs->Format.fprintf fmt "%a%s" Id.pp x c;p_tli c fmt xs

and p_tlit c fmt = function
  |[]->()
  |[(x,y)]->Format.fprintf fmt "%a:%a" Id.pp x Type.pp y
  |(x,y)::xs->Format.fprintf fmt "%a:%a%s" Id.pp x Type.pp y c;
	  p_tlit c fmt xs
and p_tlt fmt = function
  |[]->()
  |[x]->Format.fprintf fmt "%a" p_t x
  |x::xs->Format.fprintf fmt "%a;" p_t x ;p_tlt fmt xs
 
and p_it fmt (x,y) = Format.fprintf fmt "%a:%a" Id.pp x Type.pp y

let p x = Format.fprintf Format.err_formatter "@.%a@.@." p_t x
