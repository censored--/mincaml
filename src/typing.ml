(* type inference/reconstruction *)

open Syntax

exception Unify of Type.t * Type.t
exception Error of int * int * unit * Type.t * Type.t

let extenv = ref M.empty

let rec modify_type ts t = match t with
  |Type.Fun(t1,t2,_)->modify_type (ts@t1) t2
  |Type.Var({contents = Some tp},l)->modify_type ts tp
  |e -> (ts,e)

let rec typ t = match t with
  |Type.Fun(t1,t2,l)->let (t1,t2) = modify_type t1 t2 in
		      Type.Fun(List.map typ t1,t2,l)
  |Type.Var({contents=Some t1},l)->typ t1
  |e -> e

(* for pretty printing (and type normalization) *)
let rec deref_typ = function (* 型変数を中身でおきかえる関数 (caml2html: typing_deref) *)
  | Type.Fun(t1s, t2,l) -> Type.Fun(List.map deref_typ t1s, deref_typ t2,l)
  | Type.Tuple(ts,l) -> Type.Tuple(List.map deref_typ ts,l)
  | Type.Array(t,l) -> Type.Array(deref_typ t,l)
  | Type.Var({ contents = None } as r,l) ->
      Format.eprintf "uninstantiated type variable detected; assuming int@.";
      r := Some(Type.Int l);
      Type.Int l
  | Type.Var({ contents = Some(t) } as r,l) ->
      let t' = deref_typ t in
      r := Some(t');
      t'
  | t -> t
let rec deref_id_typ (x, t) = (x, deref_typ t)
let rec deref_term = function
  | Not(e,l) -> Not(deref_term e,l)
  | Neg(e,l) -> Neg(deref_term e,l)
  | Add(e1, e2, l) -> Add(deref_term e1, deref_term e2, l)
  | Sub(e1, e2, l) -> Sub(deref_term e1, deref_term e2, l)
  | Mul(e1, e2, l) -> Mul(deref_term e1, deref_term e2, l)
  | Div(e1, e2, l) -> Div(deref_term e1, deref_term e2, l)
  | Lsl(e1, e2, l) -> Lsl(deref_term e1, deref_term e2, l)
  | Lsr(e1, e2, l) -> Lsr(deref_term e1, deref_term e2, l)
  | Asr(e1, e2, l) -> Asr(deref_term e1, deref_term e2, l)
  | Eq(e1, e2, l) -> Eq(deref_term e1, deref_term e2, l)
  | LE(e1, e2, l) -> LE(deref_term e1, deref_term e2, l)
  | FNeg(e, l) -> FNeg(deref_term e, l)
  | FInv(e, l) -> FInv(deref_term e, l)
  | FAdd(e1, e2, l) -> FAdd(deref_term e1, deref_term e2, l)
  | FSub(e1, e2, l) -> FSub(deref_term e1, deref_term e2, l)
  | FMul(e1, e2, l) -> FMul(deref_term e1, deref_term e2, l)
  | FDiv(e1, e2, l) -> FDiv(deref_term e1, deref_term e2, l)
  | If(e1, e2, e3, l) -> If(deref_term e1, deref_term e2, deref_term e3,l)
  | Let(xt, e1, e2, l) -> Let(deref_id_typ xt, deref_term e1, deref_term e2,l)
  | LetRec({ name = xt; args = yts; body = e1 }, e2,l) ->
      LetRec({ name = deref_id_typ xt;
	       args = List.map deref_id_typ yts;
	       body = deref_term e1 },
	     deref_term e2,l)
  | App(e, es,l) -> App(deref_term e, List.map deref_term es,l)
  | Tuple(es,l) -> Tuple(List.map deref_term es,l)
  | LetTuple(xts, e1, e2,l) -> LetTuple(List.map deref_id_typ xts, deref_term e1, deref_term e2,l)
  | Array(e1, e2,l) -> Array(deref_term e1, deref_term e2,l)
  | Get(e1, e2,l) -> Get(deref_term e1, deref_term e2,l)
  | Put(e1, e2, e3,l) -> Put(deref_term e1, deref_term e2, deref_term e3,l)
  | e -> e

let rec occur r1 = function (* occur check (caml2html: typing_occur) *)
  | Type.Fun(t2s, t2,l) -> List.exists (occur r1) t2s || occur r1 t2
  | Type.Tuple(t2s,l) -> List.exists (occur r1) t2s
  | Type.Array(t2,l) -> occur r1 t2
  | Type.Var(r2,l) when r1 == r2 -> true
  | Type.Var({ contents = None },l) -> false
  | Type.Var({ contents = Some(t2) },l) -> occur r1 t2
  | _ -> false

let rec unify t1 t2 = (* 型が合うように、型変数への代入をする (caml2html: typing_unify) *)
  match t1, t2 with
  | Type.Unit, Type.Unit | Type.Bool _, Type.Bool _| Type.Int _, Type.Int _ | Type.Float _, Type.Float _ -> ()
  | Type.Fun(t1s, t1',l1), Type.Fun(t2s, t2',l2) ->
     (try
	 let (t1s,t1'),(t2s,t2') = 
	   modify_type t1s t1',modify_type t2s t2' in
	 let (t1s,t2s) = rest t1s t2s in
	 (match t1s,t2s with
	  |[],[]->unify t1' t2'
	  |_,[]->unify (Type.Fun(t1s,t1',l1)) t2'
	  |_,_->unify t1' (Type.Fun(t2s,t2',l2)))
       with 
       |_->raise (Unify(t1,t2)))
  | Type.Tuple(t1s,_), Type.Tuple(t2s,_) ->
     (try List.iter2 unify t1s t2s
      with Invalid_argument("List.iter2") -> raise (Unify(t1, t2)))
  | Type.Array(t1,_), Type.Array(t2,_) -> unify t1 t2
  | Type.Var(r1,_), Type.Var(r2,_) when r1 == r2 -> ()
  | Type.Var({ contents = Some(t1') },_), _ -> unify t1' t2
  | _, Type.Var({ contents = Some(t2') },_) -> unify t1 t2'
  | Type.Var({ contents = None } as r1,l), _ -> (* 一方が未定義の型変数の場合 (caml2html: typing_undef) *)
     if occur r1 t2 then raise (Unify(t1, t2));
     r1 := Some(t2)
  | _, Type.Var({ contents = None } as r2,l2) ->
     if occur r2 t1 then raise (Unify(t1, t2));
     r2 := Some(t1)
  | _, _ -> raise (Unify(t1, t2))

and rest x y = match x, y with
  |xt::xs,yt::ys->
    unify xt yt;rest xs ys
  |x,[]->(x,[])
  |[],y-> ([],y)


let funid = ref 0
let genid e =funid:=!funid+1; "_eta_"^e^string_of_int !funid

let rec g env e = (* 型推論ルーチン (caml2html: typing_g) *)
  try
    match e with
    | Unit -> Type.Unit
    | Bool(_,l) -> Type.Bool l
    | Int (_,l) -> Type.Int l
    | Float(_,l) -> Type.Float l
    | Not(e,l) ->
       unify (Type.Bool l) (g env e);
       Type.Bool l
    | Neg(e,l) ->
       unify (Type.Int l) (g env e);
       Type.Int l
    | Add(e1, e2,l) ->
       let t = Type.gentyp l in
       unify t (g env e1);
       unify t (g env e2);
       (match t with
       |Type.Var ({contents = Some (Type.Int _)},_)->Type.Int l
       |Type.Var ({contents = Some (Type.Float _)},_)->Type.Float l
       |Type.Float _->Type.Float l
       |_-> 
	 (unify (Type.Int l) (g env e1);
	  unify (Type.Int l) (g env e2);
	  Type.Int l))
    | Sub(e1, e2,l) 
    | Mul(e1, e2,l) | Div(e1, e2,l)
    | Lsl(e1, e2,l) | Lsr(e1, e2,l) | Asr(e1, e2,l)->
    (* 足し算（と引き算）の型推論 (caml2html: typing_add) *)
		       unify (Type.Int l) (g env e1);
		       unify (Type.Int l) (g env e2);
		       Type.Int l
    | FNeg(e,l) | FInv(e,l) ->
       unify (Type.Float l) (g env e);
       Type.Float l
    | FAdd(e1, e2,l) | FSub(e1, e2,l) | FMul(e1, e2,l) | FDiv(e1, e2,l) ->
							  unify (Type.Float l) (g env e1);
							  unify (Type.Float l) (g env e2);
							  Type.Float l
    | Eq(e1, e2,l) | LE(e1, e2,l) ->
		      unify (g env e1) (g env e2);
		      Type.Bool l
    | If(e1, e2, e3,l) ->
       unify (g env e1) (Type.Bool l);
       let t2 = g env e2 in
       let t3 = g env e3 in
       unify t2 t3;
       t2
    | Let((x, t), e1, e2,l) -> (* letの型推論 (caml2html: typing_let) *)
       unify t (g env e1);
       g (M.add x t env) e2
    | Var(x,l) when M.mem x env -> M.find x env (* 変数の型推論 (caml2html: typing_var) *)
    | Var(x,l) when M.mem x !extenv -> M.find x !extenv
    | Var(x,l) -> (* 外部変数の型推論 (caml2html: typing_extvar) *)
       Log.print "free variable %s assumed as external@." x;
       let t = Type.gentyp l in
       extenv := M.add x t !extenv;
       t
    | LetRec({ name = (x, t); args = yts; body = e1 }, e2,l) -> (* let recの型推論 (caml2html: typing_letrec) *)
       let env = M.add x (typ t) env in
       unify t (Type.Fun(List.map snd yts, g (M.add_list yts env) e1,l));
       g env e2
    | App(e, es,l) -> (* 関数適用の型推論 (caml2html: typing_app) *)
       let t = Type.gentyp l in
	 unify (g env e) (Type.Fun(List.map (g env) es, t,l));
	 t	 
    | Tuple(es,l) -> Type.Tuple(List.map (g env) es,l)
    | LetTuple(xts, e1, e2,l) ->
       unify (Type.Tuple(List.map snd xts,l)) (g env e1);
       g (M.add_list xts env) e2
    | Array(e1, e2,l) -> (* must be a primitive for "polymorphic" typing *)
       unify (g env e1) (Type.Int l);
       Type.Array(g env e2,l)
    | Get(e1, e2,l) ->
       let t = Type.gentyp l in
       unify (Type.Array(t,l)) (g env e1);
       unify (Type.Int l) (g env e2);
       t
    | Put(e1, e2, e3,l) ->
       let t = g env e3 in
       unify (Type.Array(t,l)) (g env e1);
       unify (Type.Int l) (g env e2);
       Type.Unit
  with Unify(t1,t2) ->
    let e'=deref_term e in
    let t1'=deref_typ t1 in
    let t2'=deref_typ t2 in
    raise  (Error(Type.line t1',Type.line t2',Format.eprintf "type error\nnear:\n%a\nline:%d-%d\n%a is not %a\n" Syntax.pp_t e' (Type.line t1') (Type.line t2') Type.pp t1' Type.pp t2',t1',t2'))

let rec rest x y = match x,y with
  |xt::xs,yt::ys->rest xs ys
  |[],_->y
  |_,[]->[]

let rec eta env = function
  | Not (x,l)->Not(eta env x,l)
  | Neg (x,l)->Neg(eta env x,l)
  | Add (x,y,l)->Add(eta env x,eta env y,l)
  | Sub (x,y,l)->Sub(eta env x,eta env y,l)
  | Mul (x,y,l)->Mul(eta env x,eta env y,l)
  | Div (x,y,l)->Div(eta env x,eta env y,l)
  | Lsl (x,y,l)->Lsl(eta env x,eta env y,l)
  | Lsr (x,y,l)->Lsr(eta env x,eta env y,l)
  | Asr (x,y,l)->Asr(eta env x,eta env y,l)
  | FNeg (x,l)->FNeg(eta env x,l)
  | FAdd (x,y,l)->FAdd(eta env x,eta env y,l)
  | FSub (x,y,l)->FSub(eta env x,eta env y,l)
  | FMul (x,y,l)->FMul(eta env x,eta env y,l)
  | FDiv (x,y,l)->FDiv(eta env x,eta env y,l)
  | FInv (x,l)->FInv(eta env x,l)
  | Eq (x,y,l)->Eq(eta env x,eta env y,l)
  | LE (x,y,l)->LE(eta env x,eta env y,l)
  | If (x,y,z,l)->let x' = eta env x in
		  let envf = ref (!env) in
		  If(x',eta env y,eta envf z,l)
  | Let (x,y,z,l)->Let(x,eta env y,eta env z,l)
  | LetRec({name=(x,t);args=y;body=z},w,l)->
     env := ((x,t),y)::(!env);
     LetRec({name=(x,typ t);args=y;body=eta env z},eta env w,l)
  | App(App(e,x,l1),y,l2)->
     eta env (App(e,x@y,l1))
  | App(x,y,l)->
     (match x with
      |Var(e,_)->
	(try
	    let (_,y') = List.find (fun ((n,t),a)-> n = e) !env in
	    let id = genid e in
	    let res = rest y y' in
	    let bod = App(x,y@List.map (fun x->Var(fst x,l)) res,l)in
	    if res = [] then
	      Let((id,Type.gentyp l),bod,Var(id,l),l)
	    else
	      LetRec({name=(id,Type.gentyp l);
		      args=res; body=bod},Var(id,l),l)
	  with
	  |_->App(eta env x,List.map (eta env) y,l))
      |_->App(eta env x,List.map (eta env) y,l))
  | Tuple(x,l)->Tuple(List.map (eta env) x,l)
  | LetTuple (x,y,z,l)->LetTuple(x,eta env y,eta env z,l)
  | Array (x,y,l)->Array(eta env x,eta env y,l)
  | Get (x,y,l)->Get(eta env x,eta env y,l)
  | Put (x,y,z,l)->Put(eta env x,eta env y,eta env z,l)
  | e -> e

let f e =
  extenv := M.empty;
(*
  (match deref_typ (g M.empty e) with
  | Type.Unit -> ()
  | _ -> Format.eprintf "warning: final result does not have type unit@.");
*)
  (*let env = ref [] in
  let e = eta env e in
  p e;*)
  (try unify Type.Unit (g M.empty e)
  with Unify _ -> Format.eprintf "top level does not have type unit"
  (*failwith "top level does not have type unit")*));
  extenv := M.map deref_typ !extenv;
  extenv := M.add "finv" (Type.Fun([Type.Float 0],Type.Float 0,0)) !extenv;
  (*env:= [];
  deref_term (eta env e)*)
  deref_term e

let p e = Format.fprintf Format.err_formatter "Typing:@.%a@." Syntax.pp_t e
