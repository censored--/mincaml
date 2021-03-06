open KNormal

let memi x env =
  try (match M.find x env with Int(_) -> true | _ -> false)
  with Not_found -> false
let memf x env =
  try (match M.find x env with Float(_) -> true | _ -> false)
  with Not_found -> false
let memt x env =
  try (match M.find x env with Tuple(_) -> true | _ -> false)
  with Not_found -> false

let findi x env = (match M.find x env with Int(i) -> i | _ -> raise Not_found)
let findf x env = (match M.find x env with Float(d) -> d | _ -> raise Not_found)
let findt x env = (match M.find x env with Tuple(ys) -> ys | _ -> raise Not_found)

let rec no_subeffect = function
  |Put _| LetRec _| App _ | LetTuple _ | ExtFunApp _->false
  | IfEq (_,_,x,y)->no_subeffect x&&no_subeffect y
  | IfLE (_,_,x,y)->no_subeffect x&&no_subeffect y
  | Let (_,x,y)->no_subeffect x&&no_subeffect y
  | _->true

let rec tail = function
  | Let (_,_,x)->tail x
  | e -> e

let rec g env fs = function (* 定数畳み込みルーチン本体 (caml2html: constfold_g) *)
  | Var(x) when memi x env -> Int(findi x env)
  | Var(x) when memf x env -> Float(findf x env)
  (* | Var(x) when memt x env -> Tuple(findt x env) *)
  | Neg(x) when memi x env -> Int(-(findi x env))
  | Add(x, y) when memi x env && memi y env -> Int(findi x env + findi y env) (* 足し算のケース (caml2html: constfold_add) *)
  | Add(x, y) when memi x env ->  if findi x env = 0 then Var(y) else Add(x,y)
  | Add(x, y) when memi y env ->  if findi y env = 0 then Var(x) else Add(x,y)
  | Sub(x, y) when memi x env && memi y env -> Int(findi x env - findi y env)
  | Sub(x, y) when memi x env ->  if findi x env = 0 then Neg(y) else Sub(x,y)
  | Sub(x, y) when memi y env ->  if findi y env = 0 then Var(x) else Sub(x,y)
  | Mul(x, y) when memi x env && memi y env -> Int(findi x env * findi y env) (* かけ算のケース (caml2html: constfold_add) *)
  | Div(x, y) when memi x env && memi y env -> Int(findi x env / findi y env)
  | Lsl(x, y) when memi x env && memi y env -> Int(findi x env lsl findi y env)
  | Lsr(x, y) when memi x env && memi y env -> Int(findi x env lsr findi y env)
  | Asr(x, y) when memi x env && memi y env -> Int(findi x env asr findi y env)
  | FNeg(x) when memf x env -> Float(-.(findf x env))
  | FInv(x) when memf x env -> Float(1.0/.(findf x env))
  | FAdd(x, y) when memf x env && memf y env -> Float(findf x env +. findf y env)
  | FAdd(x, y) when memf x env ->if findf x env = 0.0 then Var(y) else FAdd(x,y) 
  | FAdd(x, y) when memf y env ->if findf y env = 0.0 then Var(x) else FAdd(x,y) 
  | FSub(x, y) when memf x env && memf y env -> Float(findf x env -. findf y env)
  | FSub(x, y) when memf x env ->if findf x env = 0.0 then FNeg(y) else FSub(x,y) 
  | FSub(x, y) when memf y env ->if findf y env = 0.0 then Var(x) else FSub(x,y) 
  | FMul(x, y) when memf x env && memf y env -> Float(findf x env *. findf y env)
  | FDiv(x, y) when memf x env && memf y env -> Float(findf x env /. findf y env)
  | IfEq(x, y, e1, e2) when memi x env && memi y env -> if findi x env = findi y env then g env fs e1 else g env fs e2
  | IfEq(x, y, e1, e2) when memf x env && memf y env -> if findf x env = findf y env then g env fs e1 else g env fs e2
  | IfEq(x, y, e1, e2) -> IfEq(x, y, g env fs e1, g env fs e2)
  | IfLE(x, y, e1, e2) when memi x env && memi y env -> if findi x env <= findi y env then g env fs e1 else g env fs e2
  | IfLE(x, y, e1, e2) when memf x env && memf y env -> if findf x env <= findf y env then g env fs e1 else g env fs e2
  | IfLE(x, y, e1, e2) -> IfLE(x, y, g env fs e1, g env fs e2)
  | Let((x, t), e1, e2) -> (* letのケース (caml2html: constfold_let) *)
     let e1' = g env fs e1 in
     let e2' = g (M.add x e1' env) fs e2 in
     Let((x, t), e1', e2')
  | LetRec({ name = (x,t); args = ys; body = e1 }, e2) ->
     LetRec({ name = (x,t); args = ys; body = g env fs e1 }, g env ((x,ys,g env fs e1)::fs) e2)
  | LetTuple(xts, y, e) when memt y env ->
     List.fold_left2
       (fun e' xt z -> Let(xt, Var(z), e'))
       (g env fs e)
       xts
       (findt y env)
  | LetTuple(xts, y, e) -> LetTuple(xts, y, g env fs e)
  | App (x,y) when List.for_all (fun x->memi x env) y->
     (try
	 let y' = List.map (fun y -> g env fs (Var y)) y in
	 Log.print  "calculate %a [%a]@."Id.pp x p_tlt y';
	 let (name,args,e) = List.find (fun (y,_,_)->x = y) fs in
	 let argsl = List.map (fun (x,_)->x) args in
	 let env' = M.add_list2 argsl y' env in
	 let e' = if no_subeffect e then tail (g env' fs e) else e in
	 (match e' with
	  |Int _ |Float _ | Unit -> e'
	  |_->raise Not_found)
       with
       |_->App (x,y))
  | e -> e


let f = g M.empty []
