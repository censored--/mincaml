open Closure

let fundata = ref M.empty

exception Unify of Closure.t * Type.t

let find_or_make x env = if x = "min_caml_create_array" then Type.gentyp 0 else try  M.find x env with _-> Type.gentyp 0

(*Closure.tではBool型の変数が存在しないため、Int型として扱う*)
let rec b_to_i t = match t with
  |Type.Bool x->Type.Int x
  |Type.Fun(x,y,z)->Type.Fun(List.map b_to_i x,b_to_i y,z)
  |Type.Tuple(x,y)->Type.Tuple(List.map b_to_i x,y)
  |Type.Array(x,y)->Type.Array(b_to_i x,y)
  |t -> t

(*デバッグ用*)
let print_env env =
  let env = M.bindings env in
  let rec p_e x = match x with
    |(a,b)::xs->Format.eprintf "val %s : %a@." a Type.pp b; p_e xs
    |[]->() in
  p_e env


(*型検査を行い、型環境を返す関数*)
let rec g env t x =
  try
    match x with
    | Unit ->
       Typing.unify t Type.Unit; env
    | Int _-> 
       Typing.unify t (Type.Int 0);env
    | Float _->
       Typing.unify t (Type.Float 0); env
    | Neg x->
       (let tx = M.find x env in
	Typing.unify t tx; env)
    | Add (x,y) | Sub (x,y) | Mul (x,y) | Div (x,y) | Lsl (x,y) | Lsr (x,y)
    | Asr (x,y)->
       (let tx,ty = M.find x env,M.find y env in
	Typing.unify (Type.Int 0) tx;
	Typing.unify (Type.Int 0) ty;
	Typing.unify (Type.Int 0) t; env)
    | FNeg x 
    | FInv x->
       (let tx = M.find x env in
	Typing.unify (Type.Float 0) tx; env)
    | FAdd (x,y) | FSub (x,y) | FMul (x,y) 
    | FDiv (x,y)->
       (let tx,ty = M.find x env,M.find y env in
	Typing.unify (Type.Float 0) tx;
	Typing.unify (Type.Float 0) ty;
	Typing.unify (Type.Float 0) t; env)
    | IfEq (x,y,z,w)
    | IfLE (x,y,z,w)->
       (let tx = M.find x env in
	let env = g env tx (Var y) in
	let env = g env t z in
	let env = g env t w in env)
    | Let ((x,tx),y,z)->
       let tx' = b_to_i tx in
       let env = M.add x tx' env in
       let env = g env tx' y in
       g env t z
    | Var x->
       (let tx = M.find x env in
	Typing.unify t tx; env)
    | MakeCls ((x,tx),y,z)->
       let env = M.add x (b_to_i tx) env in
       let env = List.fold_left (fun env x -> 
			 if not (M.mem x env) 
			 then  M.add x (Type.gentyp 0) env 
			 else env) env y.actual_fv in
       g env t z
    | AppCls (x,y)->
       (let tx = find_or_make x env in
	let ty = List.map (fun z ->find_or_make z env) y in
	Typing.unify tx (Type.Fun(ty,t,0));
	let tx = Typing.deref_typ tx in
	let ty = List.map Typing.deref_typ ty in
	let env = M.add x (b_to_i tx) env in
	M.add_list2 y ty env)
    | AppDir (Id.L x,y)->
       (let tx = find_or_make x env in
	let ty = List.map (fun z ->find_or_make z env) y in
	Typing.unify tx (Type.Fun(ty,t,0));
	let tx = Typing.deref_typ tx in
	M.add x tx env)
    | Tuple x->
       (let tx = List.map (fun z-> find_or_make z env) x in
	Typing.unify t (Type.Tuple(tx,0));
	M.add_list2 x tx env)
    | LetTuple (x,y,z)->
       (let x = List.map (fun (x,y)->(x,b_to_i y)) x in
	let tx = List.map (fun x -> b_to_i (snd x)) x in
	let ty = find_or_make y env in
	Typing.unify (Type.Tuple(tx,0)) ty;
	let env = M.add_list x env in
	let env = M.add y ty env in
	g env t z)
    | Get (x,y)->
       (let tx,ty = find_or_make x env,find_or_make y env in
	Typing.unify (Type.Array(t,0)) tx;
	Typing.unify (Type.Int 0) ty;
	M.add_list2 [x;y] [tx;ty] env)
    | Put (x,y,z)->
       (let tx,ty,tz = find_or_make x env,find_or_make y env,find_or_make z env in
	Typing.unify tx (Type.Array(tz,0));
	Typing.unify ty (Type.Int 0);
	M.add_list2 [x;y;z] [tx;ty;tz] env)
    | ExtArray (Id.L x)
    | ExtTuple (Id.L x)->
       (let tx = find_or_make x env in
	Typing.unify tx t;
	let tx = Typing.deref_typ tx in
	M.add x tx env)
  with
    Unify(m,n)->raise (Unify(m,n))
   |_->raise (Unify(x,t))



let h {name=(Id.L x,t);args=y;formal_fv=z;body=e} =
  let Type.Fun(m,n,l) as t = b_to_i t in
  let w = List.map (fun (x,y)->(x,b_to_i y)) (y@z) in
  try let env = g (M.add_list w !fundata) n e in
      (*Format.eprintf "Success Typing %s : %a\n" x Type.pp t*)()
  with
    Unify(fn,tn)-> Format.eprintf "[Error in Typing %s:%a,%a is not %a]\n"
				  x Type.pp t Closure.pp_t fn Type.pp tn(* Closure.pp_t e*)


let f (Prog(fundefs,e)) =
  List.iter (fun f-> let (Id.L x,t) = f.name in fundata:=M.add x (b_to_i t) !fundata) fundefs;
  List.iter h fundefs;
  h {name=(Id.L "min_caml_main",Type.Fun([Type.Unit],Type.Unit,0));args=[];formal_fv=[];body=e};
  Prog(fundefs,e)
