open Closure
(*もしargsがtuple型を持っているとき、その引数の名前が前後に登場する変数は分解しない。また返り値となるときも同様*)

exception TupleError


let rec g except (env:(Id.t list) M.t) = function
  | LetTuple (xts,y,z)->
     (try 
	 let yts = M.find y env in
	 g except env
	   (List.fold_right2 (fun x y z->Let(x,Var y,z)) xts yts z)
       with
       |_->LetTuple(xts,y,g except env z))
  | Let ((x,t),y,z)->
     (match y with
      |Tuple yts-> 	
	(try
	    g_addlist except env (x,t) yts z
	  with
	  |_->Let((x,t),y,g except env z))
      |Var x' ->
	(try
	    let yts = M.find x' env in
	    g_addlist except env (x,t) yts z
	  with
	  |_->g except env z)
      |_-> g except env z)
  | IfEq (x,y,z,w)->IfEq(x,y,g except env z,g except env w)
  | IfLE (x,y,z,w)->IfLE(x,y,g except env z,g except env w)
  | e -> e

and g_addlist except (env:Id.t list M.t) ((x:Id.t),t) (yts:Id.t list) (z:t) =
  match t with
  |Type.Tuple (t,_)->
    let (_,xts) = 
      List.fold_right
	(fun t (i,z)->(i+1,((x^string_of_int i),t)::z))
	t (0,[]) in
    g except
      (M.add x yts env)
      (List.fold_right2 (fun x y z ->Let(x,Var y,z)) xts yts z)
  |_->raise TupleError
      
  


let rec add_tail env = function
  | IfEq (_,_,x,y)->add_tail (add_tail env x) y
  | IfLE (_,_,x,y)->add_tail (add_tail env x) y
  | Let (_,_,x)->add_tail env x
  | Var x ->S.add x env
  | Tuple xs ->List.fold_left (fun env x->S.add x env) env xs
  | MakeCls (_,_,x)->add_tail env x
  | AppCls (_,xs)-> List.fold_left (fun env x->S.add x env) env xs
  | AppDir (_,xs)-> List.fold_left (fun env x->S.add x env) env xs
  | LetTuple (_,_,x)-> add_tail env x
  | ExtTuple x -> (match x with
		  |Id.L x ->S.add x env)
  | e -> env

let rec add_args env yts = 
  List.fold_left 
    (fun env (yx,yt)->match yt with
		      |Type.Tuple (p,q)->S.add yx env
		      |_->env)
    S.empty yts

let rec h {name=(x, t); args=yts; formal_fv=zts; body=e} =
  let except = add_args (add_args S.empty yts) zts in
  let except = add_tail except e in
  {name=(x,t); args=yts; formal_fv=zts; body=g except M.empty e}
	   
let f (Prog(fundefs,e)) =
  Prog(List.map h fundefs,g S.empty M.empty e)
