open KNormal

let sub x env =
  try
    let (_,y) = Ss.id_find x env in
    match y with
    |Var z-> z
    |_-> x
  with
  |_-> x

let rec g env = function
  | Neg x-> Neg(sub x env)
  | Add(x,y)-> Add(sub x env,sub y env)
  | Sub(x,y)-> Sub(sub x env,sub y env)
  | Mul(x,y)-> Mul(sub x env,sub y env)
  | Div(x,y)-> Div(sub x env,sub y env)
  | Lsl(x,y)-> Lsl(sub x env,sub y env)
  | Lsr(x,y)-> Lsr(sub x env,sub y env)
  | Asr(x,y)-> Asr(sub x env,sub y env)
  | FNeg(x)-> FNeg(sub x env)
  | FInv(x)-> FNeg(sub x env)
  | FAdd(x,y)-> FAdd(sub x env,sub y env)
  | FSub(x,y)-> FSub(sub x env,sub y env)
  | FMul(x,y)-> FMul(sub x env,sub y env)
  | FDiv(x,y)-> FDiv(sub x env,sub y env)
  | IfEq (x,y,z,w)->
     IfEq (sub x env,sub y env,g env z,g env w)
  | IfLE (x,y,z,w)->
     IfLE (sub x env,sub y env,g env z,g env w)
  | ExtFunApp(x,y)->ExtFunApp(sub x env,List.map (fun x->sub x env) y)
  | App (x,y)->App(sub x env,List.map (fun x->sub x env) y)
  | Let ((x,t),y,z)->
     (if Ss.id_exists x env  then
	let env = Ss.id_delete x env in
	g env (Let ((x,t),y,z))
      else
	(try
	    match y with
	    |Unit |Get _|Put _-> Let ((x,t),y,g env z)
	    |App _|ExtFunApp _-> Let ((x,t),y,g env z)
	    |_->
	      let (y',_) = Ss.kn_find y env in
	      let env = Ss.add (x,Var y') env in
	      g env z
	  with
	  |_->
	    let y' = g env y in
	    let env' = Ss.add (x,y') env in
	    Let ((x,t),y',g env' z)))
  | Var x->Var(sub x env)
  | e -> e

let f e = g Ss.empty e
