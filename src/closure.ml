type closure = { entry : Id.l; actual_fv : Id.t list }
type t = (* クロージャ変換後の式 (caml2html: closure_t) *)
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
  | IfEq of Id.t * Id.t * t * t
  | IfLE of Id.t * Id.t * t * t
  | Let of (Id.t * Type.t) * t * t
  | Var of Id.t
  | MakeCls of (Id.t * Type.t) * closure * t
  | AppCls of Id.t * Id.t list
  | AppDir of Id.l * Id.t list
  | Tuple of Id.t list
  | LetTuple of (Id.t * Type.t) list * Id.t * t
  | Get of Id.t * Id.t
  | Put of Id.t * Id.t * Id.t
  | ExtArray of Id.l
  | ExtTuple of Id.l
type fundef = { name : Id.l * Type.t;
		args : (Id.t * Type.t) list;
		formal_fv : (Id.t * Type.t) list;
		body : t }
type prog = Prog of fundef list * t

let rec fv = function
  | Unit | Int(_) | Float(_) | ExtArray(_) | ExtTuple(_)-> S.empty
  | Neg(x) | FNeg(x) | FInv(x) -> S.singleton x
  | Add(x, y) | Sub(x, y) | Mul(x, y) | Div(x, y)
  | FAdd(x, y)| FSub(x, y)| FMul(x, y)| FDiv(x, y)
  | Get(x, y) | Lsl(x, y) | Lsr(x, y) | Asr(x, y) -> S.of_list [x; y]
  | IfEq(x, y, e1, e2)| IfLE(x, y, e1, e2) -> S.add x (S.add y (S.union (fv e1) (fv e2)))
  | Let((x, t), e1, e2) -> S.union (fv e1) (S.remove x (fv e2))
  | Var(x) -> S.singleton x
  | MakeCls((x, t), { entry = l; actual_fv = ys }, e) -> S.remove x (S.union (S.of_list ys) (fv e))
  | AppCls(x, ys) -> S.of_list (x :: ys)
  | AppDir(_, xs) | Tuple(xs) -> S.of_list xs
  | LetTuple(xts, y, e) -> S.add y (S.diff (fv e) (S.of_list (List.map fst xts)))
  | Put(x, y, z) -> S.of_list [x; y; z]

let toplevel : fundef list ref = ref []

let rec g env known = function (* クロージャ変換ルーチン本体 (caml2html: closure_g) *)
  | KNormal.Unit -> Unit
  | KNormal.Int(i) -> Int(i)
  | KNormal.Float(d) -> Float(d)
  | KNormal.Neg(x) -> Neg(x)
  | KNormal.Add(x, y) -> Add(x, y)
  | KNormal.Sub(x, y) -> Sub(x, y)
  | KNormal.Mul(x, y) -> Mul(x, y)
  | KNormal.Div(x, y) -> Div(x, y)
  | KNormal.Lsl(x, y) -> Lsl(x, y)
  | KNormal.Lsr(x, y) -> Lsr(x, y)
  | KNormal.Asr(x, y) -> Asr(x, y)
  | KNormal.FNeg(x) -> FNeg(x)
  | KNormal.FInv(x) -> FInv(x)
  | KNormal.FAdd(x, y) -> FAdd(x, y)
  | KNormal.FSub(x, y) -> FSub(x, y)
  | KNormal.FMul(x, y) -> FMul(x, y)
  | KNormal.FDiv(x, y) -> FDiv(x, y)
  | KNormal.IfEq(x, y, e1, e2) -> IfEq(x, y, g env known e1, g env known e2)
  | KNormal.IfLE(x, y, e1, e2) -> IfLE(x, y, g env known e1, g env known e2)
  | KNormal.Let((x, t), e1, e2) -> Let((x, t), g env known e1, g (M.add x t env) known e2)
  | KNormal.Var(x) -> Var(x)
  | KNormal.LetRec({ KNormal.name = (x, t); KNormal.args = yts; KNormal.body = e1 }, e2) -> (* 関数定義の場合 (caml2html: closure_letrec) *)
      (* 関数定義let rec x y1 ... yn = e1 in e2の場合は、
	 xに自由変数がない(closureを介さずdirectに呼び出せる)
	 と仮定し、knownに追加してe1をクロージャ変換してみる *)
      let toplevel_backup = !toplevel in
      let env' = M.add x t env in
      let known' = S.add x known in
      let e1' = g (M.add_list yts env') known' e1 in
      (* 本当に自由変数がなかったか、変換結果e1'を確認する *)
      (* 注意: e1'にx自身が変数として出現する場合はclosureが必要!
         (thanks to nuevo-namasute and azounoman; test/cls-bug2.ml参照) *)
      let zs = S.diff (fv e1') (S.of_list (List.map fst yts)) in
      let known', e1' =
	if S.is_empty zs then known', e1' else
	(* 駄目だったら状態(toplevelの値)を戻して、クロージャ変換をやり直す *)
	(Format.eprintf "free variable(s) %s found in function %s@." (Id.pp_list (S.elements zs)) x;
	 Format.eprintf "function %s cannot be directly applied in fact@." x;
	 toplevel := toplevel_backup;
	 let e1' = g (M.add_list yts env') known e1 in
	 known, e1') in
      let zs = S.elements (S.diff (fv e1') (S.add x (S.of_list (List.map fst yts)))) in (* 自由変数のリスト *)
      let zts = List.map (fun z -> (z, M.find z env')) zs in (* ここで自由変数zの型を引くために引数envが必要 *)
      toplevel := { name = (Id.L(x), t); args = yts; formal_fv = zts; body = e1' } :: !toplevel; (* トップレベル関数を追加 *)
      let e2' = g env' known' e2 in
      if S.mem x (fv e2') then (* xが変数としてe2'に出現するか *)
	MakeCls((x, t), { entry = Id.L(x); actual_fv = zs }, e2') (* 出現していたら削除しない *)
      else
	(Log.print "eliminating closure(s) %s@." x;
	 e2') (* 出現しなければMakeClsを削除 *)
  | KNormal.App(x, ys) when S.mem x known -> (* 関数適用の場合 (caml2html: closure_app) *)
      Log.print "directly applying %s@." x;
      AppDir(Id.L(x), ys)
  | KNormal.App(f, xs) -> AppCls(f, xs)
  | KNormal.Tuple(xs) -> Tuple(xs)
  | KNormal.LetTuple(xts, y, e) -> LetTuple(xts, y, g (M.add_list xts env) known e)
  | KNormal.Get(x, y) -> Get(x, y)
  | KNormal.Put(x, y, z) -> Put(x, y, z)
  | KNormal.ExtArray(x) -> ExtArray(Id.L(x))
  | KNormal.ExtFunApp(x, ys) -> AppDir(Id.L("min_caml_" ^ x), ys)
  | KNormal.ExtTuple(x) -> ExtTuple(Id.L(x))

let f e =
  toplevel := [];
  let e' = g M.empty S.empty e in
  Prog(List.rev !toplevel, e')

let rec pp_t fmt = function
  | Unit -> Format.fprintf fmt "()"
  | Int i -> Format.fprintf fmt "(%d:int) " i
  | Float f -> Format.fprintf fmt "(%f:float) " f
  | Neg n -> Format.fprintf fmt "-%a" Id.pp n
  | Add (x,y) ->
     Format.fprintf fmt "add  %a, %a" Id.pp x Id.pp y
  | Sub (x,y) ->
     Format.fprintf fmt "sub  %a, %a" Id.pp x Id.pp y
  | Mul (x,y) ->
     Format.fprintf fmt "mul  %a, %a" Id.pp x Id.pp y
  | Div (x,y) ->
     Format.fprintf fmt "div  %a, %a" Id.pp x Id.pp y
  | Lsl (x,y) ->
     Format.fprintf fmt "lsl  %a, %a" Id.pp x Id.pp y
  | Lsr (x,y) ->
     Format.fprintf fmt "lsr  %a, %a" Id.pp x Id.pp y
  | Asr (x,y) ->
     Format.fprintf fmt "asr  %a, %a" Id.pp x Id.pp y
  | FNeg x -> 
     Format.fprintf fmt "fneg %a" Id.pp x
  | FInv x -> 
     Format.fprintf fmt "finv %a" Id.pp x
  | FAdd (x,y)->
     Format.fprintf fmt "fadd %a, %a" Id.pp x Id.pp y
  | FSub (x,y)->
     Format.fprintf fmt "fSub %a, %a" Id.pp x Id.pp y
  | FMul (x,y)->
     Format.fprintf fmt "fmul %a, %a" Id.pp x Id.pp y
  | FDiv (x,y)->
     Format.fprintf fmt "fdiv %a, %a" Id.pp x Id.pp y
  | IfEq (x,y,z,w)->
     Format.fprintf fmt "If\t%a == %a@\n\tthen:@\n\t%a@\n\telse:@\n\t%a@." 
		    Id.pp x Id.pp y pp_t z pp_t w
  | IfLE (x,y,z,w)->
     Format.fprintf fmt "If\t%a <= %a@\n\tthen:@\n\t%a@\n\telse:@\n\t%a@." 
		    Id.pp x Id.pp y pp_t z pp_t w
  | Let ((x,y),z,w)->
     Format.fprintf fmt "\tlet (%a\t:%a)\t= %a in\n%a" 
		    Id.pp x Type.pp y pp_t z pp_t w
  | Var x -> Format.eprintf "\tVar %a" Id.pp x
  | MakeCls ((x,y),z,w)->
     Format.fprintf fmt "MakeCls ((%a,%a),%a,%a)" 
		    Id.pp x Type.pp y pp_clos z pp_t w
  | AppCls (x,y)->
     Format.fprintf fmt "AppCls (%a,[%a])" 
		    Id.pp x Id.p_list y
  | AppDir (x,y)->
     Format.fprintf fmt "AppDir (%a,[%a])" 
		    Id.pp_l x Id.p_list y
  | Tuple x->
     Format.fprintf fmt "Tuple [%a]@." Id.p_list x
  | LetTuple (x,y,z)->
     Format.fprintf fmt "let (%a)\t= %a in %a" 
		    (p_l_p ",") x Id.pp y pp_t z
  | Get (x,y)->
     Format.fprintf fmt "Get (%a,%a)" Id.pp x Id.pp y
  | Put (x,y,z)->
     Format.fprintf fmt "Put (%a,%a,%a)"
		    Id.pp x Id.pp y Id.pp z
  | ExtArray x->
     Format.fprintf fmt "ExtArray (L %a)"
		    Id.pp_l x
  | ExtTuple x->
     Format.fprintf fmt "ExtTuple (L %a)"
		    Id.pp_l x


and p_l_p c fmt = function
  |[]->()
  |[(x,y)]->Format.fprintf fmt "(%a:%a)" Id.pp x Type.pp y
  |(x,y)::z->Format.fprintf fmt "(%a:%a)%s%a" Id.pp x Type.pp y c (p_l_p c) z

and pp_clos fmt = function
  |_-> ()

and pp_fun fmt = function
  |[]->()
  |[{name = (n,t); args = x;formal_fv = y; body = z}]->
    Format.fprintf fmt "{name = (%a:%a); args=(%a);@\n  formal_fv=[%a];@\n  body=\n\t%a}"  Id.pp_l n Type.pp t (p_l_p " ") x (p_l_p ";") y pp_t z
  |{name = (n,t); args = x;formal_fv = y; body = z}::xs->
    Format.fprintf fmt "{name = (%a:%a); args=(%a);@\n  formal_fv=[%a];@\n  body=@\n\t%a};@\n %a"  Id.pp_l n Type.pp t (p_l_p " ") x (p_l_p ";") y pp_t z pp_fun xs
  

let p (Prog (e,t)) =
Format.fprintf Format.err_formatter "Closure.print@.fundefs:@.[%a]@.formula:@\n\tmain:@\n\t%a@." pp_fun e pp_t t
