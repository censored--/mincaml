(* translation into MIPS assembly (infinite number of virtual registers) *)

open Asm

let useargs = ref S.empty

let set x = useargs := S.add x !useargs;x

let classify xts ini addf addi =
  List.fold_left
    (fun acc (x, t) -> match t with
       | Type.Unit -> acc
       | Type.Float _-> addf acc x
       | _ -> addi acc x t) ini xts

let separate xts = 
  classify 
    xts 
    ([], []) 
    (fun (int, float) x -> (int, float @ [x]))
    (fun (int, float) x _ -> (int @ [x], float))

(*オフセットの設定*)
let expand xts ini addf addi = 
  classify
    xts
    ini
    (fun (offset, acc) x -> (offset + 1, addf x offset acc))
    (fun (offset, acc) x t -> (offset + 1, addi x t offset acc))

let rec g env = function (* 式の仮想マシンコード生成 *)
  | Closure.Unit -> Ans (Nop)
  | Closure.Int (i) -> Ans (Li (i))
  | Closure.Float (d) -> Ans (FLi (d))
  | Closure.Neg (x) -> Ans (Neg (set x))
  | Closure.Add (x, y) -> Ans (Add (set x, V (set y)))
  | Closure.Sub (x, y) -> Ans (Sub (set x, V (set y)))
  | Closure.Mul (x, y) -> Ans (Mul (set x, V (set y)))
  | Closure.Div (x, y) -> Ans (Div (set x, V (set y)))
  | Closure.Lsl (x, y) -> Ans (Sll (set x, V (set y)))
  | Closure.Lsr (x, y) -> Ans (Srl (set x, V (set y)))
  | Closure.Asr (x, y) -> Ans (Sra (set x, V (set y)))
  | Closure.FNeg (x) -> Ans (FNeg (set x))
  | Closure.FInv (x) -> Ans (FInv (set x))
  | Closure.FAdd (x, y) -> Ans (FAdd (set x,set y))
  | Closure.FSub (x, y) -> Ans (FSub (set x,set y))
  | Closure.FMul (x, y) -> Ans (FMul (set x,set y))
  | Closure.FDiv (x, y) -> Ans (FDiv (set x,set y))
  | Closure.IfEq (x, y, e1, e2) -> 
      (match M.find x env with
	 | Type.Bool _| Type.Int _-> Ans (IfEq (set x, V (set y), g env e1, g env e2))
	 | Type.Float _ -> Ans (IfFEq (set x, set y, g env e1, g env e2))
	 | _ -> failwith "equality supported only for bool, int, and float")
  | Closure.IfLE (x, y, e1, e2) ->
      (match M.find x env with
	 | Type.Bool _| Type.Int _-> Ans (IfLE (set x, V (set y), g env e1, g env e2))
	 | Type.Float _-> Ans (IfFLE (set x, set y, g env e1, g env e2))
	 | _ -> failwith "inequality supported only for bool, int, and float")
  | Closure.Let ((x, t1), e1, e2) ->
      let e1' = g env e1 in
      let e2' = g (M.add x t1 env) e2 in
	concat e1' (x, t1) e2'
  | Closure.Var (x) ->
      (match M.find x env with
	 | Type.Unit -> Ans (Nop)
	 | Type.Float _ -> Ans (FMov (set x))
	 | _ -> Ans (Mr (set x)))
  | Closure.MakeCls ((x, t), {Closure.entry = l; Closure.actual_fv = ys}, e2) ->
      (* closure のUnitアドレスをセットしてからストア *)
      let e2' = g (M.add x t env) e2 in
      let (offset, store_fv) = 
	expand
	  (List.map (fun y -> (set y, M.find y env)) ys)
	  (1, e2')
	  (fun y offset store_fv -> seq (Stfd (y,  x, C (offset)), store_fv))
	  (fun y _ offset store_fv -> seq (Sw (y, x, C (offset)), store_fv)) in
	Let ((x, t), Mr (reg_hp), 
	     Let ((reg_hp, Type.Int (-1)), Add (reg_hp, C (align offset)), 
	     let z = Id.genid "l" in  
	       Let ((z, Type.Int (-1)), SetL(l), 
		       seq (Sw (z, x, C (0)), store_fv))))
  | Closure.AppCls (x, ys) ->
      let (int, float) = separate (List.map (fun y -> (set y, M.find y env)) ys) in
	Ans (CallCls (x, int, float))
  | Closure.AppDir (Id.L(x), ys) ->
      let (int, float) = separate (List.map (fun y -> (set y, M.find y env)) ys) in
	Ans (CallDir (Id.L(x), int, float))
  | Closure.Tuple (xs) -> (* 組の生成 *)
      let y = Id.genid "t" in
      let (offset, store) = 
	expand
	  (List.map (fun x -> (set x, M.find x env)) xs)
	  (0, Ans (Mr (y)))
	  (fun x offset store -> seq (Stfd (x, y, C (offset)), store))
	  (fun x _ offset store -> seq (Sw (x, y, C (offset)), store))  in
	Let ((y, Type.Tuple (List.map (fun x -> M.find x env) xs,-1)), Mr (reg_hp),
	     Let ((reg_hp, Type.Int (-1)), Add (reg_hp, C (align offset)), store))
  | Closure.LetTuple (xts, y, e2) ->
      let s = Closure.fv e2 in
      let (offset, load) = 
	expand
	  xts
	  (0, g (M.add_list xts env) e2)
	  (fun x offset load ->
	     if not (S.mem x s) then load 
	     else fletd (set x, Lfd (y, C (offset)), load))
	  (fun x t offset load ->
	     if not (S.mem x s) then load 
	     else Let ((set x, t), Lw (y, C (offset)), load)) in
	load
  | Closure.Get (x, y) -> (* 配列の読み出し *)
      let offset = Id.genid "o" in  
	(match M.find x env with
	   | Type.Array (Type.Unit,l) -> Ans (Nop)
	   | Type.Array (Type.Float l1,l2) ->
	       Let ((offset, Type.Int l2), Add (set y, C (0)), 
		    Ans (Lfd (x, V (offset))))
	   | Type.Array (_,l) ->
	       Let ((offset, Type.Int l), Add (set y, C (0)),
		    Ans (Lw (x, V (offset))))
	   | _ -> assert false)
  | Closure.Put (x, y, z) ->
      let offset = Id.genid "o" in 
	(match M.find x env with
	   | Type.Array (Type.Unit,l) -> Ans (Nop)
	   | Type.Array (Type.Float l1,l2) -> 
	       Let ((offset, Type.Int l2), Add (set y, C (0)),
		    Ans (Stfd (z, x, V (offset)))) 
	   | Type.Array (_,l2) ->
	       Let ((offset, Type.Int l2), Add (set y, C (0)), 
		    Ans (Sw (z, x, V (offset)))) 
	   | _ -> assert false)
  | Closure.ExtArray (Id.L(x)) -> Ans(SetL(Id.L("min_caml_" ^ x)))
  | Closure.ExtTuple (Id.L(x)) -> Ans(SetL(Id.L("min_caml_" ^ x)))

(* 関数の仮想マシンコード生成 *)
let h { Closure.name = (Id.L(x), t); Closure.args = yts; 
	Closure.formal_fv = zts; Closure.body = e} =
  let Type.Fun(arg_typs,ret_typ,l) = t in
  let ret_reg = match ret_typ with
    | Type.Unit -> "%dummy"
    | Type.Bool _
    | Type.Int _ 
    | Type.Fun _
    | Type.Tuple _
    | Type.Array _->"%v0"
    | Type.Float _->"%f0"
    | _ -> assert false in
let (int, float) = separate yts in
  let (offset, load) = 
    expand
      zts
      (1, g (M.add x t (M.add_list yts (M.add_list zts M.empty))) e)
      (fun z offset load -> fletd (z, Lfd (reg_cl, C (offset)), load))
      (fun z t offset load -> Let ((z, t), Lw (reg_cl, C (offset)), load)) in
    match t with
      | Type.Fun (_, t2,_) ->
	 funlist := M.add x {argreg = int; fargreg = float; retreg = ret_reg; usereg = 
S.union !useargs (S.of_list (allregs@allfregs))} !funlist;
	 { name = Id.L(x); args = int; fargs = float; body = load; ret = t2}
      | _ -> assert false

(* プログラム全体の仮想マシンコード生成 *)
let f (Closure.Prog (fundefs, e)) =
  let fundefs = List.map h fundefs in
  let e = g M.empty e in
    Prog (fundefs, e)
