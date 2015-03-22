open Asm

external geti : float -> int32 = "geti"
external gethi : float -> int32 = "gethi"
external getlo : float -> int32 = "getlo"

let stackset = ref S.empty (* すでに Save された変数の集合 *)
let stackmap = ref [] (* Save された変数のスタックにおける位置 *)
let save x = 
  stackset := S.add x !stackset;
  if not (List.mem x !stackmap) then
    stackmap := !stackmap @ [x]
let savef x = 
  stackset := S.add x !stackset;
  if not (List.mem x !stackmap) then
    stackmap := !stackmap @ [x]
let locate x = 
  let rec loc = function 
    | [] -> []
    | y :: zs when x = y -> 0 :: List.map succ (loc zs)
    | y :: zs -> List.map succ (loc zs) in
    loc !stackmap
let offset x = List.hd (locate x)
let stacksize () = align ((List.length !stackmap + 1) * 1)(*1word = 4byte*)

let reg r = 
  if is_reg r 
  then String.sub r 1 (String.length r - 1)
  else r 

let load_label r label =
  "\tla\t"   ^ (reg r) ^ ", :" ^ label   ^ "\n"

let pow_of_two x = 
  let rec p_o_t x n =
    if x = 1 || x = -1 then (true,n,x) else
      match x mod 2 with
      |0->p_o_t (x/2) (n+1)
      |_->(false,0,0) in p_o_t x 0

(* 関数呼び出しのために引数を並べ替える (register shuffling) *)
let rec shuffle sw xys = 
  (* remove identical moves *)
  let (_, xys) = List.partition (fun (x, y) -> x = y) xys in
    (* find acyclic moves *)
    match List.partition (fun (_, y) -> List.mem_assoc y xys) xys with
      | ([], []) -> []
      | ((x, y) :: xys, []) -> (* no acyclic moves; resolve a cyclic move *)
	  (y, sw) :: (x, y) :: 
	    shuffle sw (List.map (function 
				    | (y', z) when y = y' -> (sw, z)
				    | yz -> yz) xys)
      | (xys, acyc) -> acyc @ shuffle sw xys

type dest = Tail | NonTail of Id.t (* 末尾かどうかを表すデータ型 *)

let rec g oc = function (* 命令列のアセンブリ生成 *)
  | (dest, Ans (exp)) -> g' oc (dest, exp)
  | (dest, Let((x, t), exp, e)) -> g' oc (NonTail (x), exp); g oc (dest, e)

and g' oc = function (* 各命令のアセンブリ生成 *)
  (* 末尾でなかったら計算結果を dest にセット *)
  | (NonTail(_), Nop) -> ()
  | (NonTail(x), Li(i)) when i >= -32768 && i < 32768 -> 
     Printf.fprintf oc "\tli\t%s, %d\n" (reg x) i
  | (NonTail(x), Li(i)) ->
     Printf.fprintf oc "\tla\t%s, %d\n" (reg x) i
  | (NonTail(x), FLi(d)) ->
     if d = 0.0 then
       Printf.fprintf oc "\tmtc1\t%s, %s\n" "zero" (reg x)
     else
       (Printf.fprintf oc "\tla\t%s, %ld #%f\n" reg_tmp (geti d) d;
	Printf.fprintf oc "\tmtc1\t%s, %s\n" reg_tmp (reg x))
  | (NonTail(x), SetL(Id.L(y))) -> 
     let s = load_label x y in Printf.fprintf oc "%s" s
  | (NonTail(x), Mr(y)) when x = y -> ()
  | (NonTail(x), Mr(y)) -> Printf.fprintf oc "\tmove\t%s, %s\n" (reg x) (reg y)
  | (NonTail(x), Neg(y)) -> Printf.fprintf oc "\tneg\t%s, %s\n" (reg x) (reg y)
  | (NonTail(x), Add(y, V(z))) -> 
     Printf.fprintf oc "\tadd\t%s, %s, %s\n" (reg x) (reg y) (reg z)
  | (NonTail(x), Add(y, C(z))) -> 
     if reg x <> reg y || z <> 0 then Printf.fprintf oc "\taddi\t%s, %s, %d\n" (reg x) (reg y) z
  | (NonTail(x), Sub(y, V(z))) -> 
     Printf.fprintf oc "\tsub\t%s, %s, %s\n" (reg x) (reg y) (reg z)
  | (NonTail(x), Sub(y, C(z))) -> 
     if reg x <> reg y || z <> 0 then Printf.fprintf oc "\tsubi\t%s, %s, %d\n" (reg x) (reg y) z
  | (NonTail(x), Mul(y, V(z))) -> (*ビットシフトにするかの場合分け*)
     Printf.fprintf oc "\tmult\t%s, %s, %s\n" (reg x) (reg y) (reg z)
  | (NonTail(x), Mul(y, C(z))) ->
     let (b,n,s) = pow_of_two z in
     if b then
       if s > 0 then
	 Printf.fprintf oc "\tsll\t%s, %s, %d\n" (reg x) (reg y) n
       else
	 (Printf.fprintf oc "\tsll\t%s, %s, %d\n" (reg x) (reg y) n;
	  Printf.fprintf oc "\tneg\t%s,%s" (reg x) (reg x))
     else
       (Printf.fprintf oc "\tli\t%s, %d\n" reg_tmp z;
	Printf.fprintf oc "\tmult\t%s, %s, %s\n" (reg x) (reg y) reg_tmp)
  | (NonTail(x), Div(y, V(z))) -> 
     Printf.fprintf oc "\tdiv\t%s, %s, %s\n" (reg x) (reg y) (reg z)
  | (NonTail(x), Div(y, C(z))) ->
     let (b,n,s) = pow_of_two z in
     if b then
       if s > 0 then
	 Printf.fprintf oc "\tsra\t%s, %s, %d\n" (reg x) (reg y) n
       else
	 (Printf.fprintf oc "\tsra\t%s, %s, %d\n" (reg x) (reg y) n;
	  Printf.fprintf oc "\tneg\t%s,%s" (reg x) (reg x))
     else 
       Printf.fprintf oc "\tli\t%s, %d\n" reg_tmp z;
     Printf.fprintf oc "\tdiv\t%s, %s, %s\n" (reg x) (reg y) reg_tmp
  | (NonTail(x), Sll(y, V(z))) -> 
     Printf.fprintf oc "\tsllv\t%s, %s, %s\n" (reg x) (reg y) (reg z)
  | (NonTail(x), Sll(y, C(z))) ->
     Printf.fprintf oc "\tsll\t%s, %s, %d\n" (reg x) (reg y) z
  | (NonTail(x), Srl(y, V(z))) -> 
     Printf.fprintf oc "\tsrlv\t%s, %s, %s\n" (reg x) (reg y) (reg z)
  | (NonTail(x), Srl(y, C(z))) ->
     Printf.fprintf oc "\tsrl\t%s, %s, %d\n" (reg x) (reg y) z
  | (NonTail(x), Sra(y, V(z))) -> 
     Printf.fprintf oc "\tsrav\t%s, %s, %s\n" (reg x) (reg y) (reg z)
  | (NonTail(x), Sra(y, C(z))) ->
     Printf.fprintf oc "\tsra\t%s, %s, %d\n" (reg x) (reg y) z
  | (NonTail(x), Slw(y, V(z))) -> 
     Printf.fprintf oc "\tsllv\t%s, %s, %s\n" (reg x) (reg y) (reg z)
  | (NonTail(x), Slw(y, C(z))) -> 
     Printf.fprintf oc "\tsll\t%s, %s, %d\n" (reg x) (reg y) z
  | (NonTail(x), Lw(y, V(z))) ->
     Printf.fprintf oc "\tadd\t%s, %s, %s\n" reg_tmp (reg y) (reg z);
     Printf.fprintf oc "\tlw\t%s, %d, %s\n" (reg x) 0 reg_tmp
  | (NonTail(x), Lw(y, C(z))) -> 
     Printf.fprintf oc "\tlw\t%s, %d, %s\n" (reg x) z (reg y)
  | (NonTail(_), Sw(x, y, V(z))) ->
     Printf.fprintf oc "\tadd\t%s, %s, %s\n" reg_tmp (reg y) (reg z);
     Printf.fprintf oc "\tsw\t%s, %d, %s\n" (reg x) 0 reg_tmp 
  | (NonTail(_), Sw(x, y, C(z))) -> 
     Printf.fprintf oc "\tsw\t%s, %d, %s\n" (reg x) z (reg y)
  | (NonTail(x), FMov(y)) when x = y -> ()
  | (NonTail(x), FMov(y)) -> Printf.fprintf oc "\tfmov\t%s, %s\n" (reg x) (reg y)
  | (NonTail(x), FNeg(y)) -> 
     Printf.fprintf oc "\tfneg\t%s, %s\n" (reg x) (reg y)
  | (NonTail(x), FInv(y)) -> 
     Printf.fprintf oc "\tfinv\t%s, %s\n" (reg x) (reg y)
  | (NonTail(x), FAdd(y, z)) -> 
     Printf.fprintf oc "\tfadd\t%s, %s, %s\n" (reg x) (reg y) (reg z)
  | (NonTail(x), FSub(y, z)) -> 
     Printf.fprintf oc "\tfsub\t%s, %s, %s\n" (reg x) (reg y) (reg z)
  | (NonTail(x), FMul(y, z)) -> 
     Printf.fprintf oc "\tfmul\t%s, %s, %s\n" (reg x) (reg y) (reg z)
  | (NonTail(x), FDiv(y, z)) -> 
     Printf.fprintf oc "\tfdiv\t%s, %s, %s\n" (reg x) (reg y) (reg z)
  | (NonTail(x), Lfd(y, V(z))) ->
     Printf.fprintf oc "\tadd\t%s, %s, %s\n" reg_tmp (reg z) (reg y);
     Printf.fprintf oc "\tlwc1\t%s, %d, %s\n" (reg x) 0 reg_tmp
  | (NonTail(x), Lfd(y, C(z))) -> 
     Printf.fprintf oc "\tlwc1\t%s, %d, %s\n" (reg x) z (reg y)
  | (NonTail(_), Stfd(x, y, V(z))) ->
     Printf.fprintf oc "\tadd\t%s, %s, %s\n" reg_tmp (reg z) (reg y);
     Printf.fprintf oc "\tswc1\t%s, %d, %s\n" (reg x) 0 reg_tmp
  | (NonTail(_), Stfd(x, y, C(z))) ->
     Printf.fprintf oc "\tswc1\t%s, %d, %s\n" (reg x) z (reg y)
  | (NonTail(_), Comment(s)) -> Printf.fprintf oc "#\t%s\n" s
  (* 退避の仮想命令の実装 *)
  | (NonTail(_), Save(x, y))
       when List.mem x allregs && not (S.mem y !stackset) ->
     save y;
     Printf.fprintf oc "\tsw\t%s, %d, %s\n" (reg x) (offset y) reg_sp
  | (NonTail(_), Save(x, y)) 
       when List.mem x allfregs && not (S.mem y !stackset) ->
     savef y;
     Printf.fprintf oc "\tswc1\t%s, %d, %s\n" (reg x) (offset y) reg_sp
  | (NonTail(_), Save(x, y)) ->
     if (not (S.mem y !stackset)) then print_string ("Error:Save "^x^","^y^"\n");
     assert (S.mem y !stackset)
  (* 復帰の仮想命令の実装 *)
  | (NonTail(x), Restore(y)) when List.mem x allregs ->
     Printf.fprintf oc "\tlw\t%s, %d, %s\n" (reg x) (offset y) reg_sp
  | (NonTail(x), Restore(y)) ->
     assert (List.mem x allfregs);
     Printf.fprintf oc "\tlwc1\t%s, %d, %s\n" (reg x) (offset y) reg_sp
  (* 末尾だったら計算結果を第一レジスタにセット *)
  | (Tail, (Nop | Sw _ | Stfd _ | Comment _ | Save _ as exp)) ->
     g' oc (NonTail(Id.gentmp Type.Unit), exp);
     Printf.fprintf oc "\tjr\tra\n";
  | (Tail, (Li _ | SetL _ | Mr _ | Neg _ | Add _ | Sub _ | Mul _ | Div _ |
	    Sll _| Srl  _ | Sra _| Slw _ | Lw  _ as exp)) -> 
     g' oc (NonTail(regs.(0)), exp);
     Printf.fprintf oc "\tjr\tra\n";
  | (Tail, (FLi _ | FMov _ | FNeg _ | FInv _ | FAdd _ | FSub _ | FMul _ | FDiv _ |
            Lfd _ as exp)) ->
     g' oc (NonTail(fregs.(0)), exp);
     Printf.fprintf oc "\tjr\tra\n";
  | (Tail, (Restore(x) as exp)) ->
     (match locate x with
      | [i] -> g' oc (NonTail(regs.(0)), exp)
      | [i; j] when (i + 1 = j) -> g' oc (NonTail(fregs.(0)), exp)
      | _ -> assert false);
     Printf.fprintf oc "\tjr\tra\n";
  | (Tail, IfEq(x, V(y), e1, e2)) ->
     g'_tail_if oc e1 e2 "beq" "bne" (reg x) (reg y)
  | (Tail, IfEq(x, C(y), e1, e2)) ->
     Printf.fprintf oc "\tli\t%s, %d\n" reg_tmp y;
     g'_tail_if oc e1 e2 "beq" "bne" (reg x) reg_tmp
  | (Tail, IfLE(x, V(y), e1, e2)) ->
     g'_tail_if oc e1 e2 "ble" "bgt" (reg x) (reg y)
  | (Tail, IfLE(x, C(y), e1, e2)) ->
     Printf.fprintf oc "\tli\t%s, %d\n" reg_tmp y;
     g'_tail_if oc e1 e2 "ble" "bgt" (reg x) reg_tmp
  | (Tail, IfGE(x, V(y), e1, e2)) ->
     g'_tail_if oc e1 e2 "ble" "bgt" (reg y) (reg x)
  | (Tail, IfGE(x, C(y), e1, e2)) ->
     Printf.fprintf oc "\tli\t%s, %d\n" reg_tmp y;
     g'_tail_if oc e1 e2 "ble" "bgt" reg_tmp (reg x)
  | (Tail, IfFEq(x, y, e1, e2)) ->
     Printf.fprintf oc "\tc.oeq\t%s, %s\n" (reg x) (reg y);
     g'_tail_if_f oc e1 e2 "bc1t" "bc1f"
  | (Tail, IfFLE(x, y, e1, e2)) ->
     Printf.fprintf oc "\tc.ole\t%s, %s\n" (reg x) (reg y);
     g'_tail_if_f oc e1 e2 "bc1t" "bc1f"
  | (NonTail(z), IfEq(x, V(y), e1, e2)) ->
     g'_non_tail_if oc (NonTail(z)) e1 e2 "beq" "bne" (reg x) (reg y)
  | (NonTail(z), IfEq(x, C(y), e1, e2)) ->
     if y <> 0 then
       (Printf.fprintf oc "\tli\t%s, %d\n" reg_tmp y;
	g'_non_tail_if oc (NonTail(z)) e1 e2 "beq" "bne" (reg x) reg_tmp)
     else
       g'_non_tail_if oc (NonTail(z)) e1 e2 "beq" "bne" (reg x) "zero"
  | (NonTail(z), IfLE(x, V(y), e1, e2)) ->
     g'_non_tail_if oc (NonTail(z)) e1 e2 "ble" "bgt" (reg x) (reg y)
  | (NonTail(z), IfLE(x, C(y), e1, e2)) ->
     if y <> 0 then
       (Printf.fprintf oc "\tli\t%s, %d\n" reg_tmp y;
	g'_non_tail_if oc (NonTail(z)) e1 e2 "ble" "bgt" (reg x) reg_tmp)
     else
       g'_non_tail_if oc (NonTail(z)) e1 e2 "ble" "bgt" (reg x) "zero"
  | (NonTail(z), IfGE(x, V(y), e1, e2)) ->
     g'_non_tail_if oc (NonTail(z)) e1 e2 "ble" "bgt" (reg y) (reg x)
  | (NonTail(z), IfGE(x, C(y), e1, e2)) ->
     if y <> 0 then
     (Printf.fprintf oc "\tli\t%s, %d\n" reg_tmp y;
     g'_non_tail_if oc (NonTail(z)) e1 e2 "ble" "bgt" reg_tmp (reg x))
     else
       g'_non_tail_if oc (NonTail(z)) e1 e2 "ble" "bgt" "zero" (reg x)
  | (NonTail(z), IfFEq(x, y, e1, e2)) ->
     Printf.fprintf oc "\tc.oeq\t%s, %s\n" (reg x) (reg y);
     g'_non_tail_if_f oc (NonTail(z)) e1 e2 "bc1t" "bc1f"
  | (NonTail(z), IfFLE(x, y, e1, e2)) ->
     Printf.fprintf oc "\tc.ole\t%s, %s\n" (reg x) (reg y);
     g'_non_tail_if_f oc (NonTail(z)) e1 e2 "bc1t" "bc1f"
  (* 関数呼び出しの仮想命令の実装 *)
  | (Tail, CallCls(x, ys, zs)) -> (* 末尾呼び出し *)
     g'_args oc [(x, reg_cl)] ys zs;
     Printf.fprintf oc "\tlw\t%s, 0, %s\n" (reg reg_sw) (reg reg_cl);
     Printf.fprintf oc "\tjr\t%s\n" (reg reg_sw);
  | (Tail, CallDir(Id.L(x), ys, zs)) -> (* 末尾呼び出し *)
     g'_args oc [] ys zs;
     Printf.fprintf oc "\tj\t:%s\n" x
  | (NonTail(a), CallCls(x, ys, zs)) ->
     g'_args oc [(x, reg_cl)] ys zs;
     let ss = stacksize () in
     Printf.fprintf oc "\tsw\t%s, %d, %s\n" reg_rp (ss - 1) reg_sp;
     if ss <> 0 then Printf.fprintf oc "\taddi\t%s, %s, %d\n" reg_sp reg_sp ss;
     Printf.fprintf oc "\tlw\t%s, %d, %s\n" reg_tmp 0 (reg reg_cl);
     Printf.fprintf oc "\tjalr\t%s\n" reg_tmp;
     if  ss <> 0 then Printf.fprintf oc "\tsubi\t%s, %s, %d\n" reg_sp reg_sp ss;
     Printf.fprintf oc "\tlw\t%s, %d, %s\n" reg_rp (ss - 1) reg_sp;
     (if List.mem a allregs && a <> regs.(0) then 
	Printf.fprintf oc "\tmove\t%s, %s\n" (reg a) (reg regs.(0)) 
      else if List.mem a allfregs && a <> fregs.(0) then 
	Printf.fprintf oc "\tfmov\t%s, %s\n" (reg a) (reg fregs.(0)));
  | (NonTail(a), CallDir(Id.L(x), ys, zs)) ->g_calldir oc a x ys zs

and g_calldir oc a x ys zs =
  g'_args oc [] ys zs;
  let ss = stacksize () in
  (match x with
   |"min_caml_print_char"-> 
     Printf.fprintf oc "\twrite\ta0\t#print_char\n"
   |"min_caml_read_int"->
     (*let s =  "\tread\t"^reg a^"\t#read_int\n"
		^"\tsll\t"^reg a^", "^reg a^", 8\n"
		^"\tread\t"^reg a^"\n"
		^"\tsll\t"^reg a^", "^reg a^", 8\n"
		^"\tread\t"^reg a^"\n"
		^"\tsll\t"^reg a^", "^reg a^", 8\n"
		^"\tread\t"^reg a^"\n" in*)
     let s = "\tread\tat\t#read_int\n"
	     ^"\tsll\tat, at, 8\n"
	     ^"\tread\tat\n"
	     ^"\tsll\tat, at, 8\n"
	     ^"\tread\tat\n"
	     ^"\tsll\tat, at, 8\n"
	     ^"\tread\tat\n"
	     ^"\tmove\tv0, at\n" in
     Printf.fprintf oc "%s" s
   |"min_caml_fabs"->
     Printf.fprintf oc "\tabs.s\tf0, f0\n"
   |_-> 
     (Printf.fprintf oc "\tsw\t%s, %d, %s\n" reg_rp (ss - 1) reg_sp;
      if ss <> 0 then Printf.fprintf oc "\taddi\t%s, %s, %d\n" reg_sp reg_sp ss;
      Printf.fprintf oc "\tjal\t:%s\n" x;
      if ss <> 0 then Printf.fprintf oc "\tsubi\t%s, %s, %d\n" reg_sp reg_sp ss;
      Printf.fprintf oc "\tlw\t%s, %d, %s\n" reg_rp (ss - 1) reg_sp);
     if List.mem a allregs && a <> regs.(0) (*&& x <> "min_caml_read_int"*) then
       Printf.fprintf oc "\tmove\t%s, %s\n" (reg a) (reg regs.(0))
     else if List.mem a allfregs && a <> fregs.(0)  then
       Printf.fprintf oc "\tfmov\t%s, %s\n" (reg a) (reg fregs.(0)))

    
and g'_tail_if_z oc e1 e2 b bn r = 
  let b_else = Id.genid (b ^ "_else") in
  Printf.fprintf oc "\t%s\t%s, :%s\n" bn r b_else;
  let stackset_back = !stackset in
  g oc (Tail, e1);
  Printf.fprintf oc "label\t:%s\n" b_else;
  stackset := stackset_back;
  g oc (Tail, e2)
and g'_tail_if_f oc e1 e2 b bn= 
  let b_else = Id.genid (b ^ "_else") in
  Printf.fprintf oc "\t%s\t:%s\n" bn b_else;
  let stackset_back = !stackset in
  g oc (Tail, e1);
  Printf.fprintf oc "label\t:%s\n" b_else;
  stackset := stackset_back;
  g oc (Tail, e2)
and g'_tail_if oc e1 e2 b bn r1 r2 = 
  let b_else = Id.genid (b ^ "_else") in
  Printf.fprintf oc "\t%s\t%s, %s, :%s\n" bn r1 r2 b_else;
  let stackset_back = !stackset in
  g oc (Tail, e1);
  Printf.fprintf oc "label\t:%s\n" b_else;
  stackset := stackset_back;
  g oc (Tail, e2)
and g'_non_tail_if_z oc dest e1 e2 b bn r = 
  let b_else = Id.genid (b ^ "_else") in
  let b_cont = Id.genid (b ^ "_cont") in
  Printf.fprintf oc "\t%s\t%s, :%s\n" bn r b_else;
  let stackset_back = !stackset in
  g oc (dest, e1);
  let stackset1 = !stackset in
  Printf.fprintf oc "\tj\t:%s\n" b_cont;
  Printf.fprintf oc "label\t:%s\n" b_else;
  stackset := stackset_back;
  g oc (dest, e2);
  Printf.fprintf oc "label\t:%s\n" b_cont;
  let stackset2 = !stackset in
  stackset := S.inter stackset1 stackset2
and g'_non_tail_if_f oc dest e1 e2 b bn = 
  let b_else = Id.genid (b ^ "_else") in
  let b_cont = Id.genid (b ^ "_cont") in
  Printf.fprintf oc "\t%s\t:%s\n" bn b_else;
  let stackset_back = !stackset in
  g oc (dest, e1);
  let stackset1 = !stackset in
  Printf.fprintf oc "\tj\t:%s\n" b_cont;
  Printf.fprintf oc "label\t:%s\n" b_else;
  stackset := stackset_back;
  g oc (dest, e2);
  Printf.fprintf oc "label\t:%s\n" b_cont;
  let stackset2 = !stackset in
  stackset := S.inter stackset1 stackset2
and g'_non_tail_if oc dest e1 e2 b bn r1 r2 = 
  let b_else = Id.genid (b ^ "_else") in
  let b_cont = Id.genid (b ^ "_cont") in
  Printf.fprintf oc "\t%s\t%s, %s, :%s\n" bn r1 r2 b_else;
  let stackset_back = !stackset in
  g oc (dest, e1);
  let stackset1 = !stackset in
  Printf.fprintf oc "\tj\t:%s\n" b_cont;
  Printf.fprintf oc "label\t:%s\n" b_else;
  stackset := stackset_back;
  g oc (dest, e2);
  Printf.fprintf oc "label\t:%s\n" b_cont;
  let stackset2 = !stackset in
  stackset := S.inter stackset1 stackset2


and g'_args oc x_reg_cl ys zs = 
  let (i, yrs) = 
    List.fold_left
      (fun (i, yrs) y -> (i + 1, (y, regs.(i)) :: yrs))
      (2, x_reg_cl) ys in
  List.iter
    (fun (y, r) -> Printf.fprintf oc "\tmove\t%s, %s\n" (reg r) (reg y))
    (shuffle reg_sw yrs);
  let (d, zfrs) = 
    List.fold_left
      (fun (d, zfrs) z -> (d + 1, (z, fregs.(d)) :: zfrs))
      (0, []) zs in
  List.iter
    (fun (z, fr) -> Printf.fprintf oc "\tfmov\t%s, %s\n" (reg fr) (reg z))
    (shuffle reg_fsw zfrs)

let h oc { name = Id.L(x); args = _; fargs = _; body = e; ret = _} =
  Printf.fprintf oc "label\t:%s\n" x;
  stackset := S.empty;
  stackmap := [];
  g oc (Tail, e)

let f oc (Prog(fundefs, e)) =
  Format.eprintf "generating assembly...@.";
  Printf.fprintf oc "\t.globl  :main\n";
  Printf.fprintf oc "label\t:main # main entry point\n";
  Printf.fprintf oc "   # main program start\n";
  stackset := S.empty;
  stackmap := [];
  g oc (NonTail("_R_0"), e);
  Printf.fprintf oc "   # main program end\n";
(*  Printf.fprintf oc "\tmove\tr3, %s\n" regs.(0); *)
(* for OS:  Printf.fprintf oc "\tjr\tra\n"*)
  Printf.fprintf oc "label\t:end_loop\n";
  Printf.fprintf oc "\tj\t:end_loop\n";
  List.iter (fun fundef -> h oc fundef) fundefs
