open Asm

let assertfalse x y = if not x then failwith y

let rec g' blks b s =
  let (xt,e,next_blk) = to_exp blks b s.Block.inst in
  (*もしstatementが基本ブロックの末尾か、でないなら次のstatementを見つけてLetin式*)
  if s.Block.s_id = b.Block.s_tail 
  then
    (*後続節がなければAns、あればletin*)
    (if List.length next_blk.Block.succs <= 0 
     then
       (Ans e, next_blk)
     else
       (assert (List.length next_blk.Block.succs = 1);
	let next_blk' = M.find (List.hd next_blk.Block.succs) blks in
	assert (List.length next_blk'.Block.preds = 2);
	if List.length b.Block.succs = 1 then
	  (Ans e,next_blk)
	else if M.is_empty next_blk'.Block.stmts then
	  (Ans e,next_blk')
	else
	  (assert (M.mem next_blk'.Block.s_head next_blk'.Block.stmts);
	   let next_stmt = M.find next_blk'.Block.s_head next_blk'.Block.stmts in
	   let (e', next_blk) = g' blks next_blk' next_stmt in
	   (Let (xt, e, e'), next_blk))))
  else
    let (e', next_blk) = g' blks b (M.find s.Block.succ b.Block.stmts) in
    (Let(xt, e, e'), next_blk)

and to_exp blks blk stmt = 
  (*Format.eprintf "%s@." blk.Block.b_id; Block.print_t stmt; *)
  match stmt with
  | Block.Li (xt,x)->(xt,Li x,blk)
  | Block.FLi(xt,x)->(xt,FLi x,blk)
  | Block.SetL(xt,x)->(xt,SetL x,blk)
  | Block.Mr(xt, x)->(xt,Mr x,blk)
  | Block.Neg(xt, x)->(xt, Neg x,blk)
  | Block.Add(xt,x,y)->(xt,Add(x,y),blk)
  | Block.Sub(xt,x,y)->(xt,Sub(x,y),blk)
  | Block.Mul(xt,x,y)->(xt,Mul(x,y),blk)
  | Block.Div(xt,x,y)->(xt,Div(x,y),blk)
  | Block.Sll(xt,x,y)->(xt,Sll(x,y),blk)
  | Block.Srl(xt,x,y)->(xt,Srl(x,y),blk)
  | Block.Sra(xt,x,y)->(xt,Sra(x,y),blk)
  | Block.Slw(xt,x,y)->(xt,Slw(x,y),blk)
  | Block.Lw(xt,x,y)->(xt,Lw(x,y),blk)
  | Block.Sw(xt,x,y,z)->(xt,Sw(x,y,z),blk)
  | Block.FMov(xt,x)->(xt,FMov x,blk)
  | Block.FNeg(xt,x)->(xt,FNeg x,blk)
  | Block.FInv(xt,x)->(xt,FInv x,blk)
  | Block.FAdd(xt,x,y)->(xt,FAdd(x,y),blk)
  | Block.FSub(xt,x,y)->(xt,FSub(x,y),blk)
  | Block.FMul(xt,x,y)->(xt,FMul(x,y),blk)
  | Block.FDiv(xt,x,y)->(xt,FDiv(x,y),blk)
  | Block.Lfd(xt,x,y)->(xt,Lfd(x,y),blk)
  | Block.Stfd(xt,x,y,z)->(xt,Stfd(x,y,z),blk)
  (* virtual instructions *)
  | Block.IfEq(xt,x,y,bt,bf)->(*if文での最後2つの引数はthenブロックとelseブロックのID*)
	 assert (M.mem bt blks);
	 assert (M.mem bf blks);
	   let blk_t,blk_f = M.find bt blks, M.find bf blks in
	 let (e1, n_blk1), (e2, n_blk2) =g blks blk_t, g blks blk_f in
	 assertfalse (n_blk1.Block.succs = n_blk2.Block.succs) (n_blk1.Block.b_id^","^n_blk2.Block.b_id^" in "^blk.Block.b_id);
	 (xt,IfEq(x,y,e1,e2),n_blk1)
  | Block.IfLE(xt,x,y,bt,bf)->
	 assert (M.mem bt blks);
	 assert (M.mem bf blks);
	 let blk_t,blk_f = M.find bt blks, M.find bf blks in
	 let (e1, n_blk1), (e2, n_blk2) = g blks blk_t, g blks blk_f in
	 assert (n_blk1.Block.succs = n_blk2.Block.succs);
	 (xt,IfLE(x,y,e1,e2),n_blk1)
  | Block.IfGE(xt,x,y,bt,bf)->
	 assert (M.mem bt blks);
	 assert (M.mem bf blks);
	 let blk_t,blk_f = M.find bt blks, M.find bf blks in
	 let (e1, n_blk1), (e2, n_blk2) = g blks blk_t, g blks blk_f in
	 assert (n_blk1.Block.succs = n_blk2.Block.succs);
	 (xt,IfLE(x,y,e1,e2),n_blk1)
  | Block.IfFEq(xt,x,y,bt,bf)->
	 assert (M.mem bt blks);
	 assert (M.mem bf blks);
	 let blk_t,blk_f = M.find bt blks, M.find bf blks in
	 let (e1, n_blk1), (e2, n_blk2) = g blks blk_t, g blks blk_f in
	 assert (n_blk1.Block.succs = n_blk2.Block.succs);
	 (xt,IfFEq(x,y,e1,e2),n_blk1)
  | Block.IfFLE(xt,x,y,bt,bf)->
	 assert (M.mem bt blks);
	 assert (M.mem bf blks);
	 let blk_t,blk_f = M.find bt blks, M.find bf blks in
	 let (e1, n_blk1), (e2, n_blk2) = g blks blk_t, g blks blk_f in
	 assert (n_blk1.Block.succs = n_blk2.Block.succs);
	 (xt,IfFLE(x,y,e1,e2),n_blk1)
  (* closure address, integer arguments, and float arguments *)
  | Block.CallCls(xt,x,y,z)-> (xt,CallCls(x,y,z),blk)
  | Block.CallDir(xt,x,y,z)-> (xt,CallDir(x,y,z),blk)
  | Block.Save(xt,x,y)->(xt,Save(x,y),blk)
  | Block.Restore(xt,x)->(xt,Restore(x),blk)

and g blks b =
  if b.Block.s_head = "" then Ans Nop, b
  else
    let(e,new_blk) = g' blks b (M.find b.Block.s_head b.Block.stmts) in
    e,new_blk
    

let h {Block.name=x;Block.args=y;Block.fargs=z;Block.ret=t;Block.blocks=blks;Block.b_head=b;Block.use_regs} =
  let (e,_) = g blks (M.find b blks) in
  {name=x;args=y;fargs=z;body= e; ret =t}

let f (Block.Prog(fundefs,e)) =
    Prog (List.map h fundefs,(h e).body)
