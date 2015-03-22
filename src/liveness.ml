open Block

let gen_in_block = ref M.empty
let kill_in_block = ref M.empty

let print () =
  let rec c_list = function
    |x::xs-> x^";"^c_list xs
    |_->"" in
  let rec c_two  x y = match x,y with
    |((b_id, gen)::xs,(_,kill)::ys)-> "["^b_id^"]"
				       ^"[gen]"^c_list (S.elements gen)^"\t"
				       ^"[kill]"^c_list (S.elements kill)^"\n"^c_two xs ys
    |_-> "" in
  Format.eprintf "%s@." (c_two (M.bindings !gen_in_block) (M.bindings !kill_in_block))

  (*statementのuse,def情報を取得*)
let get_use_def n =
  let add_if_id x (y,z) = match x with
    |Asm.V x'->(S.add x' y, z)
    |_->(y, z) in
  match n with
  (*use 0*)
  | Li((x,_),_)
  | FLi((x,_),_)
  | SetL((x,_),_)
  | Restore((x,_),_)->(S.empty, S.singleton x)
  (*use 1*)
  | Mr((x,_),y)
  | Neg((x,_),y)
  | FMov((x,_),y)
  | FNeg((x,_),y)
  | FInv((x,_),y)
  | Save((x,_),y,_)->(S.singleton y, S.singleton x)
  (*use 1 and 1 id_or_imm*)
  | Add((x,_),y,z)
  | Sub((x,_),y,z)
  | Mul((x,_),y,z)
  | Div((x,_),y,z)
  | Sll((x,_),y,z)
  | Srl((x,_),y,z)
  | Sra((x,_),y,z)
  | Slw((x,_),y,z)
  | Lw ((x,_),y,z)
  | Lfd((x,_),y,z)
  | IfEq((x,_),y,z,_,_)
  | IfLE((x,_),y,z,_,_)
  | IfGE((x,_),y,z,_,_)->add_if_id z (S.singleton y,S.singleton x)
  (*use 2*)
  | FAdd((x,_),y,z)
  | FSub((x,_),y,z)
  | FMul((x,_),y,z)
  | FDiv((x,_),y,z)
  | IfFEq((x,_),y,z,_,_)
  | IfFLE((x,_),y,z,_,_)->(S.of_list [y;z], S.singleton x)
  (*use 2 and 1 id_or_imm*)
  | Sw ((x,_),y,z,w)
  | Stfd((x,_),y,z,w)->add_if_id w (S.of_list [y;z], S.singleton x)
  (* closure address, integer arguments, and float arguments *)
  | CallCls((x,_),_,_,_)-> assert false
  | CallDir((x,_),_,y,z)->(S.of_list (y@z),S.singleton x)

let use_sites = ref M.empty
let def_sites = ref M.empty
let get_use_sites n = if M.mem n !use_sites then M.find n !use_sites else AS.empty
let get_def_sites n = if M.mem n !def_sites then M.find n !def_sites else AS.empty
let set_use_def_sites (use,def) stmt =
  S.iter  
    (fun x->use_sites := M.add x (AS.add (stmt.s_parent,stmt.s_id) (get_use_sites x)) !use_sites) use;
    S.iter 
      (fun x-> def_sites := M.add x (AS.add (stmt.s_parent,stmt.s_id) (get_def_sites x)) !def_sites) def

(*block内のin,out情報を更新*)
let analyze_block_gen_kill blk =
  let n_of_stmts = M.cardinal blk.stmts  in
  let (gen,kill) = (ref S.empty, ref S.empty) in
  if blk.s_head <> "" then (
    if not (M.mem blk.s_head blk.stmts) then failwith("[head]"^blk.s_head^"[block]"^blk.b_id);
    assert (M.mem blk.s_head blk.stmts);
    let stmt = Array.make n_of_stmts (M.find blk.s_head blk.stmts) in
    let usedef =  ref  (get_use_def stmt.(0).inst) in
    gen := fst !usedef;
    kill := snd !usedef;
    set_use_def_sites !usedef stmt.(0);
    for n = 1 to n_of_stmts - 1 do
      stmt.(n)<-M.find stmt.(n-1).succ blk.stmts;
    done;
    (*ソート済みのstatementsに再帰的に生存解析を実行*)
    for n = 1 to n_of_stmts - 1 do
      usedef := get_use_def stmt.(n).inst;
      set_use_def_sites !usedef stmt.(n);
      gen := S.union (fst !usedef) (S.diff !gen (snd !usedef));
      kill := S.union !kill (snd !usedef)
    done);
  gen_in_block := M.add blk.b_id !gen !gen_in_block;
  kill_in_block := M.add blk.b_id !kill !kill_in_block
			     
let rec add_blocks_in_out blks preds succs =
  let add_block_in_out b blks =
    b.s_liveout <- List.fold_left (fun livein succ_blk -> 
				   if List.mem succ_blk.b_id b.succs then S.union succ_blk.s_livein livein
				   else livein) S.empty blks;
    let gen = if M.mem b.b_id !gen_in_block then M.find b.b_id !gen_in_block else assert false in 
    let kill = if M.mem b.b_id !kill_in_block then M.find b.b_id !kill_in_block else assert false in
    b.s_livein <- S.union gen (S.diff b.s_liveout kill) in
  match preds with
  |(_,b)::bs->
    add_block_in_out b blks;
    add_blocks_in_out blks bs (b::succs)
  |[]->()

let analyze_stmts_survival blk =
  let stmts = List.rev (M.bindings blk.stmts) in
  let analyze_stmt_survival (sid,stmt) =
    if sid = blk.s_tail then
      stmt.v_liveout <- blk.s_liveout
    else
      stmt.v_liveout <- (M.find stmt.succ blk.stmts).v_livein;
    if sid = blk.s_head then
      stmt.v_livein <- blk.s_livein
    else
      let use,def = get_use_def stmt.inst in
      stmt.v_livein <- S.union use (S.diff stmt.v_liveout def) in
  List.iter analyze_stmt_survival stmts

let analyze fundef =
  let blks = List.rev (M.bindings fundef.blocks) in
  List.iter analyze_block_gen_kill (List.map snd blks);
  add_blocks_in_out (List.map snd blks) blks [];
  List.iter analyze_stmts_survival (List.map snd blks)

let h fundef =  analyze fundef; fundef

let f (Prog(fundefs,e)) =
    Prog(List.map h fundefs,h e)
