open Block
open Coloring

let useregs = ref S.empty

let modify x = 
  try
    if x.[0] = '%' then
      match x.[1] with
      |'r'->(if String.length x > 3 then
	       match Char.escaped x.[2]^Char.escaped x.[3] with
	       |"00"->"%zero"
	       |"01"->"%at"
	       |"02"->"%v0"
	       |"03"->"%v1"
	       |"04"->"%a0"
	       |"05"->"%a1"
	       |"06"->"%a2"
	       |"07"->"%a3"
	       |"08"->"%t0"
	       |"09"->"%t1"
	       |"10"->"%t2"
	       |"11"->"%t3"
	       |"12"->"%t4"
	       |"13"->"%t5"
	       |"14"->"%t6"
	       |"15"->"%t7"
	       |"16"->"%s0"
	       |"17"->"%s1"
	       |"18"->"%s2"
	       |"19"->"%s3"
	       |"20"->"%s4"
	       |"21"->"%s5"
	       |"22"->"%s6"
	       |"23"->"%s7"
	       |"24"->"%t8"
	       |"25"->"%t9"
	       |"26"->"%k0"
	       |"27"->"%k1"
	       |"28"->"%gp"
	       |"29"->"%sp"
	       |"30"->"%fp"
	       |"31"->"%ra"
	       |_->assert false
	     else x)
      |'f'->if String.length x > 3 then
	       (match x.[2] with
	       |'0'->"%f"^Char.escaped x.[3]
	       |_->x)
	     else x
      |_->x
    else x
  with y->(Format.eprintf "[backtrace]Error in modify %s@." x;raise y)

let rp x = try
    if get_type x <> Type.Unit 
    then let y = modify (get_color x) in useregs := S.add y !useregs; y else "%dummy"
  with y ->(Format.eprintf "[backtrace]Error in rp %s@." x;raise y)

let rpcv x = match x with 
  |Asm.V x->Asm.V (rp x) 
  | e -> e

let replace_funlist fundef =
  let Id.L name = fundef.name in
  if not (name = "_min_caml_main") then
    assertwith (M.mem name !Asm.funlist) ("Not found "^name^" in funlist\n");
  let fundata = M.find name !Asm.funlist in
  Asm.funlist := M.add name
		   {Asm.argreg = List.sort compare(List.fold_right (fun x rs-> rp x::rs) fundata.Asm.argreg []);
		   Asm.fargreg = List.sort compare(List.fold_right (fun x rs-> rp x::rs) fundata.Asm.fargreg []);
		   Asm.retreg = rp fundata.Asm.retreg;
		   Asm.usereg = !useregs
		   } !Asm.funlist;
  fundef.args <- List.sort compare (List.map rp fundef.args);
  fundef.fargs <- List.sort compare (List.map rp fundef.fargs);
  fundef.use_regs <- S.elements !useregs

let allocate fundef =
  try
  M.iter (fun _ blk->
	  M.iter (fun s_id stmt->
		  try
		  let x = match stmt.inst with
			       | Li ((x,t),y)->Li((rp x,t),y)
			       | FLi((x,t),y)->FLi((rp x,t),y)
			       | SetL((x,t),y)-> SetL((rp x,t),y)
			       | Mr ((x,t),y)->Mr ((rp x,t),rp y)
			       | Neg ((x,t),y)->Neg ((rp x,t),rp y)
			       | Add ((x,t),y,z)->Add ((rp x, t),rp y,rpcv z)
			       | Sub ((x,t),y,z)->Sub ((rp x, t),rp y,rpcv z)
			       | Mul ((x,t),y,z)->Mul ((rp x, t),rp y,rpcv z)
			       | Div ((x,t),y,z)->Div ((rp x, t),rp y,rpcv z)
			       | Sll ((x,t),y,z)->Sll ((rp x, t),rp y,rpcv z)
			       | Srl ((x,t),y,z)->Srl ((rp x, t),rp y,rpcv z)
			       | Sra ((x,t),y,z)->Sra ((rp x, t),rp y,rpcv z)
			       | Slw ((x,t),y,z)->Slw ((rp x, t),rp y,rpcv z)
			       | Lw ((x,t),y,z)->Lw ((rp x, t),rp y,rpcv z)
			       | Sw ((x,t),y,z,w)-> Sw((rp x,t),rp y, rp z, rpcv w)
			       | FMov ((x,t),y)-> FMov ((rp x,t), rp y)
			       | FNeg ((x,t),y)-> FNeg ((rp x,t), rp y)
			       | FInv ((x,t),y)-> FInv ((rp x,t), rp y)
			       | FAdd ((x,t),y,z)-> FAdd ((rp x,t),rp y,rp z)
			       | FSub ((x,t),y,z)-> FSub ((rp x,t),rp y,rp z)
			       | FMul ((x,t),y,z)-> FMul ((rp x,t),rp y,rp z)
			       | FDiv ((x,t),y,z)-> FDiv ((rp x,t),rp y,rp z)
			       | Lfd ((x,t),y,z)-> Lfd((rp x,t),rp y,rpcv z)
			       | Stfd ((x,t),y,z,w)-> Stfd((rp x,t),rp y,rp z,rpcv w)
			       | IfEq ((x,t),y,z,w,v)->IfEq((rp x,t),rp y,rpcv z,w,v)
			       | IfLE ((x,t),y,z,w,v)->IfLE((rp x,t),rp y,rpcv z,w,v)
			       | IfGE ((x,t),y,z,w,v)->IfGE((rp x,t),rp y,rpcv z,w,v) 
			       | IfFEq ((x,t),y,z,w,v)->IfFEq((rp x,t),rp y,rp z,w,v)
			       | IfFLE ((x,t),y,z,w,v)->IfFLE((rp x,t),rp y,rp z,w,v)
			       | CallCls ((x,t),y,z,w)->CallCls((rp x,t),rp y,List.map rp z,List.map rp w)
			       | CallDir ((x,t),y,z,w)->
				 CallDir ((rp x,t),y,List.map rp z,List.map rp w)
			       | Save ((x,t),y,z)->Save((x,t),rp y,z)
			       | Restore ((x,t),y)->Restore((rp x,t),y) in
		  stmt.inst <- x
		  with e ->Format.eprintf "[backtrace]Error in iter stmt %s@." s_id;raise e)
		 blk.stmts) fundef.blocks 
  with x->(Format.eprintf "[backtrace]Error in allocate %s@." (Id.string_L fundef.name);raise x)	 

let check_type fundef =
  try
    List.iter (fun x-> if not(List.mem x Asm.allregs) then invalid_arg (x^" is not GPR")) fundef.args;
    List.iter (fun x-> if not(List.mem x Asm.allfregs) then invalid_arg (x^" is not FPR")) fundef.fargs
  with
    Invalid_argument x->
    let Id.L name = fundef.name in
    let {Asm.argreg=args; Asm.fargreg=fargs; Asm.retreg=ret; Asm.usereg=regs} = M.find name !Asm.funlist in
    Format.eprintf "%s@.(%s,\t{argreg = %s;\n\t\tfargreg = %s;\n\t\tretreg = %s;\n\t\tusereg = %s})@."
		  x name (Id.t_list_to_string args) (Id.t_list_to_string fargs) ret (S.to_string regs);
    print_fundef fundef;
    raise Not_found

let replace_stmt_livenss stmt blk =
  stmt.v_livein <-S.fold (fun x live-> S.add (rp x) live) stmt.v_livein S.empty; 
  stmt.v_liveout <-S.fold (fun x live-> S.add (rp x) live) stmt.v_liveout S.empty

let replace_blk_liveness blk =
  blk.s_livein <- S.fold (fun x live-> S.add (rp x) live) blk.s_livein S.empty;
  blk.s_liveout <- S.fold (fun x live-> S.add (rp x) live) blk.s_liveout S.empty

let save_regs_CallDir fundef =
  let Id.L name = fundef.name in
  try
  let fundata = M.find name !Asm.funlist in
  let rec save_regs_CallDir_in_stmt stmt_id blk =
    try
    if stmt_id <> "" then
      (let stmt = M.find stmt_id blk.stmts in
       (match stmt.inst with
	| CallDir ((x,t),Id.L y,z,w)->
	   (*呼び出し先で使用されるためにSaveする必要のあるレジスタ*)
	   let to_save =
	     if M.mem y !Asm.funlist then
	       (M.find y !Asm.funlist).Asm.usereg
	     else
	       S.of_list gpr in
	   (*呼び出し元の関数定義の更新*)
	   fundata.Asm.usereg <- S.union to_save fundata.Asm.usereg;
	   (*関数呼び出しの際に退避させなければならない変数をレジスタ割り当て状況を見ながら決定する。*)
	   let save_regs = S.fold (fun x regs-> if S.mem (rp x) to_save then S.add x regs else regs) stmt.v_liveout S.empty in
	   let pred = ref stmt.pred in
	   let succ = stmt_id in
	   S.iter (fun reg->
		   let save_stmt = {s_id = gen_statement_id ();
				    s_parent = blk.b_id;
				    inst = Save(("%dummy",Type.Unit),rp reg,reg);
				    pred = !pred;
				    succ = succ;
				    v_livein = S.empty;
				    v_liveout = S.empty}  in
		   (*predのstatementのsuccを更新する*)
		   if !pred <> "" then 
		     (M.find !pred blk.stmts).succ <-save_stmt.s_id
		   else
		     blk.s_head <- save_stmt.s_id;
		   (*succのstatementのpredを更新する*)
		   stmt.pred <- save_stmt.s_id;
		   (*次のstatementのpredをこのstatementに設定する。*)
		   pred := save_stmt.s_id;
		   (*基本ブロックにsave_statementを追加*)
		   blk.stmts <- M.add save_stmt.s_id save_stmt blk.stmts)
		  save_regs
	|_->());
       replace_stmt_livenss stmt blk;
       save_regs_CallDir_in_stmt stmt.succ blk)
    with x->(Format.eprintf "[backtrace]Error in save_regs_CallDir_in_stmt %s %s@."stmt_id blk.b_id;raise x) in
  let rec save_regs_CallDir_in_block b_id =
    try
      let blk = M.find b_id fundef.blocks in
      save_regs_CallDir_in_stmt blk.s_head blk;
      replace_blk_liveness blk;
      List.iter save_regs_CallDir_in_block blk.succs
    with x->(Format.eprintf "[backtrace]Error in save_regs_CallDir_in_block %s@." b_id;raise x) in
  save_regs_CallDir_in_block fundef.b_head
  with x->(Format.eprintf "[backtrace]Error in save_regs_CallDir %s@." name;print_fundef fundef;raise x)




let h debug fundef = 
  Coloring.main true debug fundef;
  allocate fundef;
  replace_funlist fundef;
  check_type fundef;
  save_regs_CallDir fundef;
  fundef

let f debug (Prog(fundefs,fundef)) =
  let fundefs' = List.map (h debug) fundefs in
  let fundef' = h debug fundef in
  let r = Prog(fundefs',fundef') in
  (*Asm.eprint_funlist ();*) r
