open Util
open Block
open Format

let assertwith bool  message = if not bool then failwith message

let debug = false

type worklist = {
  mutable simplify: S.t;
  mutable moves: S.t;
  mutable freeze: S.t;
  mutable spill: S.t;
}
(*変数、レジスタ情報*)
let var_env = ref M.empty
let arg_gpr = Array.to_list(Array.init 24 (fun i->Printf.sprintf (if i+4 < 10 then "%%r0%d" else "%%r%d") (i+4)))
let val_gpr = ["%v0";"%v1"]
let gpr = arg_gpr@val_gpr
let all_gpr = ["%zero";"%at";"%gp";"%sp";"%ra"]@Asm.allregs
let fpr = Array.to_list(Array.init 32 (fun i->Printf.sprintf (if i < 10 then "%%f0%d" else "%%f%d") i))

(*接点のワークリスト、集合、スタック*)
let worklist : worklist = {simplify=S.empty;moves=S.empty;freeze=S.empty;spill=S.empty}
let precolored = ref (S.of_list (gpr@fpr))
let initial = ref S.empty
let spilled_nodes = ref S.empty
let coalesced_nodes = ref S.empty
let colored_nodes = ref S.empty
let select_stack : Id.t list ref= ref []

(*転送集合*)
let coalesced_moves = ref S.empty
let constrained_moves = ref S.empty
let frozen_moves = ref S.empty
let active_moves = ref S.empty

(*let worklist_moves = worklist.moves*)

(*その他のデータ構造*)
let adj_set = ref AS.empty
let adj_list = ref M.empty
let degree = ref M.empty
let move_list = ref M.empty
let alias = ref M.empty
let color = ref M.empty

let string_color () =
  if !color = M.empty then "No Color Assignment"
  else
    List.fold_left (fun str (x,c) -> str^(if x <> c then x^":"^c^"\n" else "")) "" (M.bindings !color)

let print () =
  (*Format.eprintf "%s@." (string_color ())*) ()

(*関数呼び出し、受け取りに用いられる変数*)
let ret_nodes = ref S.empty
let arg_nodes = ref S.empty
(*関数呼び出しをまたいで生存する変数*)
let stride_nodes = ref S.empty
(*再帰関数かの判定*)
let is_loop = ref false
(*転送命令の集合*)
let move_insts = ref M.empty

(*変数レジスタの希望表*)

let wish_env = ref M.empty

let get_wish n = if M.mem n !wish_env then M.find n !wish_env else ([],[])

let add_wish n (wish:string list) (avoid : string list)  =
  let (e1,e2) = get_wish n in
  wish_env := M.add n (wish@e1, avoid@e2)  !wish_env

let set_var_wish_env fundef stmt livein liveout =
  match stmt.inst with
  | CallDir ((x,t), Id.L name, args, fargs) when Id.L name <> fundef.name ->
     (*仮引数は一致させたい*)
     List.iter2 (fun arg arg_reg-> let rm = List.remove arg_reg  arg_gpr in add_wish arg [arg_reg] rm) args arg_gpr;
     List.iter2 (fun farg farg_reg->add_wish farg [farg_reg] (List.remove farg_reg fpr)) fargs fpr;
     (*返り値も一致させたい*)
     (match t with
      |Type.Unit->()
      |Type.Float _->add_wish x ["%f00"] []
      |_-> add_wish x ["%v0"] [])
     (*関数呼び出しをまたいで生存する変数は引数を避けたい*)
  |_->()

(*初期化、関数のデータ解析関数群*)
let quotient t = match t with
  |Type.Float _| Type.Unit -> t 
  |_-> Type.Int 0

let get_var_type stmt =
  let pick_id x = match x with
    |Asm.V x'->[(x',Type.Int 0)]
    |_->[] in
  match stmt.inst with
  | Save _->[]
  | Li (xt,_)
  | FLi (xt,_)
  | SetL (xt,_)
  | Restore (xt,_)->[xt]
  | Mr  (xt,y)
  | Neg (xt,y)->[xt;(y,Type.Int 0)]
  | Add (xt,y,z)
  | Sub (xt,y,z)
  | Mul (xt,y,z)
  | Div (xt,y,z)
  | Sll (xt,y,z)
  | Srl (xt,y,z)
  | Sra (xt,y,z)
  | Slw (xt,y,z)
  | Lw  (xt,y,z)
  | Lfd (xt,y,z)
  | IfEq(xt,y,z,_,_)
  | IfLE(xt,y,z,_,_)
  | IfGE(xt,y,z,_,_)->pick_id z@[xt;(y,Type.Int 0)]
  | Sw  (xt,y,z,w)->pick_id w@[xt;(y,Type.Int 0);(z,Type.Int 0)]
  | Stfd(xt,y,z,w)->pick_id w@[xt;(y,Type.Float 0);(z,Type.Int 0)]
  | FMov(xt,y)
  | FNeg(xt,y)
  | FInv(xt,y)->[xt;(y,Type.Float 0)]
  | FAdd(xt,y,z)
  | FSub(xt,y,z)
  | FMul(xt,y,z)
  | FDiv(xt,y,z)
  | IfFEq(xt,y,z,_,_)
  | IfFLE(xt,y,z,_,_)->[xt;(y,Type.Float 0);(z,Type.Float 0)]
  (* closure address, integer arguments, and float arguments *)
  | CallCls (xt,name,args,fargs)->assert false
  | CallDir (xt,Id.L name,args,fargs)->
     xt::List.map (fun a->(a,Type.Int 0)) args@List.map (fun f->(f,Type.Float 0)) fargs

let set_var_env fundef =
  var_env := M.empty;
  List.iter (fun x-> var_env := M.add x (Type.Int 0) !var_env) (fundef.args@gpr@all_gpr);
  List.iter (fun x-> var_env := M.add x (Type.Float 0) !var_env) (fundef.fargs@fpr@Asm.allfregs);
  var_env:= M.add "%dummy" Type.Unit !var_env;
  M.iter 
    (fun _ blk -> 
     M.iter 
       (fun _ stmt->
	var_env := List.fold_left (fun env (x,t)->M.add x (quotient t) env) 
				  !var_env (get_var_type stmt)) blk.stmts) fundef.blocks

let is_move_instruction stmt = match stmt.inst with
  |Mr _|FMov _-> true
  |_-> false

let update list n id =
  let id_list =if M.mem n !list then M.find n !list else S.empty in
  list := M.add n (S.add id id_list) !list

let increment_degree n =
  let degree_n = 1 + if M.mem n !degree then M.find n !degree else 0 in
  degree := M.add n degree_n !degree

let add_edge(u,v) =
  if (not (AS.mem (u,v) !adj_set)) && u <> v then
    ((*if debug then Format.eprintf "add_edge (%s,%s)@." u v;*)
     adj_set := AS.union !adj_set (AS.of_list [(u,v);(v,u)]);
     if not (S.mem u !precolored) then
       (update adj_list u v;
	increment_degree u);
     if not (S.mem v !precolored) then
       (update adj_list v u;
	increment_degree v))

let initialize is_first fundef =
  set_var_env fundef;(*関数の変数の型情報を登録*)

  precolored := S.of_list (gpr@all_gpr@fpr@Asm.allfregs);(*既彩色節をレジスタで初期化*)
  worklist.simplify <- S.empty;
  worklist.moves <- S.empty;
  worklist.freeze <- S.empty;
  worklist.spill <- S.empty;
  
  select_stack := [];
  
  coalesced_moves := S.empty;
  constrained_moves := S.empty;
  frozen_moves := S.empty;

  adj_set := AS.empty;
  adj_list := M.fold (fun x _ env -> M.add x S.empty env) !var_env M.empty;
  degree := M.fold (fun x _ env -> M.add x 0 env) !var_env M.empty;
  move_list := M.empty;
  alias := M.empty;
  color := S.fold (fun x env -> M.add x x env) !precolored M.empty;
  color := M.add "%dummy" "%dummy" !color;

  List.iter (fun x -> List.iter (fun y -> add_edge (x,y)) fundef.args) fundef.args;
  List.iter (fun x -> List.iter (fun y -> add_edge (x,y)) fundef.fargs) fundef.fargs;

  wish_env := M.empty;

  if is_first then 
    (initial := M.fold (fun x t env-> if not (S.mem x !precolored) && t <> Type.Unit then S.add x env else env) !var_env S.empty;
     colored_nodes := S.empty;
     spilled_nodes := S.empty;
     coalesced_nodes := S.empty)
		    

(*build関数群*)

(*バグの温床*)
let set_liveness_around_call_dir fundef stmt livein liveout = match stmt.inst with
  |CallDir ((x,_), Id.L name, args,fargs)->
    ret_nodes := S.add x !ret_nodes;
    arg_nodes := S.union !arg_nodes (S.of_list (args@fargs));
    if Id.L name = fundef.name then is_loop := true
  |_->()

let add_move_insts stmt = match stmt.inst with
  |Mr ((dst,_),src)
  |FMov((dst,_),src)->move_insts := M.add stmt.s_id (dst,src) !move_insts
  |_->()

     

let build fundef =
  M.iter
    (fun _ b->
     let live = ref b.s_liveout in
     (*forall stmt ∈ instructions(b)について逆順で*)
     let rec iter stmt_id =
       if stmt_id <> "" then
	 let liveout = !live in
	 (let stmt = M.find stmt_id b.stmts in
	 let use,def = Liveness.get_use_def stmt.inst in
	 (*転送命令の登録*)
	 if is_move_instruction stmt then
	   (live := S.diff !live use;
	    S.iter (fun n ->
		    update move_list n stmt_id) (S.union use def);
	    worklist.moves <- S.add stmt_id worklist.moves;
	    add_move_insts stmt);
	 live := S.union !live def;
	 S.iter (fun d-> S.iter (fun l-> add_edge(l,d)) !live) def;
	 live := S.union use (S.diff !live def);
	 let livein = !live in
	 set_liveness_around_call_dir fundef stmt livein liveout;
	 set_var_wish_env fundef stmt livein liveout;
	 iter stmt.pred)
       else
	 (let use,def = (S.empty, S.of_list (fundef.args@fundef.fargs)) in
	 live := S.union !live def;
	 S.iter (fun d-> S.iter (fun l-> add_edge(l,d)) !live) def;
	 live := S.union use (S.diff !live def)) in
	 
     iter b.s_tail) fundef.blocks

(*make_worklistの関数群*)
	 
let get_degree n = try M.find n !degree with _-> failwith ("get_degree "^n)

let set_degree n d = degree := M.add n d !degree

let get_type n = try M.find n !var_env with _-> failwith ("get_type "^n)

let get_K n = match get_type n with |Type.Float _->List.length fpr |_->List.length gpr

let move_related n = M.mem n !move_list

let make_worklist () =
  S.iter (fun n->
	   initial := S.remove n !initial;
	   if not (M.mem n !degree) then failwith ("couldn't find "^n^"'s degree in make_worklist ()\n");
	   if get_degree n > get_K n then
	     worklist.spill <- S.add n worklist.spill
	   else if move_related n then
	     worklist.freeze <- S.add n worklist.freeze
	   else
	     worklist.simplify <-S.add n worklist.simplify) !initial

(*単純化*)

let adjacent n = 
 if M.mem n !adj_list then
   S.diff (M.find n !adj_list) (S.union (S.of_list !select_stack) !coalesced_nodes)
 else S.empty

let node_moves n =
  if M.mem n !move_list then
    S.inter (M.find n !move_list) (S.union !active_moves worklist.moves)
  else S.union !active_moves worklist.moves
 

(*仮引数、CallDirの引数、CallDirの返り値、その他の順で彩色したいので、その逆で選んでいく*)
let pop_simplify_worklist fundef =
  let s2 = S.inter !ret_nodes worklist.simplify in
  let s3 = S.inter !arg_nodes worklist.simplify in
  let s4 = S.inter (S.of_list (fundef.args@fundef.fargs)) worklist.simplify in
  let s1 = S.diff worklist.simplify (S.union s2 (S.union s3 s4)) in
  let ans = List.hd (S.elements s1@S.elements s2@S.elements s3@S.elements s4) in
  worklist.simplify<-S.remove ans worklist.simplify;
  ans

let push n stack = stack:= n::!stack

let pop stack = match !stack with
  |s::ss-> stack:= ss; s
  |_->assert false

let simplify fundef =
  let n = pop_simplify_worklist fundef in
  push n select_stack

let enable_moves nodes =
  S.iter (fun n->
	  S.iter (fun m->
		  if S.mem m !active_moves then
		    (active_moves := S.remove m !active_moves;
		     worklist.moves <- S.add m worklist.moves)) (node_moves n)) nodes

let decrement_degree m =
  let d = get_degree m in
  set_degree m (d-1);
  if d = get_K m then
    (enable_moves (S.add m (adjacent m));
     worklist.spill <- S.remove m worklist.spill;
     if move_related m then
       worklist.freeze <- S.add m worklist.freeze
     else
       worklist.simplify <- S.add m worklist.simplify)

(*合併*)

let add_worklist u =
  if not (S.mem u !precolored) && not (move_related u) && get_degree u < get_K u then
	   (worklist.freeze <- S.remove u worklist.freeze;
	    worklist.simplify <- S.add u worklist.simplify)
	     
let ok (t,r) = get_degree t < get_K t || S.mem t !precolored || AS.mem (t,r) !adj_set

let conservative nodes =
  let k = ref 0 in
  S.iter (fun n->
	  if get_degree n >= get_K n then k:= !k + 1) nodes; S.is_empty nodes || !k < get_K (S.min_elt nodes)

let rec get_alias n =
  if S.mem n !coalesced_nodes then
    get_alias (M.find n !alias)
  else n

let get_color n = if M.mem (get_alias n) !color then M.find (get_alias n) !color 
		  else failwith ("get_color "^n)

let combine u v =
  if debug then eprintf "Convine %s, %s" u v;
  if S.mem v worklist.freeze then
    worklist.freeze <- S.remove v worklist.freeze
  else
    worklist.spill <- S.add v worklist.spill;
  coalesced_nodes := S.add v !coalesced_nodes;
  alias := M.add v u !alias;
  move_list := M.add u (S.union (M.find u !move_list) (M.find v !move_list)) !move_list;
  enable_moves (S.singleton v);
  S.iter (fun t->
	  add_edge (t,u);
	  decrement_degree t) (adjacent v);
  if get_degree u >= get_K u && S.mem u worklist.freeze then
    (worklist.freeze <- S.remove u worklist.freeze;
     worklist.spill <- S.add u worklist.spill)

let coalesce fundef =
  let m = S.min_elt worklist.moves in
  assert (M.mem m !move_insts);
  let x,y = M.find m !move_insts in
  let x = get_alias x in
  let y = get_alias y in
  let (u,v) = if S.mem y !precolored then (y,x) else (x,y) in
  worklist.moves <- S.remove m worklist.moves;
  if u = v then
    (coalesced_moves := S.add m !coalesced_moves;
     add_worklist u)
  else if S.mem v !precolored || AS.mem (u,v) !adj_set then
    (constrained_moves := S.add m !constrained_moves;
     add_worklist u;
     add_worklist v)
  else if S.mem u !precolored && S.for_all (fun t-> ok (t,u)) (adjacent v) 
	  || not (S.mem u !precolored) && conservative (S.union (adjacent u) (adjacent v)) then
    (constrained_moves := S.add m !constrained_moves;
     combine u v;
     add_worklist u)
  else
    active_moves := S.add m !active_moves

(*凍結*)

let freeze_moves u =
  S.iter (fun m->
	  assert (M.mem m !move_insts);
	  let x,y = M.find m !move_insts in
	  let v = if get_alias y = get_alias u then get_alias x else get_alias y in
	  active_moves := S.remove m !active_moves;
	  frozen_moves := S.add m !frozen_moves;
	  (*レジスタでないかも判定する必要がある*)
	  if not (S.mem v !precolored) && node_moves v = S.empty && get_degree v < get_K v then
	    (worklist.freeze <- S.remove v worklist.freeze;
	     worklist.simplify <- S.add v worklist.simplify)
	 ) (node_moves u)

let freeze () =
  let u = S.min_elt worklist.freeze in
  worklist.freeze <- S.remove u worklist.freeze;
  worklist.simplify <- S.add u worklist.simplify;
  freeze_moves u


(*spill*)

(*発見的手法で選択する
 現状では適当に選んでいるだけなので、要改良*)
let pop_spill_worklist () =
  let e = S.min_elt worklist.spill in
  worklist.spill <- S.remove e worklist.spill; e

let select_spill () =
  let m = pop_spill_worklist () in
  worklist.simplify <- S.add m worklist.simplify;
  freeze_moves m

(*彩色*)

let choose_color n t fundef ok_colors = 
  let where x arg = 
    let rec w x n = function
      |y::ys->if y = x then n else w x (n+1) ys
      |[]->(-1) in w x 0 arg in
  match t with
  |Type.Float _->
    let p = where n fundef.fargs in
    let reg = if p<10 then "%f0"^string_of_int p else "%f"^string_of_int p in
    if p >= 0 && S.mem reg ok_colors then
      reg
    else
      S.max_elt ok_colors
  |_->
    let p = where n fundef.args in
    let reg = if p+4<10 then "%r0"^string_of_int(p+4) else "%r"^string_of_int(p+4) in
    if p >= 0 && S.mem reg ok_colors then
      reg
    else
      S.max_elt ok_colors

	    
let assign_colors fundef =
  assert (S.is_empty (S.inter !precolored (S.of_list !select_stack))); (* レジスタはスタックには絶対積まれていないはず *)
  assert (S.is_empty (S.inter !precolored !coalesced_nodes)); (* レジスタはスタックには絶対積まれていないはず *)
  while !select_stack <> [] do
    let n = pop(select_stack) in
    Format.eprintf "[Color]\n%s@." (string_color ());
    let t = get_type n in
    let ok_colors = ref (S.of_list (match t with 
				    |Type.Float _-> fpr 
				    | _->gpr)) in
    assert (M.mem n !adj_list);
    if true then eprintf "[adj_list %s]%s@." n (S.to_string (M.find n !adj_list));
    S.iter (fun w->
	    if S.mem (get_alias w) (S.union !colored_nodes !precolored) then
	      (assertwith (M.mem (get_alias w) !color) ("Not found "^w^"'s alias : "^(get_alias w)^" in color");
	       ok_colors := S.remove (M.find (get_alias w) !color) !ok_colors)
	   ) (M.find n !adj_list);
    if !ok_colors = S.empty then
      spilled_nodes := S.add n !spilled_nodes
    else
      ((*if debug then eprintf "[colored nodes]%s@." (S.to_string !colored_nodes);*)
       colored_nodes := S.add n !colored_nodes;
       let c = choose_color n t fundef !ok_colors in
       (*if debug then*) eprintf "Color %s => %s@." n c;
       color := M.add n c !color)
  done;
  S.iter (fun n->
	  assert (M.mem (get_alias n) !color);
	  (*if debug then*) eprintf "Color %s => %s@." n (M.find (get_alias n) !color);
	  color := M.add n (M.find (get_alias n) !color) !color) !coalesced_nodes

(*プログラムの書き換え*)

let insert_arg_save fundef n = ()

let insert_save fundef site n new_temp = ()

let insert_restore fundef new_temps (blk_id,stmt_id) x =
  let blk = M.find blk_id fundef.blocks in
  let stmt = M.find stmt_id blk.stmts in
  let new_stmt_id = Block.gen_statement_id () in
  let new_temp = Id.genid x in
  let t = get_type x in
  new_temps := S.add new_temp !new_temps;
  let new_stmt = {
    s_id = new_stmt_id;
    s_parent = blk.b_id;
    inst = Restore ((new_temp, t), x);
    pred = stmt.pred;
    succ = stmt.s_id;
    v_livein = S.empty;
    v_liveout = S.empty } in
  stmt.pred <- new_stmt_id;
  if new_stmt.pred = "" then 
    blk.s_head <- new_stmt_id
  else 
    let pred = M.find new_stmt.pred blk.stmts in
    pred.succ <- new_stmt_id;
    blk.stmts <- M.add new_stmt_id new_stmt blk.stmts;
    stmt.inst <- Block.replace stmt x new_temp

let rewrite_program fundef =
  eprintf "Coloring %s again.....@." (Id.string_L fundef.name);
  let new_temps = ref S.empty in
  (*各v in spilled_nodes毎にメモリ位置を割付け、定義と使用のそれぞれについて新しいテンポラリv_iを生成し、
   プログラム（命令）中にv_iの各定義の後に格納命令を挿入し、v_iの各使用前に取り出し命令を挿入する。
   すべてのv_iを集合newTempsに入れる。*)
  S.iter (fun v->
	  eprintf "Spill %s@." v;
	  (*引数の場合関数の最初にSaveを挿入*)
	  if List.mem v (fundef.args@fundef.fargs) then insert_arg_save fundef v;
	  (*各定義の前にSaveを挿入*)
	  let new_temp = Id.genid v in
	  AS.iter (fun site-> insert_save fundef site v new_temp) (Liveness.get_def_sites v);
	  (*各使用の前にRestoreを挿入*)
	  AS.iter (fun site-> insert_restore fundef new_temps site v) (Liveness.get_use_sites v)
	 ) !spilled_nodes;
  spilled_nodes := S.empty;
  initial := S.union !colored_nodes (S.union !coalesced_nodes !new_temps);
  colored_nodes := S.empty;
  coalesced_nodes := S.empty

let rec main is_first debug_mode fundef =
  Liveness.analyze fundef;
  if debug_mode then Block.print_fundef fundef;
  initialize is_first  fundef;
  build fundef;
  (*eprintf "[adj_list]\n%s@." (M.to_string !adj_list S.to_string);*)
  make_worklist ();
  while not (worklist.simplify = S.empty && worklist.moves = S.empty && worklist.freeze = S.empty && worklist.spill = S.empty) do
    if worklist.simplify <> S.empty then simplify fundef 
    else if worklist.moves <> S.empty then coalesce fundef 
    else if worklist.freeze <> S.empty then freeze ()
    else if worklist.spill <> S.empty then select_spill ();

    if true then
      (Format.eprintf "[simplify]\t%s@." (S.to_string worklist.simplify);
       Format.eprintf "[moves]\t%s@." (S.to_string worklist.moves);
       Format.eprintf "[freeze]\t%s@." (S.to_string worklist.freeze);
       Format.eprintf "[spill]\t%s@." (S.to_string worklist.spill))
  done;
  assign_colors fundef;
  if debug then print ();
  if !spilled_nodes <> S.empty then
    (rewrite_program fundef;
     main false debug_mode fundef)

let f (Prog(fundefs,fundef)) =
  List.fold_left (fun _ fundef-> Format.eprintf "Coloring %s@." (Id.string_L fundef.name);main true debug fundef) () fundefs;
  Format.eprintf "Coloring %s@." (Id.string_L fundef.name); main true debug fundef;
  Prog(fundefs, fundef)

