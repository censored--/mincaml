let limit = ref 1000
let extension = ref ".s"
let debug = ref false
let fdiv = ref false
let finv_software = ref false
let coloring = ref false

let rec iter n e = (* 最適化処理をくりかえす (caml2html: main_iter) *)
  Format.eprintf "iteration %d@." n;
  if n = 0 then e else
  let e' = Subelim.f (Elim.f (ConstFold.f (Inline.f (Assoc.f (Beta.f e))))) in
  if e = e' then e else
  iter (n - 1) e'

let lexbuf outchan l = (* バッファをコンパイルしてチャンネルへ出力する (caml2html: main_lexbuf) *)
  Id.counter := 0;
  (*if !debug then Typing.extenv := M.empty;*)
  Format.eprintf "Lexing and parsing....\n";
  let sy = (Myparser.exp Mylexer.token l) in
  (*if !debug then Syntax.p sy;*)
  Format.eprintf "Typing....\n";
  let ty = (Typing.f sy) in
  (*if !debug then Typing.p sy;*)
  Format.eprintf "kNormalizing....\n";
  let kn = KNormal.f ty !fdiv !finv_software in
  Format.eprintf "Alpha conversion....\n";
  let al = Alpha.f kn in
  Format.eprintf "Iterating....\n";
  let it = iter !limit al in
  if !debug then KNormal.p it;
  Format.eprintf "Closuring....\n";
  let cl = Closure.f it in
  if !debug then Closure.p cl;
  Format.eprintf "Typing Closure....\n";
  let cl = Typing_closure.f cl in
  Format.eprintf "Virtualize and simulating....\n";
  let v = Simm.f (Virtual.f cl) in
  if !debug then Asm.p v;
  if !coloring then
    (Format.eprintf "Convert to Block.t.....\n";
     let v = Block.f v in
     Format.eprintf "Analyze liveness and register coloring.....\n";
     let v = RegAlloc2.f !debug v in
     if !debug then Block.print v;
     Format.eprintf "Convert to Asm.t.....\n";
     let v = ToAsm.f v in
     if !debug then Asm.p v;
     if !debug then Emit.f stdout v;
     Emit.f outchan v)
  else
    (if !debug then Format.eprintf "Register allocating....\n";
     let v = RegAlloc.f v in
     if !debug then Asm.p v;
     if !debug then Emit.f stdout v;
     Emit.f outchan v)
		

let string s = lexbuf stdout (Lexing.from_string s) (* 文字列をコンパイルして標準出力に表示する (caml2html: main_string) *)

let file f = (* ファイルをコンパイルしてファイルに出力する (caml2html: main_file) *)
  let inchan = open_in (f ^ ".ml") in
  let outchan = open_out (f ^ !extension) in
  let buf = (Lexing.from_channel inchan) in
  try
    lexbuf outchan buf;
    close_in inchan;
    close_out outchan
  with e -> (close_in inchan; close_out outchan; raise e)

let () = (* ここからコンパイラの実行が開始される (caml2html: main_entry) *)
  let files = ref [] in
  Arg.parse
    [("-inline", Arg.Int(fun i -> Inline.threshold := i), "maximum size of functions inlined");
     ("-iter", Arg.Int(fun i -> limit := i), "maximum number of optimizations iterated");
     ("-debug",Arg.Unit(fun _->debug:=true),"print debug message");
     ("-fdiv",Arg.Unit(fun _->fdiv:=true),"handle fdiv as fdiv");
     ("-finv",Arg.String(fun i->match i with
				|"s"->finv_software := true
				|"h"->finv_software := false),"handle finv by software or hardware");
     ("-test",Arg.Unit(fun _->extension:="_test"),"make program_test");
     ("-c",Arg.Unit(fun _->coloring:=true),"register coloring")]
    (fun s -> files := !files @ [s])
    ("censored Min-Caml Compiler\n" ^
     Printf.sprintf "usage: %s [-inline m] [-iter n] [-debug] [-test] [-fdiv] [-finv s] [-c] ...filenames without \".ml\"..." Sys.argv.(0));
  List.iter
    (fun f -> ignore (file f))
    !files
