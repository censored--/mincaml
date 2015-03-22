{
(* lexerが利用する変数、関数、型などの定義 *)
open Myparser
open Type
}

(* 正規表現の略記 *)
let space = [' ' '\t' '\r']
let newline=['\n']
let digit = ['0'-'9']
let lower = ['a'-'z']
let upper = ['A'-'Z']


rule token = parse
| (space)+
    { token lexbuf }
| newline
    { Lexing.new_line lexbuf;
      token lexbuf}
| "(*"
    { comment lexbuf; (* ネストしたコメントのためのトリック *)
      token lexbuf }
| '('
    { LPAREN }
| ')'
    { RPAREN }
| "true"
    { BOOL(true) }
| "false"
    { BOOL(false) }
| "not"
    { NOT }
| digit+ (* 整数を字句解析するルール (caml2html: lexer_int) *)
    { INT(int_of_string (Lexing.lexeme lexbuf)) }
| digit+ ('.' digit*)? (['e' 'E'] ['+' '-']? digit+)?
    { FLOAT(float_of_string (Lexing.lexeme lexbuf)) }
| "fun"
    { FUN }
| '-' (* -.より後回しにしなくても良い? 最長一致? *)
    { MINUS }
| '+' (* +.より後回しにしなくても良い? 最長一致? *)
    { PLUS }
| '*'
    { AST }
| '/'
    { SLASH }
| "-."
    { MINUS_DOT }
| "+."
    { PLUS_DOT }
| "*."
    { AST_DOT }
| "/."
    { SLASH_DOT }
| '='
    { EQUAL }
| "<>"
    { LESS_GREATER }
| "<="
    { LESS_EQUAL }
| ">="
    { GREATER_EQUAL }
| "lsl"
    { LSL }
| "lsr"
    { LSR }
| "asr"
    { ASR }
| '<'
    { LESS }
| '>'
    { GREATER }
| "if"
    { IF }
| "then"
    { THEN }
| "else"
    { ELSE }
| "let"
    { LET }
| "in"
    { IN }
| "rec"
    { REC }
| ','
    { COMMA }
| '_'
    { IDENT(Id.gentmp Type.Unit) }
| "Array.create" (* [XX] ad hoc *)
    { ARRAY_CREATE }
| "create_array" (* [XX] ad hoc *)
    { ARRAY_CREATE }
| '.'
    { DOT }
| "->"
    { MINUS_GREATER }
| "<-"
    { LESS_MINUS }
| "fequal"
    { FEQUAL }
| "fless"
    { FLESS }
| "fneg"
    { MINUS_DOT }
| "fiszero"
    { FISZERO }
| "fispos"
    { FISPOS }
| "fisneg"
    { FISNEG }
| "fhalf"
    { FHALF }
| "fsqr"
    { FSQR }
| ';'
    { SEMICOLON }
| eof
    { EOF }
| lower (digit|lower|upper|'_')* (* 他の「予約語」より後でないといけない *)
    { IDENT(Lexing.lexeme lexbuf) }
| _
    { failwith
	(let {Lexing.pos_fname=_;Lexing.pos_lnum=sl;Lexing.pos_bol=sb;Lexing.pos_cnum=sc}=Lexing.lexeme_start_p lexbuf in
	 let {Lexing.pos_fname=_;Lexing.pos_lnum=el;Lexing.pos_bol=eb;Lexing.pos_cnum=ec}=Lexing.lexeme_end_p lexbuf in
	  Printf.sprintf "unknown token %s line:%d,%d-%d"
	   (Lexing.lexeme lexbuf)
	   sl (sc-sb) (ec-eb)) }
and comment = parse
| newline
    { Lexing.new_line lexbuf;
      comment lexbuf }
| "*)"
    { () }
| "(*"
    { comment lexbuf;
      comment lexbuf }
| eof
    { Format.eprintf "warning: unterminated comment@." }
| _
    { comment lexbuf }
