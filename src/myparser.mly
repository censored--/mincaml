%{
(* parserが利用する変数、関数、型などの定義 *)
open Syntax
let line ()=(let {Lexing.pos_lnum=l}=Parsing.symbol_start_pos () in l)
let addtyp x = (x, Type.gentyp (line()))
let fun_id = ref 0
let make_fid () =  fun_id :=!fun_id+1;
		  "_lambda_"^string_of_int (!fun_id)

%}

/* 字句を表すデータ型の定義 (caml2html: parser_token) */
%token <bool> BOOL
%token <int> INT
%token <float> FLOAT
%token  NOT
%token  FUN
%token  MINUS
%token  PLUS
%token  AST
%token  SLASH
%token  MINUS_DOT
%token  PLUS_DOT
%token  AST_DOT
%token  SLASH_DOT
%token  EQUAL
%token  LESS_GREATER
%token  LESS_EQUAL
%token  GREATER_EQUAL
%token  LESS
%token  GREATER
%token  LSL
%token  LSR
%token  ASR
%token  IF
%token  THEN
%token  ELSE
%token <Id.t> IDENT
%token  LET
%token  IN
%token  REC
%token  COMMA
%token  ARRAY_CREATE
%token  DOT
%token  MINUS_GREATER
%token  LESS_MINUS
%token  FEQUAL
%token  FLESS
%token  FISPOS
%token  FISNEG
%token  FISZERO
%token  FHALF
%token  FSQR
%token  FABS
%token  SEMICOLON
%token  LPAREN
%token  RPAREN
%token  EOF

/* 優先順位とassociativityの定義（低い方から高い方へ） (caml2html: parser_prior) */
%right prec_let
%right SEMICOLON
%right prec_if
%right LESS_MINUS
%left COMMA
%left EQUAL LESS_GREATER LESS GREATER LESS_EQUAL GREATER_EQUAL
%left LSL LSR ASR
%left PLUS MINUS PLUS_DOT MINUS_DOT
%left AST_DOT SLASH_DOT AST SLASH
%right prec_unary_minus
%left prec_app
%left DOT

/* 開始記号の定義 */
%type <Syntax.t> exp
%start exp
%%

simple_exp: /* 括弧をつけなくても関数の引数になれる式 (caml2html: parser_simple) */
| LPAREN exp RPAREN
    { $2 }
| LPAREN RPAREN
    { Unit }
| BOOL
    { Bool($1,line()) }
| INT
    { Int($1,line()) }
| FLOAT
    { Float($1,line()) }
| IDENT
    { Var($1,line()) }
| simple_exp DOT LPAREN exp RPAREN
    { Get($1, $4,line()) }

exp: /* 一般の式 (caml2html: parser_exp) */
| simple_exp
    { $1 }
| NOT exp
    %prec prec_app
    { Not($2,line()) }
| MINUS exp
    %prec prec_unary_minus
    { match $2 with
    | Float(f,l) -> Float(-.f,l) (* -1.23などは型エラーではないので別扱い *)
    | e -> Neg(e,line()) }
| exp PLUS exp /* 足し算を構文解析するルール (caml2html: parser_add) */
    { Add($1, $3,line()) }
| exp MINUS exp
    { Sub($1, $3,line()) }
| exp AST exp 
    { Mul($1, $3,line()) }
| exp SLASH exp
    { Div($1, $3,line()) }
| exp EQUAL exp
    { Eq($1, $3,line()) }
| exp LESS_GREATER exp
    { Not(Eq($1, $3,line()),line()) }
| exp LESS exp
    { Not(LE($3, $1,line()),line()) }
| exp GREATER exp
    { Not(LE($1, $3,line()),line()) }
| exp LSL exp
    { Lsl($3, $1,line()) }
| exp LSR exp
    { Lsr($1, $3,line()) }
| exp ASR exp
    { Asr($1, $3,line()) }
| exp LESS_EQUAL exp
    { LE($1, $3,line()) }
| exp GREATER_EQUAL exp
    { LE($3, $1,line()) }
| IF exp THEN exp ELSE exp
    %prec prec_if
    { If($2, $4, $6,line()) }
| MINUS_DOT exp
    %prec prec_unary_minus
    { FNeg($2,line()) }
| exp PLUS_DOT exp
    { FAdd($1, $3,line()) }
| exp MINUS_DOT exp
    { FSub($1, $3,line()) }
| exp AST_DOT exp
    { FMul($1, $3,line()) }
| exp SLASH_DOT exp
    { FDiv($1,$3,line()) }
| LET IDENT EQUAL exp IN exp
    %prec prec_let
    { Let(addtyp $2, $4, $6,line()) }
| LET REC fundef IN exp
    %prec prec_let
    { LetRec($3, $5,line()) }
| funexp exp
    %prec prec_let
    { let fid = make_fid () in 
      LetRec({ name = (addtyp fid); args = $1;
	       body = $2 }, Var(fid,line()), line()) }
| exp actual_args
    %prec prec_app
    { App($1, $2,line()) }
| elems
    { Tuple($1,line()) }
| LET LPAREN pat RPAREN EQUAL exp IN exp
    { LetTuple($3, $6, $8,line()) }
| simple_exp DOT LPAREN exp RPAREN LESS_MINUS exp
    { Put($1, $4, $7,line()) }
| exp SEMICOLON exp
    { Let((Id.gentmp Type.Unit, Type.Unit), $1, $3,line()) }
| FEQUAL simple_exp simple_exp
    %prec prec_app
    { Eq($2, $3,line()) }
| FLESS simple_exp simple_exp
    %prec prec_app
    { Not(LE($3, $2,line()),line()) }
| FISZERO simple_exp
    %prec prec_app
    { Eq($2, Float(0.0,line()),line()) }
| FISPOS simple_exp
    %prec prec_app
    { Not(LE($2, Float(0.0,line()) ,line()),line()) }
| FISNEG simple_exp
    %prec prec_app
    { Not(LE(Float(0.0,line()), $2, line()),line()) }
| FHALF simple_exp
    %prec prec_app
    { FMul(Float(0.5, line()), $2, line()) }
| FSQR simple_exp
    %prec prec_app
    { FMul($2, $2,line()) }    
| ARRAY_CREATE simple_exp simple_exp
    %prec prec_app
    { Array($2, $3,line()) }
| error
    { failwith
      (let {Lexing.pos_fname=sn;Lexing.pos_lnum=sl;Lexing.pos_bol=sb;Lexing.pos_cnum=sc}
	=(Parsing.symbol_start_pos ()) in
	  let {Lexing.pos_fname=en;Lexing.pos_lnum=el;Lexing.pos_bol=eb;Lexing.pos_cnum=ec}
	= (Parsing.symbol_end_pos ()) in
	  (Printf.sprintf "parse error near characters (%d,%d)-(%d,%d)" sl (sc-sb) el (ec-eb))) }

funexp:
| funexp FUN formal_args MINUS_GREATER
    { $1@$3 }
| FUN formal_args MINUS_GREATER
    { $2 }

fundef:
| IDENT formal_args EQUAL exp
    { { name = addtyp $1; args = $2; body = $4 } }
formal_args:
| IDENT formal_args
    { addtyp $1 :: $2 }
| IDENT
    { [addtyp $1] }

actual_args:
| actual_args simple_exp
    %prec prec_app
    { $1 @ [$2] }
| simple_exp
    %prec prec_app
    { [$1] }

elems:
| elems COMMA exp
    { $1 @ [$3] }
| exp COMMA exp
    { [$1; $3] }

pat:
| pat COMMA IDENT
    {  $1 @ [addtyp $3] }
| IDENT COMMA IDENT
    { [addtyp $1; addtyp $3] }
