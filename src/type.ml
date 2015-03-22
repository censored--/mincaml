
type t = (* MinCamlの型を表現するデータ型 (caml2html: type_t) *)
  | Unit
  | Bool of int
  | Int of int
  | Float of int
  | Fun of t list * t * int (* arguments are uncurried *)
  | Tuple of t list * int
  | Array of t * int
  | Var of t option ref * int

let line = function
  | Unit->(-1)
  | Bool i->i
  | Int i->i
  | Float i->i
  | Fun(_,_,i)->i
  | Tuple(_,i)->i
  | Array(_,i)->i
  | Var(_,i)->i


let gentyp n = Var((ref None),n) (* 新しい型変数を作る *)

let rec pp_t_list c fmt = function
  |[]->()
  |[x]-> pp fmt x
  |x::xs-> Format.fprintf fmt "%a%s%a" pp x c (pp_t_list c) xs

and pp fmt = function
  | Unit -> Format.fprintf fmt "unit"
  | Bool _ -> Format.fprintf fmt "bool"
  | Int _-> Format.fprintf fmt "int"
  | Float _-> Format.fprintf fmt "float"
  | Fun (x,y,_) -> Format.fprintf fmt "(%a->%a)" (pp_t_list "->") x pp y
  | Tuple (x,_)-> Format.fprintf fmt "(%a)" (pp_t_list ",") x
  | Array (x,_)-> Format.fprintf fmt "array %a" pp x
  | Var (t,_)-> Format.fprintf fmt "Var%a" pp_opt !t

and pp_opt fmt = function
  |None-> Format.fprintf fmt "(Undef)"
  |Some x->Format.fprintf fmt "(%a)" pp x
and print x = 
  Format.fprintf Format.err_formatter "%a@." pp x
