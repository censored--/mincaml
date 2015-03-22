type t = (* MinCamlの構文を表現するデータ型 (caml2html: syntax_t) *)
  | Unit
  | Bool of bool * int
  | Int of int * int
  | Float of float * int
  | Not of t * int
  | Neg of t * int
  | Add of t * t * int
  | Sub of t * t * int
  | Mul of t * t * int
  | Div of t * t * int
  | Lsl of t * t * int
  | Lsr of t * t * int
  | Asr of t * t * int
  | FNeg of t * int
  | FAdd of t * t * int
  | FSub of t * t * int
  | FMul of t * t * int
  | FDiv of t * t * int
  | FInv of t * int
  | Eq of t * t * int
  | LE of t * t * int
  | If of t * t * t * int
  | Let of (Id.t * Type.t) * t * t * int
  | Var of Id.t * int
  | LetRec of fundef * t * int
  | App of t * t list * int
  | Tuple of t list * int
  | LetTuple of (Id.t * Type.t) list * t * t * int
  | Array of t * t * int
  | Get of t * t * int
  | Put of t * t * t * int
and fundef = { name : Id.t * Type.t; args : (Id.t * Type.t) list; body : t }

let rec pp_t fmt = function
  | Unit -> Format.fprintf fmt "()"
  | Bool(b,_)-> Format.fprintf fmt "(%b:bool)" b
  | Int(i,_)-> Format.fprintf fmt "(%d:int)" i
  | Float(f,_)->Format.fprintf fmt "(%f:float)" f
  | Not(x,_)->Format.fprintf fmt "not(%a)" pp_t x
  | Neg(x,_)->Format.fprintf fmt "(-%a)" pp_t x
  | Add(x,y,_)->Format.fprintf fmt "(%a + %a)" pp_t x pp_t y
  | Sub(x,y,_)->Format.fprintf fmt "(%a - %a)" pp_t x pp_t y
  | Mul(x,y,_)->Format.fprintf fmt "(%a * %a)" pp_t x pp_t y
  | Div(x,y,_)->Format.fprintf fmt "(%a / %a)" pp_t x pp_t y
  | Lsl(x,y,_)->Format.fprintf fmt "(%a lsl %a)" pp_t x pp_t y
  | Lsr(x,y,_)->Format.fprintf fmt "(%a lsr %a)" pp_t x pp_t y
  | Asr(x,y,_)->Format.fprintf fmt "(%a asr %a)" pp_t x pp_t y
  | FNeg(x,_)->Format.fprintf fmt "(-.%a)" pp_t x
  | FInv(x,_)->Format.fprintf fmt "(1.0/.%a)" pp_t x
  | FAdd(x,y,_)->Format.fprintf fmt "(%a +.%a)" pp_t x pp_t y
  | FSub(x,y,_)->Format.fprintf fmt "(%a -.%a)" pp_t x pp_t y
  | FMul(x,y,_)->Format.fprintf fmt "(%a *.%a)" pp_t x pp_t y
  | FDiv(x,y,_)->Format.fprintf fmt "(%a /.%a)" pp_t x pp_t y
  | Eq(x,y,_)->Format.fprintf fmt "(%a==%a)" pp_t x pp_t y
  | LE(x,y,_)->Format.fprintf fmt "(%a<=%a)" pp_t x pp_t y
  | If(x,y,z,_)->Format.fprintf fmt "if %a @\n\t  then\t%a@\n\t  else\t%a" pp_t x pp_t y pp_t z
  | Let((x,y),z,w,_)->Format.fprintf fmt "let (%a:%a) = @\n\t  %a@\n\tin@\n\t  %a" Id.pp x Type.pp y pp_t z pp_t w
  | Var(x,_)->Format.fprintf fmt "(%a:var)" Id.pp x
  | LetRec(x,y,_)->Format.fprintf fmt "(let rec %a @\n\tin@\n\t  %a)" pp_f x pp_t y
  | App(x,y,_)->Format.fprintf fmt "(%a %a)" pp_t x (pp_l " ") y
  | Tuple(x,_)->Format.fprintf fmt " (%a) " (pp_l ",") x
  | LetTuple(x,y,z,_)->Format.fprintf fmt "let (%a) = @\n\t  %a@\n\tin@\n\t  %a" pp_arg x pp_t y pp_t z
  | Array(x,y,_)->Format.fprintf fmt "(Array.create %a %a)" pp_t x pp_t y
  | Get(x,y,_)->Format.fprintf fmt "%a.(%a)" pp_t x pp_t y
  | Put(x,y,z,_)->Format.fprintf fmt "(%a.(%a)<-%a)" pp_t x pp_t y pp_t z
and pp_l c fmt = function
  |[]->()
  |[x]->Format.fprintf fmt "%a" pp_t x
  |x::xs->Format.fprintf fmt "%a%s%a" pp_t x c (pp_l c) xs
and pp_p c f g fmt = function
  |[]->()
  |[(x,y)]->Format.fprintf fmt "(%a%s%a)" f x c g y
  |(x1,x2)::xs->Format.fprintf fmt "(%a%s%a) %a" f x1 c g x2 (pp_p c f g) xs
and pp_arg fmt = function
  |[]->()
  |[(x,y)]->Format.fprintf fmt "(%a:%a)" Id.pp x Type.pp y
  |(x1,x2)::xs->Format.fprintf fmt "(%a:%a) %a" Id.pp x1 Type.pp x2 pp_arg xs
and pp_f fmt {name=(x,y); args=z; body=w} =
  Format.fprintf fmt "(%a %a):%a =@\n\t  %a" Id.pp x pp_arg z Type.pp y pp_t w

let p e = Format.fprintf Format.err_formatter "Syntax:@.%a@." pp_t e 


