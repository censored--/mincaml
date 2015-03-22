type t = string (* 変数の名前 (caml2html: id_t) *)
type l = L of string (* トップレベル関数やグローバル配列のラベル (caml2html: id_l) *)

let pp fmt x = Format.fprintf fmt "%s" x 

let print x = Format.fprintf Format.err_formatter "%a" pp x

let rec p_list fmt = function
  |[]->()
  |[x]->pp fmt x
  |x::xs->Format.fprintf fmt "%a;%a" pp x p_list xs

let t_list_to_string x =
  let rec t_l_t_s = function
    |t::tx::ts->t^";"^t_l_t_s (tx::ts)
    |t::ts->t
    |[]->"" in
  "["^t_l_t_s x^"]"


let string_L = function
  |L x-> x

let pp_l fmt x = Format.fprintf fmt "%s" (string_L x)

let rec pp_list = function
  | [] -> ""
  | [x] -> x
  | x :: xs -> x ^ " " ^ pp_list xs

let counter = ref 0
let genid s =
  incr counter;
  Printf.sprintf "%s_%d" s !counter

let rec id_of_typ = function
  | Type.Unit -> "u"
  | Type.Bool _ -> "b"
  | Type.Int _-> "i"
  | Type.Float _-> "d"
  | Type.Fun _ -> "f"
  | Type.Tuple _ -> "t"
  | Type.Array _ -> "a" 
  | Type.Var _ -> assert false
let gentmp typ =
  incr counter;
  Printf.sprintf "T%s%d" (id_of_typ typ) !counter
