(* customized version of Map *)

module M =
  Map.Make
    (struct
      type t = Id.t
      let compare = compare
    end)
include M

let add_list xys env = List.fold_left (fun env (x, y) -> add x y env) env xys
let add_list2 xs ys env = List.fold_left2 (fun env x y -> add x y env) env xs ys

let findwith x env msg = if M.mem x env then M.find x env else failwith ("Not found "^x^" in a Map\n"^msg)

let to_string x yfun =
  let x' = bindings x in
  let rec t_s x = match x with
    |(x,y)::xx::xs->"("^x^","^yfun y^"),"^t_s (xx::xs)
    |(x,y)::xs->"("^x^","^yfun y^")"
    |[]->"" in
  "["^t_s x'^"]"
