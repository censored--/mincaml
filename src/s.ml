(* customized version of Set *)

module S =
  Set.Make
    (struct
      type t = Id.t
      let compare = compare
    end)
include S

let of_list l = List.fold_left (fun s e -> add e s) empty l

let to_string set = let set_l = elements set in
		    let rec loop = function
		      |x::xs::xt->x^";"^loop (xs::xt)
		      |x::xs->x
		      |[]->"" in
		    "["^loop set_l^"]"

let findwith x env = if S.mem x env then S.find x env else (Format.eprintf "Not found %s in a Set@." x; raise Not_found)
let findwith x env msg = if S.mem x env then S.find x env else (Format.eprintf "Not found %s in a Set\n%s@." x msg; raise Not_found)
