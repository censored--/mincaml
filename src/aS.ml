module AS = Set.Make(struct
		      type t = Id.t * Id.t
		      let compare = (fun (x1,y1) (x2,y2)->
				     if compare x1 x2 <> 0 then compare x1 x2
				     else compare y1 y2)
		    end)
include AS
let of_list l = List.fold_left (fun s e -> AS.add e s) AS.empty l

let to_string x =
  let x' = elements x in
  let rec t_s x = match x with
    |(x1,x2)::xx::xs->"("^x1^","^x2^");"^t_s (xx::xs)
    |(x1,x2)::xs->"("^x1^","^x2^")"
    |[]->"" in
  "["^t_s x'^"]"
