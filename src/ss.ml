
module Ss =
  Set.Make
    (struct
      type t = Id.t * KNormal.t
      let compare = fun (x,y) (z,w) -> 
	if x > z then 1 else if x = z then 0 else -1
    end)
include Ss

let id_eq x = fun (y,_)-> if x = y then true else false
let kn_eq x = fun (_,y)-> if x = y then true else false

let id_delete x l = filter (fun y -> not (id_eq x y)) l
let kn_delete x l = filter (fun y -> not (kn_eq x y)) l
let id_exists x l = exists (id_eq x) l
let kn_exists x l = exists (kn_eq x) l

let id_find x l = min_elt (filter (id_eq x) l)
let kn_find x l =  min_elt (filter (kn_eq x) l)
