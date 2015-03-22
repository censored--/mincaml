type node = string
module Vertex = Set.Make
		  (struct
		    type t = string
		    let compare = compare
		  end)

module Edge = Set.Make
		  (struct
		    type t = string * string
		    let compare = compare
		  end)

type vertex = Vertex.t
type edge = Edge.t
type t = {vertex:vertex;edge: edge}

let string_of_vertex v =
  let vl = Vertex.elements v in
  let rec s_of_v = function
    |x::xx::xs->x^", "^s_of_v (xx::xs)
    |x::xs->x
    |_->"" in s_of_v vl

let string_of_edge e =
  let el = Edge.elements e in
  let rec s_of_e = function
    |(x,y)::xx::xs->"("^x^","^y^"), "^s_of_e (xx::xs)
    |(x,y)::xs->"("^x^","^y^")"
    |_->"" in s_of_e el

let fprintf fmt {vertex=v;edge=e} =
  Format.fprintf fmt "[vertex]\n%s\n[edges]\n%s@." (string_of_vertex v) (string_of_edge e)
let printf x = fprintf Format.std_formatter x
let eprintf x = fprintf Format.err_formatter x


let empty = {vertex = Vertex.empty; edge = Edge.empty}

let add_edge (a,b) {vertex=v;edge=e} = {vertex = v;edge = Edge.add (a,b) e}

let add_undir_edge (a,b) {vertex=v;edge=e} = {vertex = v; edge = Edge.add (b,a) (Edge.add (a,b) e)}

let add_node x {vertex=v;edge=e} = {vertex = Vertex.add x v;edge = e}

let add_clique c {vertex=v;edge=e} =
  let  rec add_c cx cs {vertex=v;edge=e} = 
    let graph = add_node cx (List.fold_left 
			       (fun graph c-> if cx != c then add_undir_edge (cx, c) graph else graph) 
			       {vertex=v;edge=e} c) in
    match cs with 
    |dx::ds-> add_c dx ds graph 
    |[]-> graph in
  match c with
  |[]-> {vertex=v;edge=e}
  |cx::cs->add_c cx cs {vertex=v;edge=e}

let remove_edge (a,b) {vertex=v;edge=e} = {vertex = v; edge = Edge.remove (a,b) e}

let remove_undir_edge (a,b) {vertex=v;edge=e} = {vertex = v; edge = Edge.remove (b,a) (Edge.remove (a,b) e)}

(*頂点 xとx を端点に持つ辺をグラフから削除する*)
let remove_node x {vertex=v;edge=e} =
  {vertex = Vertex.remove x v; edge = Edge.filter (fun (a,b)->x <> a&&x <> b) e}

let mem_edge x {vertex=v;edge=e} = Edge.mem x e

let mem_node x {vertex=v;edge=e} = Vertex.mem x v

let adjacent x {vertex = v; edge = e} = Vertex.filter (fun a-> Edge.mem (x,a) e) v

let degree x {vertex=v;edge=e} = Vertex.cardinal (adjacent x {vertex=v;edge=e})

let max_degree {vertex=v;edge=e} =
  Vertex.fold 
    (fun x max-> let degx = degree x {vertex=v;edge=e} in
     if degx > max then degx else max) v 0


let elements g = (Vertex.elements g.vertex, Edge.elements g.edge)
