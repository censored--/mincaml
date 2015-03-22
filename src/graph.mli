type node = string
module Vertex : Set.S
module Edge : Set.S

type vertex = Vertex.t
type edge = Edge.t
type t = {vertex:vertex; edge:edge}

val fprintf : Format.formatter -> t -> unit
val printf : t -> unit
val eprintf : t -> unit

val empty : t

val add_edge : node * node -> t -> t
val add_undir_edge : node * node -> t -> t
val add_node : node -> t -> t

val add_clique : node list -> t -> t

val remove_edge : node * node -> t -> t
val remove_undir_edge : node * node -> t -> t
val remove_node : node -> t -> t

val mem_edge : node * node -> t -> bool
val mem_node : node -> t -> bool

val adjacent : node -> t -> vertex

val degree : node -> t -> int
val max_degree : t -> int

val elements : t -> node list * (node * node) list
