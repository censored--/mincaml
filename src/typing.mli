exception Error of int * int * unit * Type.t * Type.t
val extenv : Type.t M.t ref
val deref_typ : Type.t -> Type.t
val unify : Type.t -> Type.t -> unit
val f : Syntax.t -> Syntax.t
val p : Syntax.t->unit
