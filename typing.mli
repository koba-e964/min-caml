exception Error of Syntax.t * Syntax.t * Type.t * Type.t
val extenv : Type.t M.t ref
val f : Syntax.t -> bool -> Syntax.t
val f_withtype : Syntax.t -> bool -> Syntax.t * Type.t

