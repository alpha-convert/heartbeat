type t
[@@deriving show]

val empty : t
val node : int -> t -> t -> t
val size : t -> int

val view : t -> (int * t * t) option

val quickcheck_generator_t : t Core.Quickcheck.Generator.t