type t = Empty | Node of int * int * t * t

val empty : t
val node : int -> t -> t -> t
[@@inline]
val size : t -> int
[@@inline]

val view : t -> (int * t * t) option
[@@inline]

val quickcheck_generator_t : t Core.Quickcheck.Generator.t

val generate_balanced : t Core.Quickcheck.Generator.t
val generate_stringy : t Core.Quickcheck.Generator.t