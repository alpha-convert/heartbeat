type 'a t

val empty : 'a t
val node : 'a -> 'a t -> 'a t -> 'a t
val size : 'a t -> int

val view : 'a t -> ('a * 'a t * 'a t) option