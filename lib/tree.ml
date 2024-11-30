type t = Empty | Node of int * int * t * t
[@@deriving show]

let size = function
    | Empty -> 0
    | Node (s,_,_,_) -> s
let empty = Empty
let node x l r = Node (1 + size l + size r,x,l,r)

let view t =
    match t with
    | Empty -> None
    | Node (_,x,l,r) -> Some (x,l,r)

let quickcheck_generator_t =
    let open Base_quickcheck.Generator in
    let open Let_syntax in
    recursive_union [return empty] ~f:(
        fun g ->  [
            let%bind l = g in
            let%bind r = g in
            let%bind x = Base_quickcheck.Generator.small_positive_or_zero_int in
            return (node x l r)
        ]
    )