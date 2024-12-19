type t = Empty | Node of int * int * t * t
[@@deriving show]

let view t  =
    match t with
    | Empty -> None
    | Node (_,x,l,r) -> Some (x,l,r)
[@@inline]

let size = function
    | Empty -> 0
    | Node (s,_,_,_) -> s
[@@inline]
let empty = Empty
let node x l r = Node (1 + size l + size r,x,l,r)
[@@inline]


(* TODO: i think this only returns totally balacned trees, oops. *)
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
let generate_balanced =
    let open Core.Quickcheck.Generator in
    let open Core.Quickcheck.Let_syntax in
    fixed_point (fun gt ->
        let%bind n = size in
        if n == 0 then return empty else
        let%bind l = with_size ~size:(n-1) gt in
        let%bind r = with_size ~size:(n-1) gt in
        let%bind x = small_non_negative_int in
        return (node x l r)
    )

let generate_stringy =
    let open Core.Quickcheck.Generator in
    let open Core.Quickcheck.Let_syntax in
    fixed_point (fun self ->
        let%bind n = size in
        if n == 0 then return empty else
        let%bind t = with_size ~size:(n-1) self in
        let%bind x = small_non_negative_int in
        weighted_union [
            (1.0,return (node x t empty));
            (1.0,return (node x empty t));
        ]
    )