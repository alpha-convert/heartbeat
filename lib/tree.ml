type 'a t = Empty | Node of int * 'a * 'a t * 'a t

let size = function
    | Empty -> 0
    | Node (s,_,_,_) -> s
let empty = Empty
let node x l r = Node (1 + size l + size r,x,l,r)

let view t =
    match t with
    | Empty -> None
    | Node (_,x,l,r) -> Some (x,l,r)
