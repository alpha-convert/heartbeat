type 'a tree = Empty | Node of 'a * 'a tree * 'a tree

module type SUM = sig
    val sum : int tree -> int
end

(*
1. Normal Recursive tree sum.
*)
module Recursive : SUM = struct
    let rec sum t =
        match t with
        | Empty -> 0
        | Node (x,l,r) -> x + sum l + sum r
end

(*
2. CPS'd RecurAndAccumsive tree sum
*)

module CPS : SUM = struct
    let rec sum' t k =
        match t with
        | Empty -> k 0
        | Node (x,l,r) -> sum' l (fun sl -> sum' r (fun sr -> k (x + sl + sr)))
    let sum t = sum' t (fun x -> x)
end

(* 3 Defunctionalized CPS'd tree sum . *)
module CPSDefunc : SUM = struct
    type kont = Id
        | Recur of int tree * kont (* Accum (t,k) ~~ fun a -> k (a + sum x) *)
        | Accum of int * kont (* Accum (x,k) ~~ fun a -> k (a + x)*)
    let rec apply k a =
        match k with
        | Id -> a
        | Recur (t,k) -> sum' t (Accum (a,k))
        | Accum (x,k) -> apply k (x + a)
    and sum' t k =
        match t with
        | Empty -> apply k 0
        | Node (x,l,r) -> sum' l (Recur (r,Accum (x,k)))
    let sum t = sum' t Id
end


(*
4. Imperative, destination-passing continuation.
Sum' turns into a function int tree -> icont -> unit, which writes its result to the ref at the bottom.
*)

module ICPSDefunc : SUM = struct
    type kont = Store of int ref | Recur of int tree * kont | Accum of int * kont

    let rec apply k a =
        match k with
        | Store r -> r := a
        | Recur (t,k) -> sum' t (Accum (a,k))
        | Accum (x,k) -> apply k (x + a)
    and sum' t k =
        match t with
        | Empty -> apply k 0
        | Node (x,l,r) -> sum' l (Recur (r,(Accum (x,k))))
    let sum t = let r = ref 0 in sum' t (Store r); !r
end


(*
5. Tail-recursion-ify apply
*)

module TR_ICPS_Defunc : SUM = struct
    type kont = Store of int ref | Recur of int tree * kont | Accum of int * kont
    let rec apply k a =
        let k_ref = ref k in
        let a_ref = ref a in
        let quit = ref false in
        while not !quit do
            match !k_ref with
            | Store dst -> dst := !a_ref; quit := true
            | Recur (t,k) -> sum' t (Accum (!a_ref,k)); quit := true
            | Accum (x,k') -> a_ref := !a_ref + x; k_ref := k'
        done
    and sum' t k =
        match t with
        | Empty -> apply k 0
        | Node (x,l,r) -> sum' l (Recur (r,Accum (x,k)))

    let sum t = let r = ref 0 in sum' t (Store r); !r
end


(*
6. Inline apply into the definiton of sum'
*)
module Inlined_TR_ICPS_Defunc : SUM = struct
    type kont = Store of int ref | Recur of int tree * kont | Accum of int * kont
    let rec sum' t k =
        match t with
        | Empty ->
            let k_ref = ref k in
            let a_ref = ref 0 in
            let quit = ref false in
            while not !quit do
                match !k_ref with
                | Store dst -> dst := !a_ref; quit := true
                | Recur (t,k') -> sum' t (Accum (!a_ref,k')); quit := true
                | Accum (x,k') -> a_ref := !a_ref + x; k_ref := k'
            done
        | Node (x,l,r) -> sum' l (Recur (r,Accum (x,k)))

    let sum t = let r = ref 0 in sum' t (Store r); !r
end

(*7. compltely inlined and constant stack space. *)
module Complete : SUM = struct
    type kont = Store of int ref | Recur of int tree * kont | Accum of int * kont
    let rec sum' t k =
        let t = ref t in
        let k = ref k in
        let sum_quit = ref false in
        while not !sum_quit do
            match !t with
            | Empty ->
                let a_ref = ref 0 in
                let apply_quit = ref false in
                while not !apply_quit do
                    match !k with
                    | Store dst -> dst := !a_ref; apply_quit := true; sum_quit := true
                    | Recur (t',k') -> 
                        t := t';
                        k := Accum (!a_ref,k');
                        apply_quit := true
                    | Accum (x,k') -> a_ref := !a_ref + x; k := k'
                done
            | Node (x,l,r) ->
                t := l;
                k := Recur (r,Accum (x,!k))
        done
    let sum t = let r = ref 0 in sum' t (Store r); !r
end

module CompleteLiftAcc : SUM = struct
    type kont = Store of int ref | Recur of int tree * kont | Accum of int * kont
    let rec sum' t k =
        let t = ref t in
        let k = ref k in
        let acc = ref 0 in
        let sum_quit = ref false in
        while not !sum_quit do
            match !t with
            | Empty ->
                let apply_quit = ref false in
                while not !apply_quit do
                    match !k with
                    | Store dst -> dst := !acc ; apply_quit := true; sum_quit := true
                    | Recur (t',k') -> 
                        t := t';
                        k := k';
                        apply_quit := true
                    | Accum (x,k') -> acc := x + !acc; k := k'
                done
            | Node (x,l,r) ->
                t := l;
                k := Recur (r,Accum (x,!k))
        done
    let sum t = let r = ref 0 in sum' t (Store r); !r
end

module HeartbeatSum(Params : sig
    val heartbeat_rate : int
    val num_domains : int
end
) : SUM = struct

    module T = Domainslib.Task;;

    let pool = T.setup_pool ~num_domains:Params.num_domains ()

    let heartbeat =
        let beats = ref 0 in
        fun () ->
            if !beats == Params.heartbeat_rate then (beats := 0; true)
            else (incr beats; false)


    type kont = Store of int ref | Recur of int tree * kont | Accum of int * kont | Join of (unit T.promise)

    (* with uniquness this could be in-place. *)
    let [@tail_mod_cons] rec try_promote k =
        match k with
        | Store dst -> Store dst
        | Accum (n,k) -> Accum (n, try_promote k)
        | Recur (t,k) -> Join (T.async pool (fun () -> sum' t k))
        | Join p -> Join p

    and sum' t k =
        let t = ref t in
        let k = ref k in
        let sum_quit = ref false in
        while not !sum_quit do
            k := if heartbeat () then try_promote !k else !k;
            match !t with
            | Empty ->
                let a_ref = ref 0 in
                let apply_quit = ref false in
                while not !apply_quit do
                    k := if heartbeat () then try_promote !k else !k;
                    match !k with
                    | Store dst -> dst := !a_ref; apply_quit := true; sum_quit := true
                    | Recur (t',k') -> 
                        t := t';
                        k := Accum (!a_ref,k');
                        apply_quit := true
                    | Accum (x,k') -> a_ref := !a_ref + x; k := k'
                    | Join p -> T.await pool p; apply_quit := true; sum_quit := true
                done
            | Node (x,l,r) ->
                t := l;
                k := Recur (r,Accum (x,!k))
        done
    let sum t = T.run pool (fun () -> let r = ref 0 in sum' t (Store r); !r)
end

module ForkJoinSum(Params : sig val num_domains : int end) : SUM = struct
    module T = Domainslib.Task;;

    let pool = T.setup_pool ~num_domains:Params.num_domains ()

    let rec sum' t () =
        match t with
        | Empty -> 0
        | Node(x,l,r) ->
            let pl = T.async pool (sum' l) in
            let pr = T.async pool (sum' r) in
            let nl = T.await pool pl in
            let nr = T.await pool pr in
            x + nl + nr
    
    let sum t = T.run pool (sum' t)
end