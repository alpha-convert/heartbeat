module type SUM = sig
    val sum : Tree.t -> int [@@zero_alloc]
end

module T = Domainslib.Task;;

(*
VERSION 1
*)

(*
1. Normal Recursive tree sum.
*)
module Recursive : SUM = struct
    let rec sum t =
        match Tree.view t with
        | None -> 0
        | Some (x,l,r) -> x + sum l + sum r
end

module RecursiveAccRef : SUM = struct
    let sum t =
        let acc = ref 0 in
        let rec go t =
            match t with
            | Tree.Empty -> ()
            | Tree.Node(_,x,l,r) ->
                acc := !acc + x;
                go l;
                go r
            in
        go t; !acc
end



module RecursiveLeak : SUM = struct
    let rec sum t =
        match t with
        | Tree.Empty -> 0
        | Tree.Node (_,x,l,r) -> x + sum l + sum r
end


module ExplicitStack : SUM = struct
    let go t =
        let acc = ref 0 in
        let quit = ref false in
        let stk = Core.Stack.create () in
        while not !quit do
            match !t with
            | Tree.Empty -> (
                match Core.Stack.pop stk with
                | None -> quit := true
                | Some rt' -> t := !rt'
            )
            | Tree.Node (_,x,l,r) -> acc := !acc + x; t := l; Core.Stack.push stk (ref r); ()
        done;
        !acc

    let sum t = go (ref t)
end

module ExplicitStackList : SUM = struct
    let go t =
        let acc = ref 0 in
        let quit = ref false in
        let stk = ref [] in
        while not !quit do
            match !t with
            | Tree.Empty -> (
                match !stk with
                | [] -> quit := true
                | rt' :: stk' -> t := rt'; stk := stk'
            )
            | Tree.Node (_,x,l,r) -> acc := !acc + x; t := l; stk := r :: !stk; ()
        done;
        !acc

    let sum t = go (ref t)
end


(*
2. CPS'd RecurAndAccumsive tree sum
*)

module CPS : SUM = struct
    let rec sum' t k =
        match t with
        | Tree.Empty -> k 0
        | Tree.Node (_,x,l,r) -> sum' l (fun sl -> sum' r (fun sr -> k (x + sl + sr)))
    let sum t = sum' t (fun x -> x)
end

(* 3 Defunctionalized CPS'd tree sum . *)
module CPSDefunc : SUM = struct
    type kont = Id
        | Recur of Tree.t * kont (* Accum (t,k) ~~ fun a -> k (a + sum x) *)
        | Accum of int * kont (* Accum (x,k) ~~ fun a -> k (a + x)*)
    let rec apply k a =
        match k with
        | Id -> a
        | Recur (t,k) -> sum' t (Accum (a,k))
        | Accum (x,k) -> apply k (x + a)
    and sum' t k =
        match t with
        | Tree.Empty -> apply k 0
        | Node(_,x,l,r) -> sum' l (Recur (r,Accum (x,k)))
    let sum t = sum' t Id
end


(*
4. Imperative, destination-passing continuation.
Sum' turns into a function int tree -> icont -> unit, which writes its result to the ref at the bottom.
*)

module ICPSDefunc : SUM = struct
    type kont = Store of int ref | Recur of Tree.t * kont | Accum of int * kont

    let rec apply k a =
        match k with
        | Store r -> r := a
        | Recur (t,k) -> sum' t (Accum (a,k))
        | Accum (x,k) -> apply k (x + a)
    and sum' t k =
        match t with
        | Empty -> apply k 0
        | Node(_,x,l,r) -> sum' l (Recur (r,(Accum (x,k))))
    let sum t = let r = ref 0 in sum' t (Store r); !r
end


(*
5. Tail-recursion-ify apply
*)

module TR_ICPS_Defunc : SUM = struct
    type kont = Store of int ref | Recur of Tree.t * kont | Accum of int * kont
    let rec apply k a =
        let k_ref = ref k in
        let acc = ref a in
        let quit = ref false in
        while not !quit do
            match !k_ref with
            | Store dst -> dst := !acc; quit := true
            | Recur (t,k) -> sum' t (Accum (!acc,k)); quit := true
            | Accum (x,k') -> acc := !acc + x; k_ref := k'
        done
    and sum' t k =
        match t with
        | Empty -> apply k 0
        | Node (_,x,l,r) -> sum' l (Recur (r,Accum (x,k)))

    let sum t = let r = ref 0 in sum' t (Store r); !r
end


(*
6. Inline apply into the definiton of sum'
*)
module Inlined_TR_ICPS_Defunc : SUM = struct
    type kont = Store of int ref | Recur of Tree.t * kont | Accum of int * kont
    let rec sum' t k =
        match t with
        | Tree.Empty ->
            let k_ref = ref k in
            let acc = ref 0 in
            let quit = ref false in
            while not !quit do
                match !k_ref with
                | Store dst -> dst := !acc; quit := true
                | Recur (t,k') -> sum' t (Accum (!acc,k')); quit := true
                | Accum (x,k') -> acc := !acc + x; k_ref := k'
            done
        | Node(_,x,l,r) -> sum' l (Recur (r,Accum (x,k)))

    let sum t = let r = ref 0 in sum' t (Store r); !r
end

(*7. compltely inlined and constant stack space. *)
module Complete : SUM = struct
    type kont = Store of int ref | Recur of Tree.t * kont | Accum of int * kont
    let sum' t k =
        let t = ref t in
        let k = ref k in
        let sum_quit = ref false in
        while not !sum_quit do
            match !t with
            | Tree.Empty ->
                let acc = ref 0 in
                let apply_quit = ref false in
                while not !apply_quit do
                    match !k with
                    | Store dst -> dst := !acc; apply_quit := true; sum_quit := true
                    | Recur (t',k') -> 
                        t := t';
                        k := Accum (!acc,k');
                        apply_quit := true
                    | Accum (x,k') -> acc := !acc + x; k := k'
                done
            | Node (_,x,l,r) ->
                t := l;
                k := Recur (r,Accum (x,!k))
        done
    let sum t = let r = ref 0 in sum' t (Store r); !r
end

module CompleteLiftAcc : SUM = struct
    type kont = Store of int ref | Recur of Tree.t * kont
    let sum' t k =
        let t = ref t in
        let k = ref k in
        let acc = ref 0 in
        let sum_quit = ref false in
        while not !sum_quit do
            match !t with
            | Tree.Empty ->
                (match !k with
                 | Store dst -> dst := !acc ; sum_quit := true
                 | Recur (t',k') -> t := t'; k := k')
            | Node (_,x,l,r) ->
                t := l;
                acc := x + !acc;
                k := Recur (r,!k)
        done
    let sum t = let r = ref 0 in sum' t (Store r); !r
end

module CompleteLiftAccRegion (Params : sig
  val region : Tree.t Core.Uniform_array.t
end) : SUM = struct

    let sum' t dst =
        let i = ref 0 in
        let t = ref t in
        let acc = ref 0 in
        let sum_quit = ref false in
        while not !sum_quit do
            match !t with
            | Tree.Empty ->
                (if !i == 0 then (dst := !acc ; sum_quit := true)
                else
                    let t' = Core.Uniform_array.unsafe_get Params.region !i in
                    t := t'; decr i)
            | Node (_,x,l,r) ->
                t := l;
                acc := x + !acc;
                incr i;
                Core.Uniform_array.unsafe_set_omit_phys_equal_check Params.region !i r;
        done
    let sum t = let r = ref 0 in
                Core.Uniform_array.set Params.region 0 t;
                sum' t r; !r
end


module HeartbeatSum(Params : sig
    val heartbeat_rate : int
    val pool : T.pool ref
end
) : SUM
= struct

    type kontframe_type =
    | Recur of Tree.t
    | Accum of int
    | Join of (int ref) * (unit T.promise)
    
    type kontframe = {
        mutable frame_type : kontframe_type;
        next : [`Nil of int ref | `Box of kontframe]
    }

    (* a continuation is (a) a linked list of frames, just like before, and
     (b) a deque of pointers to Recur frames. The front of the queue is the youngest stack frame, most recently pushed.
       the rear of the queue is the oldest stack frame, the closest to being promoted.
    *)
    type kont = {
        (* front is young, back is old. *)
        promotable_dq : (kontframe ref) Core.Deque.t;
        mutable frames : [`Nil of int ref | `Box of kontframe]
    }

    let init_kont r = {promotable_dq = Core.Deque.create ~initial_length:100 () ;frames = `Nil r}

    exception BrokenInvariant of string

    let rec try_promote k =
        match Core.Deque.dequeue_back k.promotable_dq with
        | None -> ()
        | Some kf ->
            match !kf.frame_type with
            | Recur t ->
                let r = ref 0 in
                let p = T.async !Params.pool (fun () -> sum' (ref t) (init_kont r) (ref 0)) in
                !kf.frame_type <- Join (r,p)
            | _ -> raise (BrokenInvariant "Oldest stack frame is not a recur.")

    and sum' t (k : kont) beats =
        let heartbeat () =
            if !beats >= Params.heartbeat_rate then (beats := 0; true)
            else (incr beats; false)
        in
        let sum_quit = ref false in
        while not !sum_quit do
            (* at the start of each iteration, promote the oldest Recursive *)
            if heartbeat () then try_promote k else ();
            match !t with
            | Tree.Empty ->
                let acc = ref 0 in
                let apply_quit = ref false in
                while not !apply_quit do
                    if heartbeat () then try_promote k else ();
                    match k.frames with
                    | `Nil dst -> dst := !acc; apply_quit := true; sum_quit := true
                    | `Box frame ->  (
                        match frame.frame_type with
                        | Recur t' ->
                            t := t';
                            k.frames <- `Box {frame_type = Accum !acc; next = frame.next};
                            apply_quit := true;
                            ignore (Core.Deque.dequeue_front_exn k.promotable_dq)
                        | Accum x ->
                            acc := !acc + x;
                            k.frames <- frame.next
                        | Join (r,p) ->
                            T.await !Params.pool p;
                            k.frames <- `Box {frame_type = Accum !r; next = frame.next}
                    )
                done
            | Node (_,x,l,r) ->
                t := l;
                let kf_accum = {frame_type = Accum x; next = k.frames} in
                let kf_recur = {frame_type = Recur r; next = `Box kf_accum} in
                Core.Deque.enqueue_front k.promotable_dq (ref kf_recur);
                k.frames <- `Box kf_recur
        done
    let sum t = T.run !Params.pool (fun () -> let r = ref 0 in sum' (ref t) (init_kont r) (ref 0); !r)
end

module HeartbeatSumUopt (Params : sig
    val heartbeat_rate : int
    val pool : T.pool ref
end
) : SUM
= struct

    type kontframe_type = Recur of Tree.t | Accum of int | Join of int ref * unit T.promise

    type kontframe = {
        mutable frame_type : kontframe_type;
        next : kontframe Uopt.t;
    }

    (* a continuation is (a) a linked list of frames, just like before, and
     (b) a deque of pointers to Recur frames. The front of the queue is the youngest stack frame, most recently pushed.
       the rear of the queue is the oldest stack frame, the closest to being promoted.
    *)
    type kont = {
        (* front is young, back is old. *)
        promotable_dq : kontframe Core.Deque.t;
        mutable head : kontframe Uopt.t;
        return_ref : int ref

    }

    let init_kont r = {promotable_dq = Core.Deque.create ~initial_length:100 () ;head = Uopt.none; return_ref = r}

    exception BrokenInvariant of string

    let rec try_promote k =
        match Core.Deque.dequeue_back k.promotable_dq with
        | None -> ()
        | Some kf ->
            match kf.frame_type with
            | Recur t ->
                let r = ref 0 in
                let p = T.async !Params.pool (fun () -> sum' (ref t) (init_kont r) (ref 0)) in
                kf.frame_type <- Join (r,p)
            | _ -> raise (BrokenInvariant "Oldest stack frame is not a recur.")

    and sum' t (k : kont) beats =
        let heartbeat () =
            if !beats >= Params.heartbeat_rate then (beats := 0; true)
            else (incr beats; false)
        in
        let sum_quit = ref false in
        while not !sum_quit do
            (* at the start of each iteration, promote the oldest Recursive *)
            if heartbeat () then try_promote k else ();
            match !t with
            | Tree.Empty ->
                let acc = ref 0 in
                let apply_quit = ref false in
                while not !apply_quit do
                    if heartbeat () then try_promote k else ();
                    if Uopt.is_none k.head then (k.return_ref := !acc; apply_quit := true; sum_quit := true)
                    else
                        let frame = Uopt.unsafe_value k.head in
                        match frame.frame_type with
                        | Recur t' ->
                            t := t';
                            k.head <- Uopt.some {frame_type = Accum !acc; next = frame.next };
                            apply_quit := true;
                            ignore (Core.Deque.dequeue_front_exn k.promotable_dq)
                        | Accum x -> acc := !acc + x; k.head <- frame.next
                        | Join (r,p) ->
                            T.await !Params.pool p;
                            k.head <- Uopt.some {frame_type = Accum !r; next = k.head};
                done
            | Node (_,x,l,r) ->
                t := l;
                let kf_accum = {frame_type = Accum x; next = k.head} in
                let kf_recur = {frame_type = Recur r; next = Uopt.some kf_accum} in
                Core.Deque.enqueue_front k.promotable_dq kf_recur;
                k.head <- Uopt.some kf_recur;
        done
    let sum t = T.run !Params.pool (fun () -> let r = ref 0 in sum' (ref t) (init_kont r) (ref 0); !r)
end

module HeartbeatSumUoptLoop (Params : sig
    val heartbeat_rate : int
    val pool : T.pool ref
end
) : SUM
= struct

    type kontframe_type = Recur of Tree.t | Accum of int | Join of int ref * unit T.promise

    type kontframe = {
        mutable frame_type : kontframe_type;
        next : kontframe Uopt.t;
    }

    (* a continuation is (a) a linked list of frames, just like before, and
     (b) a deque of pointers to Recur frames. The front of the queue is the youngest stack frame, most recently pushed.
       the rear of the queue is the oldest stack frame, the closest to being promoted.
    *)
    type kont = {
        (* front is young, back is old. *)
        promotable_dq : kontframe Core.Deque.t;
        head : kontframe Uopt.t;
        return_ref : int ref

    }

    let init_kont r = {promotable_dq = Core.Deque.create ~initial_length:100 () ;head = Uopt.none; return_ref = r}

    exception BrokenInvariant of string

    let rec try_promote k =
        match Core.Deque.dequeue_back k.promotable_dq with
        | None -> ()
        | Some kf ->
            match kf.frame_type with
            | Recur t ->
                let r = ref 0 in
                let p = T.async !Params.pool (fun () -> go t (init_kont r) ~beats:0) in
                kf.frame_type <- Join (r,p)
            | _ -> raise (BrokenInvariant "Oldest stack frame is not a recur.")

    and go t (k : kont) ~beats =
        let heartbeat () =
            if beats >= Params.heartbeat_rate then (0, true)
            else (beats + 1, false)
        in
        let (beats,hb) = heartbeat() in
        if hb then try_promote k;
        match t with
        | Tree.Empty -> apply k ~beats:beats ~acc:0
        | Tree.Node(_,x,l,r) -> 
            let kf_accum = {frame_type = Accum x; next = k.head} in
            let kf_recur = {frame_type = Recur r; next = Uopt.some kf_accum} in
            Core.Deque.enqueue_front k.promotable_dq kf_recur;
            go l {k with head = Uopt.some kf_recur} ~beats:beats
    and [@inline] apply k ~beats ~acc =
        if Uopt.is_none k.head then k.return_ref := acc
        else
            let frame = Uopt.unsafe_value k.head in
            match frame.frame_type with
            | Recur t' ->
                ignore (Core.Deque.dequeue_front_exn k.promotable_dq);
                let acc_frame = Uopt.some {frame_type = Accum acc; next = frame.next} in
                go t' {k with head = acc_frame} ~beats
            | Accum x -> apply {k with head = frame.next} ~beats:beats ~acc:(acc + x)
            | Join (r,p) ->
                T.await !Params.pool p;
                let acc_frame = Uopt.some {frame_type = Accum !r; next = k.head} in
                apply {k with head = acc_frame} ~beats:beats ~acc:acc
            
    let sum t = T.run !Params.pool (fun () -> let r = ref 0 in go t (init_kont r) ~beats:0; !r)
end

module ForkJoinSum(Params : sig
    val pool : T.pool ref
    val fork_cutoff : int

end) : (sig
    include SUM
    val teardown : unit -> unit
 end) = struct
    module T = Domainslib.Task;;

    let rec fj_sum t () =
        if Tree.size t < Params.fork_cutoff then RecursiveLeak.sum t else
        match t with
        | Empty -> 0
        | Node (_,x,l,r) ->
            let pl = T.async !Params.pool (fj_sum l) in
            let pr = T.async !Params.pool (fj_sum r) in
            let nl = T.await !Params.pool pl in
            let nr = T.await !Params.pool pr in
            x + nl + nr
    
    let sum t = T.run !Params.pool (fj_sum t)

    let teardown () = T.teardown_pool !Params.pool
end
