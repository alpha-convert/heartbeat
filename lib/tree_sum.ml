module type SUM = sig
    val sum : Tree.t -> int [@@zero_alloc]
end
include
  struct
    [@@@ocaml.warning "-60"]
    module Mica =
      struct
        include
          struct
            type expr =
              | Sum of Tree.t [@@deriving show { with_path = false }]
            type ty =
              | Int [@@deriving show { with_path = false }]
            let gen_expr ty =
              let open Core in
                let open Quickcheck.Generator in
                  let open Let_syntax in
                    size >>=
                      (fun k ->
                         match (ty, k) with
                         | (Int, _) ->
                             let gen_sum =
                               let g__001_ = Tree.quickcheck_generator_t in
                               g__001_ >>| (fun e__002_ -> Sum e__002_) in
                             union [gen_sum])
            let _ = gen_expr
          end
        module Interpret(M:SUM) =
          struct
            type value =
              | ValInt of int
            let interp e =
              match e with | Sum treet__003_ -> ValInt (M.sum treet__003_)
            let _ = interp
          end
        include
          struct
            module TestHarness(M1:SUM)(M2:SUM) =
              struct
                module I1 = (Interpret)(M1)
                module I2 = (Interpret)(M2)
                open Core
                include
                  struct
                    let trials = 100
                    let test_int () =
                      Quickcheck.test (gen_expr Int)
                        ~trials:trials
                        ~f:(fun e ->
                              match ((I1.interp e), (I2.interp e)) with
                              | (ValInt int__005_, ValInt int__004_) ->
                                  ([%test_eq : int]) int__005_ int__004_)
                    let _ = test_int
                    let run_tests () = test_int ()
                    let _ = run_tests
                  end
              end
          end
      end
  end[@@ocaml.doc "@inline"]

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
                            let _ = Core.Deque.dequeue_front_exn k.promotable_dq in ()
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
        mutable next : kontframe Uopt.t;
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
            (* if heartbeat () then try_promote k else (); *)
            match !t with
            | Tree.Empty ->
                let acc = ref 0 in
                let apply_quit = ref false in
                while not !apply_quit do
                    (* if heartbeat () then try_promote k else (); *)
                    if Uopt.is_none k.head then (k.return_ref := !acc; apply_quit := true; sum_quit := true)
                    else
                        let frame = Uopt.unsafe_value k.head in
                        match frame.frame_type with
                        | Recur t' ->
                            t := t';
                            k.head <- Uopt.some {frame_type = Accum !acc; next = frame.next };
                            apply_quit := true;
                            (* let _ = Core.Deque.dequeue_front_exn k.promotable_dq in (); *)
                        | Accum x -> acc := !acc + x; k.head <- frame.next
                        | Join (r,p) ->
                            T.await !Params.pool p;
                            k.head <- Uopt.some {frame_type = Accum !r; next = k.head};
                done
            | Node (_,x,l,r) ->
                t := l;
                let kf_accum = {frame_type = Accum x; next = k.head} in
                let kf_recur = {frame_type = Recur r; next = Uopt.some kf_accum} in
                (* Core.Deque.enqueue_front k.promotable_dq kf_recur; *)
                k.head <- Uopt.some kf_recur;
        done
    let sum t = T.run !Params.pool (fun () -> let r = ref 0 in sum' (ref t) (init_kont r) (ref 0); !r)
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


let%test_unit "Recursive/CPS" =
    let open Mica.TestHarness(Recursive)(CPS) in
    run_tests ()

let%test_unit "Recursive/Complete" =
    let open Mica.TestHarness(Recursive)(Complete) in
    run_tests ()

let%test_unit "Complete/CompleteLiftAcc" =
    let open Mica.TestHarness(Complete)(CompleteLiftAcc) in
    run_tests ()

let%test_unit "Complete/CompleteLiftAccRegion" =
    let region = Core.Uniform_array.create ~len:100000 Tree.empty in
    let module M = CompleteLiftAccRegion(struct let region = region end) in
    let open Mica.TestHarness(Complete)(M) in
    run_tests ()


let%test_unit "Complete/Heartbeat" =
    let pool = ref @@ T.setup_pool ~num_domains:4 () in
    let module Params = struct
        let pool = pool
        let heartbeat_rate = 3
    end in
    let module HB = HeartbeatSum(Params) in
    let open Mica.TestHarness(Complete)(HB) in
    run_tests ();
    T.teardown_pool !pool

let%test_unit "Recursive/Heartbeat" =
    let pool = ref @@ T.setup_pool ~num_domains:4 () in
    let module Params = struct
        let pool = pool
        let heartbeat_rate = 3
    end in
    let module HB = HeartbeatSum(Params) in
    let open Mica.TestHarness(Recursive)(HB) in
    run_tests ();
    T.teardown_pool !pool

let%test_unit "Recursive/Heartbeat" =
    let pool = ref @@ T.setup_pool ~num_domains:0 () in
    let module Params = struct
        let pool = pool
        let heartbeat_rate = 1000000000000000000
    end in
    let module HB = HeartbeatSumUopt(Params) in
    let open Mica.TestHarness(Recursive)(HB) in
    run_tests ();
    T.teardown_pool !pool

let%test_unit "Recursive/ForkJoin" =
    let pool = ref @@ T.setup_pool ~num_domains:4 () in
    let module Params = struct
        let pool = pool
        let fork_cutoff = 10
    end in
    let module HB = ForkJoinSum(Params) in
    let open Mica.TestHarness(Recursive)(HB) in
    run_tests ();
    T.teardown_pool !pool