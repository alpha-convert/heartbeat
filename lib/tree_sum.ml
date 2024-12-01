module type SUM = sig
    val sum : Tree.t -> int
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

(*
1. Normal Recursive tree sum.
*)
module Recursive : SUM = struct
    let rec sum t =
        match Tree.view t with
        | None -> 0
        | Some (x,l,r) -> x + sum l + sum r
end

(*
2. CPS'd RecurAndAccumsive tree sum
*)

module CPS : SUM = struct
    let rec sum' t k =
        match Tree.view t with
        | None -> k 0
        | Some (x,l,r) -> sum' l (fun sl -> sum' r (fun sr -> k (x + sl + sr)))
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
        match Tree.view t with
        | None -> apply k 0
        | Some (x,l,r) -> sum' l (Recur (r,Accum (x,k)))
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
        match Tree.view t with
        | None -> apply k 0
        | Some (x,l,r) -> sum' l (Recur (r,(Accum (x,k))))
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
        match Tree.view t with
        | None -> apply k 0
        | Some (x,l,r) -> sum' l (Recur (r,Accum (x,k)))

    let sum t = let r = ref 0 in sum' t (Store r); !r
end


(*
6. Inline apply into the definiton of sum'
*)
module Inlined_TR_ICPS_Defunc : SUM = struct
    type kont = Store of int ref | Recur of Tree.t * kont | Accum of int * kont
    let rec sum' t k =
        match Tree.view t with
        | None ->
            let k_ref = ref k in
            let acc = ref 0 in
            let quit = ref false in
            while not !quit do
                match !k_ref with
                | Store dst -> dst := !acc; quit := true
                | Recur (t,k') -> sum' t (Accum (!acc,k')); quit := true
                | Accum (x,k') -> acc := !acc + x; k_ref := k'
            done
        | Some (x,l,r) -> sum' l (Recur (r,Accum (x,k)))

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
            match Tree.view !t with
            | None ->
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
            | Some (x,l,r) ->
                t := l;
                k := Recur (r,Accum (x,!k))
        done
    let sum t = let r = ref 0 in sum' t (Store r); !r
end

module CompleteLiftAcc : SUM = struct
    type kont = Store of int ref | Recur of Tree.t * kont | Accum of int * kont
    let sum' t k =
        let t = ref t in
        let k = ref k in
        let acc = ref 0 in
        let sum_quit = ref false in
        while not !sum_quit do
            match Tree.view !t with
            | None ->
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
            | Some (x,l,r) ->
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

    type kontframe_type =
    | Recur of Tree.t
    | Accum of int
    | Join of (int ref) * (unit T.promise)
    
    type kontframe = {
        mutable frame_type : kontframe_type;
        next : [`Nil of int ref | `Box of kontframe]
    }

    type kont = {
        (* front is young, back is old. *)
        promotable_dq : (kontframe ref) Core.Deque.t;
        mutable frames : [`Nil of int ref | `Box of kontframe]
    }

    let init_kont r = {promotable_dq = Core.Deque.create();frames = `Nil r}

    exception BrokenInvariant of string

    let rec try_promote k =
        match Core.Deque.dequeue_back k.promotable_dq with
        | None -> ()
        | Some rkf ->
            match !rkf.frame_type with
            | Recur t ->
                let r = ref 0 in
                let p = T.async pool (fun () -> sum' (ref t) (init_kont r) (ref 0)) in
                !rkf.frame_type <- Join (r,p)
            | _ -> raise (BrokenInvariant "Oldest stack frame is not a recur.")

    and sum' t (k : kont) beats =
        let heartbeat () =
            if !beats >= Params.heartbeat_rate then (beats := 0; true)
            else (incr beats; false)
        in
        let sum_quit = ref false in
        while not !sum_quit do
            if heartbeat () then try_promote k else ();
            match Tree.view !t with
            | None ->
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
                            T.await pool p;
                            k.frames <- `Box {frame_type = Accum !r; next = frame.next}
                    )
                done
            | Some (x,l,r) ->
                t := l;
                let kf_accum = {frame_type = Accum x; next = k.frames} in
                let kf_recur = {frame_type = Recur r; next = `Box kf_accum} in
                Core.Deque.enqueue_front k.promotable_dq (ref kf_recur);
                k.frames <- `Box kf_recur
        done
    let sum t = T.run pool (fun () -> 
        let r = ref 0 in sum' (ref t) (init_kont r) (ref 0); !r
    )
end

module ForkJoinSum(Params : sig
    val num_domains : int
    val fork_cutoff : int

end) : SUM = struct
    module T = Domainslib.Task;;

    let pool = T.setup_pool ~num_domains:Params.num_domains ()

    let rec fj_sum t () =
        if Tree.size t < Params.fork_cutoff then Recursive.sum t else
        match Tree.view t with
        | None -> 0
        | Some (x,l,r) ->
            let pl = T.async pool (fj_sum l) in
            let pr = T.async pool (fj_sum r) in
            let nl = T.await pool pl in
            let nr = T.await pool pr in
            x + nl + nr
    
    let sum t = T.run pool (fj_sum t)
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

let%test_unit "Complete/Heartbeat" =
    let module Params = struct
        let num_domains = 4
        let heartbeat_rate = 3
    end in
    let module HB = HeartbeatSum(Params) in
    let open Mica.TestHarness(Complete)(HB) in
    run_tests ()

let%test_unit "Recursive/Heartbeat" =
    let module Params = struct
        let num_domains = 4
        let heartbeat_rate = 3
    end in
    let module HB = HeartbeatSum(Params) in
    let open Mica.TestHarness(Recursive)(HB) in
    run_tests ()

let%test_unit "Recursive/ForkJoin" =
    let module Params = struct
        let num_domains = 4
        let fork_cutoff = 10
    end in
    let module HB = ForkJoinSum(Params) in
    let open Mica.TestHarness(Recursive)(HB) in
    run_tests ()