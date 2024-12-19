open Heartbeat

open Core
open Core_bench


(*
Note: memory manager (GC) might degrade with number of domains. be careful of this. potential stop the world pauses with GC

High level: each domain has its own minor heap, they share a major heap.
All collections are stop-the-world (we think). Peruse the "retrofitting parallelism".

Promotions can happen because of task migration: another domain wants to start executing a task you've put on your queue.
Moving the task between domains *requires* promoting it.

Potential performance problems might be because of the allocations of the traversa/sum itself.
*)
let num_domains = 0
let pool = ref (Domainslib.Task.setup_pool ~num_domains:num_domains ())
let refresh_pool () =
  Domainslib.Task.teardown_pool !pool;
  pool := Domainslib.Task.setup_pool ~num_domains:num_domains ()

let () = 
  let depths = [18] in
  let depths_and_names = List.map ~f:(fun n -> (Int.to_string n,n)) depths in
  Bench.bench 
    ~run_config:(Bench.Run_config.create ~quota:(Bench.Quota.Num_calls 10000) ())
  [
    Bench.Test.create_group ~name:"balanced" [
      Bench.Test.create_parameterised ~args:depths_and_names ~name:"recursive" @@
      (
        fun n -> 
        let t = Core.Quickcheck.random_value ~size:n Tree.generate_balanced in
        Core.stage @@ fun () -> Tree_sum.Recursive.sum t
      );
      Bench.Test.create_parameterised ~args:depths_and_names ~name:"recursive-leak" @@
      (
        fun n -> 
        let t = Core.Quickcheck.random_value ~size:n Tree.generate_balanced in
        Core.stage @@ fun () -> Tree_sum.RecursiveLeak.sum t
      );
      Bench.Test.create_parameterised ~args:depths_and_names ~name:"recursive-acc-ref" @@
      (
        fun n -> 
        let t = Core.Quickcheck.random_value ~size:n Tree.generate_balanced in
        Core.stage @@ fun () -> Tree_sum.RecursiveAccRef.sum t
      );
      Bench.Test.create_parameterised ~args:depths_and_names ~name:"explicit-stack" @@
      (
        fun n -> 
        let t = Core.Quickcheck.random_value ~size:n Tree.generate_balanced in
        Core.stage @@ fun () -> Tree_sum.ExplicitStack.sum t
      );
      Bench.Test.create_parameterised ~args:depths_and_names ~name:"explicit-stack-list" @@
      (
        fun n -> 
        let t = Core.Quickcheck.random_value ~size:n Tree.generate_balanced in
        Core.stage @@ fun () -> Tree_sum.ExplicitStackList.sum t
      );
      Bench.Test.create_parameterised ~args:depths_and_names ~name:"cps" @@
      (
        fun n -> 
        let t = Core.Quickcheck.random_value ~size:n Tree.generate_balanced in
        Core.stage @@ fun () -> Tree_sum.CPS.sum t
      );

      Bench.Test.create_parameterised ~args:depths_and_names ~name:"cps-defunc" @@
      (
        fun n -> 
        let t = Core.Quickcheck.random_value ~size:n Tree.generate_balanced in
        Core.stage @@ fun () -> Tree_sum.CPSDefunc.sum t
      );
      Bench.Test.create_parameterised ~args:depths_and_names ~name:"icps-defunc" @@
      (
        fun n -> 
        let t = Core.Quickcheck.random_value ~size:n Tree.generate_balanced in
        Core.stage @@ fun () -> Tree_sum.ICPSDefunc.sum t
      );
      (* Bench.Test.create_parameterised ~args:depths_and_names ~name:"tr-icps-defunc" @@
      (
        fun n -> 
        let t = Core.Quickcheck.random_value ~size:n Tree.generate_balanced in
        Core.stage @@ fun () -> Tree_sum.TR_ICPS_Defunc.sum t
      );
      Bench.Test.create_parameterised ~args:depths_and_names ~name:"inlined-tr-icps-defunc" @@
      (
        fun n -> 
        let t = Core.Quickcheck.random_value ~size:n Tree.generate_balanced in
        Core.stage @@ fun () -> Tree_sum.Inlined_TR_ICPS_Defunc.sum t
      ); *)
      Bench.Test.create_parameterised ~args:depths_and_names ~name:"complete" @@
      (
        fun n -> 
        Gc.set { (Gc.get()) with minor_heap_size = 99999000}; (* make the minor heap sufficiently large that this doesn't alocate...*)
        let t = Core.Quickcheck.random_value ~size:n Tree.generate_balanced in
        Core.stage @@ fun () -> Tree_sum.Complete.sum t
      );

      Bench.Test.create_parameterised ~args:depths_and_names ~name:"complete-lift-acc" @@
      (
        fun n -> 
        Gc.set { (Gc.get()) with minor_heap_size = 99999000}; (* make the minor heap sufficiently large that this doesn't alocate...*)
        let t = Core.Quickcheck.random_value ~size:n Tree.generate_balanced in
        Core.stage @@ fun () -> Tree_sum.CompleteLiftAcc.sum t
      );
      Bench.Test.create_parameterised ~args:depths_and_names ~name:"complete-lift-acc-region" @@
      (
        fun n -> 
        Gc.set { (Gc.get()) with minor_heap_size = 99999000}; (* make the minor heap sufficiently large that this doesn't alocate...*)
        let t = Core.Quickcheck.random_value ~size:n Tree.generate_balanced in
        let region = Core.Uniform_array.create ~len:1000 Tree.empty in
        let module M = Tree_sum.CompleteLiftAccRegion(struct let region = region end) in
        Core.stage @@ fun () -> M.sum t
      );

      Bench.Test.create_parameterised ~args:depths_and_names ~name:"fj-fork10000" @@
      (
        Gc.set { (Gc.get()) with minor_heap_size = 256000};
        let fork_cutoff = 10000 in
        fun n -> refresh_pool(); let module Params = struct let pool = pool;; let fork_cutoff = fork_cutoff end in let module FJ = Tree_sum.ForkJoinSum(Params) in
        let t = Core.Quickcheck.random_value ~size:n Tree.generate_balanced in
        Core.stage @@ fun () -> FJ.sum t
      );
      Bench.Test.create_parameterised ~args:depths_and_names ~name:"fj-fork100000" @@
      (
        let fork_cutoff = 100000 in
        fun n -> refresh_pool(); let module Params = struct let pool = pool;; let fork_cutoff = fork_cutoff end in let module FJ = Tree_sum.ForkJoinSum(Params) in
        let t = Core.Quickcheck.random_value ~size:n Tree.generate_balanced in
        Core.stage @@ fun () -> FJ.sum t
      );
      Bench.Test.create_parameterised ~args:depths_and_names ~name:"fj-fork1000000" @@
      (
        let fork_cutoff = 1000000 in
        fun n -> refresh_pool(); let module Params = struct let pool = pool;; let fork_cutoff = fork_cutoff end in let module FJ = Tree_sum.ForkJoinSum(Params) in
        let t = Core.Quickcheck.random_value ~size:n Tree.generate_balanced in
        Core.stage @@ fun () -> FJ.sum t
      );
      Bench.Test.create_parameterised ~args:depths_and_names ~name:"hb" @@
      (
        let heartbeat_rate = 10000000 in
        fun n -> refresh_pool(); let module Params = struct let pool = pool;; let heartbeat_rate = heartbeat_rate end in let module HB = Tree_sum.HeartbeatSum(Params) in
        let t = Core.Quickcheck.random_value ~size:n Tree.generate_balanced in
        Core.stage @@ fun () -> HB.sum t
      );
    ] 
  ]