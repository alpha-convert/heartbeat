open Heartbeat

open Core
open Core_bench

module R = Tree_sum.Recursive
module HB = Tree_sum.HeartbeatSum(
  struct
    let heartbeat_rate = 1000
    let num_domains = 4
  end
)
module FJ = Tree_sum.ForkJoinSum(
  struct
    let num_domains = 4
    let fork_cutoff = 300
  end
)


let () = Command_unix.run @@ 
  let balanced_tree = Core.Quickcheck.random_value ~seed:`Nondeterministic ~size:14 Tree.generate_balanced in
  let () = print_endline (Int.to_string (Tree.size balanced_tree)) in
  Bench.make_command [
    Bench.Test.create_group ~name:"balanced" [
      Bench.Test.create ~name:"recursive" (fun () -> R.sum balanced_tree);
      (* Bench.Test.create ~name:"CPS" (fun () -> Tree_sum.CPS.sum balanced_tree); *)
      (* Bench.Test.create ~name:"CPSDefunc" (fun () -> Tree_sum.CPSDefunc.sum balanced_tree); *)
      (* Bench.Test.create ~name:"ICPSDefunc" (fun () -> Tree_sum.ICPSDefunc.sum balanced_tree); *)
      (* Bench.Test.create ~name:"TR_ICPSDefunc" (fun () -> Tree_sum.TR_ICPS_Defunc.sum balanced_tree); *)
      (* Bench.Test.create ~name:"Inlined_TR_ICPSDefunc" (fun () -> Tree_sum.Inlined_TR_ICPS_Defunc.sum balanced_tree); *)
      Bench.Test.create ~name:"Complete" (fun () -> Tree_sum.Complete.sum balanced_tree);
      Bench.Test.create ~name:"heartbeat" (fun () -> HB.sum balanced_tree);
      Bench.Test.create ~name:"FJ" (fun () -> FJ.sum balanced_tree)
    ]
]

let () = HB.teardown ()
