type pool = unit
type 'a promise = unit -> 'a

let async _ f = f
let await _ f = f ()

let run _ f = f ()

let teardown_pool _ = ()

let setup_pool ~num_domains () = ()