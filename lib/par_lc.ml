type var = String.t
type term = Var of var | Lam of var * term | App of term * term | ParPair of term * term | Fst of term | Snd of term

type value = Clos of env * var  * term | PairVal of value * value
and env = (var , value, Core.String.comparator_witness) Base.Map.t

exception RuntimeErr

let match_clos v =
  match v with
  | Clos (rho,x,t) -> (rho,x,t)
  | _ -> raise RuntimeErr

let match_pair v =
  match v with
  | PairVal (v1,v2) -> (v1,v2)
  | _ -> raise RuntimeErr

let bind x v rho = Core.Map.add_exn (Core.Map.remove rho x) x v

let lookup x rho =
  try Core.Map.find_exn rho x with
  _ -> raise RuntimeErr

let rec seq_big_step (e : term) rho : value =
  match e with
  | Var x -> lookup x rho
  | Lam (x,t) -> Clos (rho,x,t)
  | App (e1,e2) ->
      let (rho',x,e') = seq_big_step_clos e1 rho in
      seq_big_step e' (bind x (seq_big_step e2 rho) rho')
  | ParPair (e1,e2) ->
      PairVal (seq_big_step e1 rho, seq_big_step e2 rho)
  | Fst e -> let (v,_) = seq_big_step_pair e rho in v
  | Snd e -> let (_,v) = seq_big_step_pair e rho in v
and seq_big_step_clos e rho = match_clos (seq_big_step e rho)
and seq_big_step_pair e rho = match_pair (seq_big_step e rho)


type kont = KAppL of term * env * kont
          | KAppR of env * var * term * kont
          | KPairL of term * env * kont
          | KPairR of value * kont
          | KFst of kont
          | KSnd of kont
          | KTop

type config = CTerm of term | CValue of value

let step c rho k =
  let throw rho k v =
    match k with
    | KAppL (t',rho'',k') ->
        let rho',x',t = match_clos v in
        (CTerm t',rho'', KAppR (rho',x',t,k'))
    | KAppR (rho',x,t,k') -> (CTerm t, bind x v rho', k')
    | KPairL (t,rho',k') -> (CTerm t, rho', KPairR (v,k'))
    | KPairR (v',k') -> (CValue (PairVal (v',v)),rho,k')
    | KFst k' ->
        let v,_ = match_pair v in
        (CValue v, rho, k')
    | KSnd k' ->
        let _,v = match_pair v in
        (CValue v, rho, k')
    | KTop -> (CValue v, rho, KTop)
  in
  let push rho k t =
    match t with
    | Var x -> (CValue (lookup x rho),rho,k)
    | Lam (x,t) -> (CValue (Clos (rho,x,t)),rho,k)
    | App (e1,e2) -> (CTerm e1,rho,KAppL (e2,rho,k))
    | ParPair (e1,e2) -> (CTerm e1,rho,KPairL (e2,rho,k))
    | Fst e -> (CTerm e, rho, KFst k)
    | Snd e -> (CTerm e, rho, KSnd k)
  in
  match c with
  | CValue v -> throw rho k v
  | CTerm t -> push rho k t

let seq_small_step t rho =
  let rec go c rho k =
    match c,k with
    | CValue v, KTop -> v
    | _,_ -> let c',rho',k' = step c rho k in
            go c' rho' k'
  in go (CTerm t) rho KTop


let par_small_step num_domains t rho =
  (* bad for benchmarking, set these up before. *)
  let module T = Domainslib.Task in
  let pool = T.setup_pool ~num_domains:num_domains () in
  let rec go c rho k ()=
    match c,k with
    | CValue v, KTop -> v
    | CTerm (ParPair (e1,e2)), k ->
        let p1 = T.async pool (go (CTerm e1) rho KTop) in
        let p2 = T.async pool (go (CTerm e2) rho KTop) in
        let v1 = T.await pool p1 in
        let v2 = T.await pool p2 in
        go (CValue (PairVal (v1,v2))) rho k ()
    | _,_ -> let c',rho',k' = step c rho k in
             go c' rho' k' ()
  in
  T.run pool (go (CTerm t) rho KTop)
