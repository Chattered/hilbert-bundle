module Bu = BatUnix

(* Interpret exceptions in the evaluation of a predicate as false. *)
let and_can f x =
  try
    f x
  with _ -> false

(* Folding and_can across a list. *)
let rec all_can f = function
    []    -> true
  | x::xs ->
      try f x && all_can f xs
      with _ -> false
    
(* All ways of taking a single element from a list *)
let removes xs =
  let rec loop pre rs = function
    []      -> rs
  | (x::xs) -> loop (pre @ [x]) ((x,pre @ xs) :: rs) xs
  in loop [] [] xs;;

(* Map a commutative binary function across all unordered pairs drawn from a list. *)
let rec map_sym f = function
    []    -> []
  | x::xs -> List.map (f x) xs @ map_sym f xs

(* Rewrite each element of a list of rewrites with the others. *)
let mutual_rewrite rls =
  List.map (fun (rl,rls) -> REWRITE_RULE rls rl) (removes rls)

let mutual_simp rls =
  List.map (fun (rl,rls) -> SIMP_RULE rls rl) (removes rls)

(* Hack to redirect all SIGINTs to the current thread *)
let interrupt_only_self () =
  let p = Unix.getpid () in
  let t = Thread.id (Thread.self ()) in
  let Sys.Signal_handle h = Sys.signal 2 Sys.Signal_default in
  let reinterrupt () =
    Thread.delay 0.5;
    Unix.kill p Sys.sigint in
  Sys.set_signal Sys.sigint
    (Sys.Signal_handle (fun n -> if Thread.id (Thread.self ()) = t
      then h n else reinterrupt ()))

(* Rewrite theorems with "=" labelled hypotheses *)    
let (hyps_with_set : goal -> thm list -> thm list) =
  fun (hyps,g) thms ->
    let sets = Bl.map snd (Bl.filter ((=) "=" o fst) hyps) in
    map (REWRITE_RULE sets) thms
      
