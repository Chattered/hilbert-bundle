(* Additional combinators for Mizar Light. *)

module Ts  = Treestream
module Tsm = Monad.MakeLazyPlus(Ts)

let aconv_ac rls tm1 tm2 =
  let rwr tm =
    snd (dest_eq (concl (REWRITE_CONV rls tm))) in
  let rec aac tm1 tm2 =
    tm1 = tm2 or
      match (tm1,tm2) with
          Var(x1,ty1),Var(x2,ty2) -> tm1 = tm2
        | Const(x1,ty1),Const(x2,ty2) -> tm1 = tm2
        | Comb(s1,t1),Comb(s2,t2) ->
          aac s1 s2 && aac t1 t2
        | Abs(Var(_,ty1) as x1,t1),Abs(Var(_,ty2) as x2,t2) ->
          ty1 = ty2 && aac (rwr t1) (rwr (vsubst [x1,x2] t2))
        | _,_ -> false in
  aac (rwr tm1) (rwr tm2)

let discovery_depth = ref 40

(* Discover theorems based on the discovered goal hypotheses and add
   as justification.  *)    
let (obviously : (thm Ts.m -> thm Ts.m) -> step -> step)
    = fun d (tac, (t,l,thl,just)) ->
      tac,
      (t,l,thl,
       let j thms ((hyps,g_tm) as g) = 
         let hyps = Tsm.of_list (map snd (hyps_with_set hyps)) in
         let d_thms = Ll.to_list
           (Ll.concat (Ts.to_thms (Ll.take !discovery_depth (d hyps)))) in
         (just (d_thms @ thms)) g in
       match t with
           None -> failwith "obviously"
         | Some t -> j)

(* Attempt to find the conjuncts in the goal and then rewrite. *)
let (clearly : (thm Ts.m -> thm Ts.m) -> step -> step)
    = fun d (tac, (t,l,thl,just)) ->
      tac,
      (t,l,thl,
       let j thms ((hyps,g_tm) as g) =
         let hyps = Tsm.of_list (map snd (hyps_with_set hyps)) in
         let d_thms = Ll.find_all
           (fun tm thm -> aconv_ac [CONJ_ACI] tm (concl thm))
           (conjuncts g_tm)
           (Ll.concat (Ts.to_thms (Ll.take !discovery_depth (d hyps)))) in
         (just (d_thms @ thms)) g in
       match t with
           None -> failwith "obviously"
         | Some t -> j)

(* Interactive case splitting. *)
let (case' : (goal -> term) -> step) =
  fun t ->
    (fun (t',l,thl, just) g ->
       match t' with
	   None -> failwith "case"
	 | Some t' -> 
	     (DISJ_CASES_THEN2 (N_ASSUME_TAC l)
		(LABEL_TAC "case") (SPEC (t' g) EXCLUDED_MIDDLE)) g),    
    default_stepinfo (Some t);;

(* Final case split. *)
let (finished : step) =
  (fun (_,_,thl,just) (asl,_) as g ->
     just (map snd (filter ((=) "case" o fst) asl) @ thl g) g),
  default_stepinfo None;;
     
(* Interactive subgoaling. *)
let (lemma' : (goal -> term) -> step) =
  fun t ->
    (fun (t',l,thl,just) g ->
       match t' with
	   None -> failwith "lemma"
	 | Some t' ->
	     (SUBGOAL_THEN (t' g) (N_ASSUME_TAC l)) g),
    default_stepinfo (Some t);;

let goal_frees (hyps,gl) =
  let can_gen thm =
    let concl_frees = frees (concl thm) in
    filter (not o C mem concl_frees) (freesl (hyp thm)) in
  itlist union (map (can_gen o snd) hyps) (frees gl) 

(* Modification to set, generalising free variables not free in the goal or
   generalisable in the hypotheses. *)
let (set': (goal -> term) -> step) =
  fun t ->
    let stp =
      (fun (t',l,_,_) g ->
       match t' with
         None -> failwith "set"
       | Some t ->
           let eq = t g in
           let lhs,rhs = dest_eq eq in
           let lv,largs = strip_comb lhs in
           let rtm = list_mk_abs(largs,rhs) in
           let ex = mk_exists(lv,mk_eq(lv,rtm)) in
           let genargs = filter (not o C mem (goal_frees g)) largs in
           (SUBGOAL_THEN ex (X_CHOOSE_THEN lv
                               (fun th -> (N_ASSUME_TAC l o itlist GEN genargs)
		                 (prove(eq,REWRITE_TAC[th])))) THENL
              [REWRITE_TAC[EXISTS_REFL];
               ALL_TAC]) g),
      default_stepinfo (Some t) in
    stp at -1;;

let set_assums (hyps,_) =
  map snd (filter ((=) "=" o fst) hyps)

(* Alternative take, rewriting with set assumptions if EXISTS_TAC fails. *)
let (take': (goal -> term) list -> step) =
  fun tl ->
    (fun _ g -> (MAP_EVERY EXISTS_TAC (map (fun t -> t g) tl)
                   ORELSE (REWRITE_TAC (set_assums g)
                             THEN MAP_EVERY EXISTS_TAC (map (fun t -> t g) tl))) g),
    default_stepinfo None;;

(* Simple rewriting of the goal with justification theorems. *)
let (unfolding : step) =
  (fun (_,_,thl,_) g -> REWRITE_TAC (thl g) g), default_stepinfo None

let case = case' o parse_mterm;;
let lemma = lemma' o parse_mterm;;
let set = set' o parse_mterm;;
let take = take' o map parse_mterm;;

