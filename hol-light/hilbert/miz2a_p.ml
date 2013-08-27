(* ========================================================================= *)
(* Mizar Light II                                                            *)
(*                                                                           *)
(*                                                                           *)
(* Documentation and marked additions by Phil Scott.                         *)
(* ========================================================================= *)

(* mterm's can be roughly identified with the type (goal -> term). An mterm is
   parsed into an actual term using a goal, which effectively represents the
   proof context and importantly contains the free variables which must be
   matched up with any frees in the mterm (HOL/Light by default will treat
   any new variable as fresh and give it an arbitrary polymorphic type). The
   main definitions of the proof commands have a dashed equivalent (e.g. have'
   for have) which take a (goal -> term) rather than an mterm. *)

(* The goal is identified with the proof context at each step in the proof. *)

type mterm = string;;

let parse_context_term s env =
  let ptm,l = (parse_preterm o lex o explode) s in
  if l = [] then
   (term_of_preterm o retypecheck
     (map ((fun (s,ty) -> s,pretype_of_type ty) o dest_var) env)) ptm
  else failwith "Unexpected junk after term";;

let goal_frees (asl,w) =
  frees (itlist (curry mk_imp) (map (concl o snd) asl) w);;

(* Takes a string and a goal and returns a term where the substrings 
   "thesis" has been replaced by the goal, "antecedent" by any antecedent of
   the goal, opposite by the negation of the goal, and ... by the left-hand
   of the last theorem in the assumption list (the last intermediate fact).*)
let (parse_mterm: mterm -> goal -> term) =
  let ttm = mk_var("thesis",bool_ty) in
  let atm = mk_var("antecedent",bool_ty) in
  let otm = mk_var("opposite",bool_ty) in
  fun s (asl,w as g) ->
    let ant = try fst (dest_imp w) with Failure _ -> atm in
    let opp = try dest_neg w with Failure _ -> mk_neg w in
    let t =
     (subst [w,ttm; ant,atm; opp,otm]
       (parse_context_term s ((goal_frees g) @ [ttm; atm; otm]))) in
    try
      let lhs = lhand (concl (snd (hd asl))) in
      let itm = mk_var("...",type_of lhs) in
      subst [lhs,itm] t
    with Failure _ -> t;;

(* The elements of stepinfo are
     1) the term associated with this step (such as the term assumed by assume)
     2) a number associated with this step, which will label the term if added
        to the goal's hypotheses
     3) a list of theorems chosen to justify this step dependent on the proof
        context (goal)
        at this point in the proof
     4) a tactic which depends on the justification theorems
*)

(* PHIL: The number label is now a list, allowing the user to break a
   conjunction into separate hypotheses. *)
type stepinfo =
  (goal -> term) option * int list *
  (goal -> thm list) * (thm list -> tactic);;

(* A step then consists in a continuation of a function which sends a stepinfo to
   a tactic. A step will be introduced with a primitive such as assume, and then
   augmented by subsequent primitives such as have, after which it can be turned
   into a tactic by applying the first component to the second. Steps are generally
   composed by primitives such as proof and theorem, which apply the tactics
   of each step in sequence to solve the (sub)goal.*)

type step = (stepinfo -> tactic) * stepinfo;;

let TRY' tac thl = TRY (tac thl);;

let (then'_) = fun tac1 tac2 thl -> tac1 thl THEN tac2 thl;;

(* Phil: Theorems for local variable assignments *)
let (assigns : goal -> thm list) = fun (asl,_) ->
  map snd (filter ((=) "=" o fst) asl);;

let (WITH_REWR_ASSIGN : (thm list -> tactic) -> thm list -> tactic) =
  fun t thl g ->
    let assigns = assigns g in
    (REWRITE_TAC assigns THEN (t (map (REWRITE_RULE assigns) thl))) g;;  

(* The standard prover rewrites the goal and justifying theorems with any
   local variable assignment theorems. I tried two other alternative schemes:

   1) Rewriting in "step" before any tactic is applied: this leads to unwanted
   rewriting in "assume", "fix", "proof" and so on.
   2) Rewriting in "step" before any *justification* tactic is applied: this
   leads to unwanted rewriting in "proof."

   The current scheme also performs the rewriting before tactics supplied by
   "using", so that user supplied tactics can use local variables.

   The reason I have done this is because ARITH_TAC was failing mysteriously
   in the presence of assignment assumptions.
*)
let standard_prover = TRY' (WITH_REWR_ASSIGN (REWRITE_TAC THEN' MESON_TAC));;
let sketch_prover = K CHEAT_TAC;;
let current_prover = ref standard_prover;;

(* The (goal -> thm list) element of default_stepinfo filters out all
   hypotheses labelled with "=" (which are introduced by specifying "at" with
   a negative number, and passes these to the justification for use with 
   the current_prover.) Currently, the only hypotheses labelled this way are
   assignments of local variables introduced by (set), which seems to be the
   only intention, given the choice of the "=" label.*)
(* Phil: I've changed this so that local variable assignments are not added to
   the justification theorems. See definition of using and standard prover. *)
let (default_stepinfo: (goal -> term) option -> stepinfo) =
  fun t -> t,[],K [],(fun thl -> !current_prover thl);;

(* Currently used to supply the term used with consider. *)
let ((st'): step -> (goal -> term)  -> step) =
  fun (tac,(t,l,thl,just)) t' -> (tac,(Some t',l,thl,just));;

let (st) = fun stp -> (st') stp o parse_mterm;;

(* Replaces the label number associated with this step. *)
let (((at)): step -> int list -> step) =
  fun (tac,(t,_,thl,just)) ls -> (tac,(t,ls,thl,just));;

(* Pulls hypotheses from the goal context and selects them as justifying theorems
   for this step. Hypotheses are chosen by label, or if the argument is negative,
   by counting backwards through the hypothesis list.  *)
let (((from)): step -> int list -> step) =
  fun (tac,(t,l,thl,just)) ll -> (tac,(t,l,
    (fun (asl,_ as g) -> thl g @
      let n = length asl in
      map
        (fun l ->
          if l < 0 then snd (el ((n - l - 1) mod n) asl)
            else assoc (string_of_int l) asl)
        ll),
    just));;

(* Pulls the last hypothesis introduced in the list. *)
let so x = fun y -> x y from [-1];;

(* Selects theorems as justifying this step. *)
let (((by)): step -> thm list -> step) =
  fun (tac,(t,l,thl,just)) thl' -> (tac,(t,l,(fun g -> thl g @ thl'),just));;

(* Inserts a thm list tactic to justify this step. *)
let (((using)): step -> (thm list -> tactic) -> step) =
  fun (tac,(t,l,thl,just)) just' -> (tac,(t,l,thl,WITH_REWR_ASSIGN just' THEN' just));;

let (step: step -> tactic) = fun (f,x) -> f x;;
      
(* itlist is a right fold and ALL_TAC is the identity for THEN. The use of
   THENL means that we require there to be exactly one subgoal generated
   by each tactic. The result is that we apply the first generated tactic
   to produce one subgoal, then apply the second generated tactic, and so
   on. *)

(* PHIL: I'm just adding a counter here for my write-up. This is a dirty
   modification, but should work in most cases. *)
let step_count = ref 0;;

let (steps: step list -> tactic) =
  fun stpl ->
    step_count := !step_count + List.length stpl;
    itlist (fun tac1 tac2 -> tac1 THENL [tac2]) (map step stpl) ALL_TAC;;

(* Ignores all step information and uses a sequence of tactics to advance the goal. *)
let (tactics: tactic list -> step) =
  fun tacl -> ((K (itlist ((THEN)) tacl ALL_TAC)),
    default_stepinfo None);;

(* Uses the trivial goal to instantiate frees in the supplied term, and then
   proves the term by applying each step in sequence. *)
let (theorem': (goal -> term) -> step list -> thm) =
  let g = ([],`T`) in
  fun t stpl -> prove(t g,steps stpl);;

let (((proof)): step -> step list -> step) =
  fun (tac,(t,l,thl,just)) prf -> (tac,(t,l,thl,K (steps prf)));;

(* Places a theorem into the goal's hypotheses, with optional label. If
   the label is negative, then the hypothesis is used as justification by
   default_stepinfo. *)
let (N_ASSUME_TAC: int list -> thm_tactic) =
  let rec conjs thm = function
  [l] -> [l,thm]
    | l::ls -> let lthm,rthm = CONJ_PAIR thm in
               (l,lthm) :: conjs rthm ls in
  fun ls th (asl,_ as g) ->
    match ls with
        [] -> ASSUME_TAC th g
      | ls -> 
        (MAP_EVERY
           (fun n,thm -> 
             LABEL_TAC (if n < 0 then "=" else string_of_int n) thm)
           (conjs th ls)) g

(* Need a proper induction step. Provide the variable to induct on and the
   induction theorem. Use suppose to gather potential antecedents of the
   induction theorem, generalise the induction variable, and then combine into
   the conjuncts of the induction theorem. *)
(* let (((induction)): step -> thm -> step) = *)
(*   fun (tac,(t,l,thl,just)) induct_tac -> *)
(*     (tac,(t,l,thl,K (MATCH_MP_TAC induct_tac *)
(*       THEN CONJUNCTS_TAC))) *)

(* Takes a goal splitting tactic and runs each subproof. This will have to do
   for induction, for now. *)
let (((parts)) : tactic -> step list list -> step) =
  fun tac prfs -> (K (tac THENL map steps prfs), default_stepinfo None);;

(* Case splitting. The term associated with the leading step in each step list
   is merely used to build a disjunction and therefore can be introduced
   with suppose. The remaining steps should prove the main goal. The first argument
   to per can be a step which helps justify the disjunction, or "cases" if the
   disjunction follows from this step alone. *)
let (per: step -> step list list -> step) =
  let F = `F` in
  fun (_,(_,_,thl,just)) cases ->
    (fun (_,_,thl',just') g ->
       let tx (t',_,_,_) =
         match t' with None -> failwith "per" | Some t -> t g in
       let dj = itlist (curry mk_disj)
         (map (tx o snd o hd) cases) F in
       (SUBGOAL_THEN dj
          (EVERY_TCL (map (fun case -> let _,ls,_,_ = snd (hd case) in
            (DISJ_CASES_THEN2 (N_ASSUME_TAC ls))) cases) CONTR_TAC) THENL
        ([(just' THEN' just) ((thl' g) @ (thl g))] @
           map (steps o tl) cases)) g),
    (None,[],(K []),(K ALL_TAC));;

(* ===================================================================== *)
(* Proof steps                                                           *)
(* ===================================================================== *)
(* The following functions are used to build individual steps of a       *)
(* declarative proof. In general, they use default_stepinfo as the       *)
(* step_info, which is then augmented by additional functions such as    *)
(* at and from. These additional functions may alter the justification   *)
(* function (by explicitly using tactics), change the term associated    *)
(* with the proof step --- such as the term being assumed --- or change  *)
(* the choice of theorems to be used for justification. However, they    *)
(* ultimately decide how to turn the final stepinfo into a tactic.       *)          
(* ===================================================================== *)

(* Pure sugar. Should follow per. *)  
let (cases: step) =
  (fun _ -> failwith "cases"),default_stepinfo None;;

(* Merely associates a term with this step. Useful with per. *)
let (suppose': (goal -> term) -> step) =
  fun t -> (fun _ -> failwith "suppose"),default_stepinfo (Some t);;

(* All considered variables depend on the goal, and therefore we can
   presumably infer types based on the goal. All variables are bound
   existentially to the st term. The existential is then proven using
   the justification for this step, quantifiers are strippers with
   X_CHOOSE_THEN and the resulting theorem is put in the goal context
   at the appropriate place. *)
let (consider': (goal -> term) list -> step) =
  let T = `T` in
  fun tl' ->
  (fun (t',l,thl,just) (asl,w as g) ->
    let tl = map (fun t' -> t' g) tl' in
    let g' = ((asl @ (map (fun t -> ("",REFL t)) tl)),w) in
    let ex = itlist (curry mk_exists) tl
      (match t' with
         None -> failwith "consider"
       | Some t -> t g') in
    (SUBGOAL_THEN ex
       ((EVERY_TCL (map X_CHOOSE_THEN tl)) (N_ASSUME_TAC l)) THENL
     [just (thl g); ALL_TAC]) g),
  default_stepinfo (Some
    (fun g -> end_itlist (curry mk_conj)
      (map (fun t' -> let t = t' g in mk_eq(t,t)) tl')));;

(* Simple use of EXISTS_TAC, stripping existential quantifiers from the goal.
   No term is associated with this step, and no justification is used to
   prove it.. *)
let (take': (goal -> term) list -> step) =
  fun tl ->
    (fun _ g -> (MAP_EVERY EXISTS_TAC o map (fun t -> t g)) tl g),
    default_stepinfo None;;

(* In Freek's original paper, assume corresponded to the DISCH tactic and was
   therefore used only at the start of the proof of an implication. This is
   very inflexible for a general declarative proof language where we want to
   make hypotheses wherever we feel it convenient. Freek's improved version
   lets you do much cooler things. The trick is to add the supplied term as an
   assumed theorem to the hypotheses of the goal, by using DISJ_CASES_THEN2
   with "assume \/ ~assum" and then showing that ~assume solves the goal after
   rewriting it and sending it to the justification function with the other
   justifying theorems. Obviously, in the case when the goal is of the form
   "assume ==> ..." this will certainly work. More complex cases can be dealt
   with by supplying an explicit justification, which shows that the negation
   of the assumption also solves the goal.

   In Mizar Light, you can *justify* your assumptions!
*)

(* Compare the rewriting in this step to that in thus. If the first assumption
   gives an abbreviation, then assuming it will unfold the appreviation. If
   we follow the rewriting as in thus, then this won't happen.*)   
let (assume': (goal -> term) -> step) =
  fun t ->
    (fun (t',l,thl,just) g ->
       match t' with
         None -> failwith "assume"
       | Some t ->
           (DISJ_CASES_THEN2
              (fun th -> REWRITE_TAC[th] THEN
                 N_ASSUME_TAC l th)
              (fun th -> just ((REWRITE_RULE[] th)::(thl g)))
            (SPEC (t g) EXCLUDED_MIDDLE)) g),
    default_stepinfo (Some t);;

(* Accepts a term to prove and subgoals it. It is proven using the justification
   for this step, after which it is added to the assumptions at the stated
   position.
*)
let (have': (goal -> term) -> step) =
  fun t ->
    (fun (t',l,thl,just) g ->
       match t' with
         None -> failwith "have"
       | Some t ->
           (SUBGOAL_THEN (t g) (N_ASSUME_TAC l) THENL
            [just (thl g); ALL_TAC]) g),
    default_stepinfo (Some t);;

(* Mostly as have'. In fact, I'm not sure if the tactic couldn't have been more
   efficiently written as:

   SUBGOAL_THEN (t g) N_ASSUME_TAC l THENL
   [just (thl g);
       EVERY (map (fun th -> REWRITE_TAC[EQT_INTRO th])
         (CONJUNCTS th))]

   Unlike have', the proven theorem is used to rewrite the exact term in the
   goal. *)
let (thus': (goal -> term) -> step) =
  fun t ->
    (fun (t',l,thl,just) g ->
       match t' with
         None -> failwith "thus"
       | Some t ->
           (SUBGOAL_THEN (t g) ASSUME_TAC THENL
            [just (thl g);
             POP_ASSUM (fun th ->
               N_ASSUME_TAC l th THEN
               EVERY (map (fun th -> REWRITE_TAC[EQT_INTRO th])
                 (CONJUNCTS th)))])
           g),
    default_stepinfo (Some t);;

(* Simple use of X_GEN_TAC, stripping quantifiers from the goal.
   No term is associated with this step, and no justification is used to prove it. *)
let (fix': (goal -> term) list -> step) =
  fun tl ->
    (fun _ g -> (MAP_EVERY X_GEN_TAC o (map (fun t -> t g))) tl g),
    default_stepinfo None;;

(* Introduces a local variable. The term at this step must be an assignment can be
   a functional assignment such as S x y = x + y, or a simple assignment such as
   X = 1. Justifications at this step are ignored. `?S. S = \x y. x + y` is
   trivially proven, S is obtained, and then used to produce the equality
   which is added at the required position.*)
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
           (SUBGOAL_THEN ex (X_CHOOSE_THEN lv
              (fun th -> (N_ASSUME_TAC l) (prove(eq,REWRITE_TAC[th])))) THENL
            [REWRITE_TAC[EXISTS_REFL];
             ALL_TAC]) g),
      default_stepinfo (Some t) in
    stp at [-1];;

let theorem = theorem' o parse_mterm;;
let suppose = suppose' o parse_mterm;;
let consider = consider' o map parse_mterm;;
let take = take' o map parse_mterm;;
let assume = assume' o parse_mterm;;
let have = have' o parse_mterm;;
let thus = thus' o parse_mterm;;
let fix = fix' o map parse_mterm;;
let set = set' o parse_mterm;;

let iff prfs = tactics [EQ_TAC THENL map steps prfs];;

let (otherwise: ('a -> step) -> ('a -> step)) =
  fun stp x ->
    let tac,si = stp x in
    ((fun (t,l,thl,just) g ->
       REFUTE_THEN (fun th ->
         tac (t,l,K ([REWRITE_RULE[] th] @ thl g),just)) g),
     si);;

let (thesis:mterm) = "thesis";;
let (antecedent:mterm) = "antecedent";;
let (opposite:mterm) = "opposite";;
let (contradiction:mterm) = "F";;

let hence = so thus;;
let qed = hence thesis;;

(* Interactive interface. *)
let h = g o parse_term;;
let f = e o step;;
let ff = e o steps;;
let ee = e o EVERY;;

(* Insert a trivial step? *)
let fp = f o (fun x -> x proof []);;

(* Additional combinators for Mizar Light. *)
module Di  = Treestream
module Dim = Monad.MakeLazyPlus(Di)

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
let (obviously : (thm Di.m -> thm Di.m) -> step -> step)
    = fun d (tac, (t,l,thl,just)) ->
      tac,
      (t,l,thl,
       fun thms ((hyps,g_tm) as g) ->
         let d_thms = Dim.of_list (hyps_with_set g thms) in
         let d_thms = Di.to_eager_thms !discovery_depth (d d_thms) in
         (just (d_thms @ thms)) g);;

(* Attempt to find the conjuncts in the goal and then rewrite. *)
let (clearly : (thm Di.m -> thm Di.m) -> step -> step)
    = fun d (tac, (t,l,thl,just)) ->
      tac,
      (t,l,thl,
       let j thms ((hyps,g_tm) as g) =
         let d_thms = Dim.of_list (hyps_with_set g thms) in
         let d_thms = Ll.find_all
           (fun tm thm -> aconv_ac [CONJ_ACI] tm (concl thm))
           (conjuncts g_tm)
           (Ll.concat (Ll.take !discovery_depth (Di.to_thms (d d_thms)))) in
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
    stp at [-1];;

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
  (fun (_,_,thl,_) g ->   
    REWRITE_TAC (assigns g @ map (REWRITE_RULE (assigns g)) (thl g)) g), default_stepinfo None

let case = case' o parse_mterm;;
let set = set' o parse_mterm;;
let take = take' o map parse_mterm;;

