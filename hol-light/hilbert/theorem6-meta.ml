(* The strategy is as follows: Our base case is a three point collinear set, giving
   the orderings ABC, ACB and BAC from Theorem 4. In the recursive case, say we
   have ABCDEF. We then generate all possible orderings of the five points
   BCDEF. Without loss of generality, assume this is in normal form.  and now
   generate all orderings of ACDEF consistent with BCDEF:

   B C D E F
  AB   D E F
   B A D E F
   B   DAE F
   B   D EAF
   B   D E FA

   The case which does not begin with B is dealt with by using five2 on
   DCB and DBA to give CBA and then conjoining ABC to
   change_origin ABC (CONJUNCTS BCDEF) to yield ABCDEF.

   The case BADEF needs a case-split on Theorem 4:
     ABC -> as above
     BAC -> conjoin to BCDEF to give BACDEF
     BCA -> conjoin to BADEF to give BCADEF

   All remaining cases are dealt with by adding BCD onto (say) BDEFA.
*)   

let dest_disj' tm =
  if is_disj tm then dest_disj tm else (tm, `F`);;

(* Applies an inference rule to every disjunct in a disjunction, returning a
   new disjunction. *)
let rec disj_f f thm =
  if is_disj (concl thm) then
    let (d1,d2) = dest_disj (concl thm) in
    let thm1, thm2 =
      f (ASSUME d1), disj_f f (ASSUME d2) in
    let dthm1, dthm2 =
      DISJ1 thm1 (concl thm2), DISJ2 (concl thm1) thm2 in
      DISJ_CASES thm dthm1 dthm2
  else f thm

let five2' =
  prove (`!A B C D. between B C D /\ between A B D ==>
           between A B C`, MESON_TAC [five2; SWAP_BETWEEN]);;

let disj3 thm t1 t2 t3 =
  let [d1;d2;d3] = disjuncts (concl thm) in
  let [dt1;dt2;dt3] = [t1 (ASSUME d1); t2 (ASSUME d2); t3 (ASSUME d3)] in
  let [d1';d2';d3'] = [concl dt1; concl dt2; concl dt3] in
    DISJ_CASES
      thm 
      (DISJ1 dt1 (mk_disj (d2',d3')))
      (DISJ_CASES
	 (ASSUME (mk_disj (d2,d3)))
	 (DISJ2 d1' (DISJ1 dt2 d3'))
	 (DISJ2 d1' (DISJ2 d2' dt3)));;      

let mk_bet p q r = mk_comb (mk_comb (mk_comb (`between`, p), q), r)

let rec first_can f = function
    [] -> []
  | x :: xs -> try [f x] with _ -> first_can f xs  

let BETWEEN_NEQ = prove (`!A B C. between A B C ==> ~(A = B) /\ ~(A = C) /\ ~(B = C)`,
			 MESON_TAC [g21])

let four' = prove (`!A B C. (?a. on_line A a /\ on_line B a /\ on_line C a)
                      ==> ~(A = B) ==> ~(A = C) ==> ~(B = C)
                      ==> between A B C \/ between B A C \/ between B C A`,
                   MESON_TAC [four]);;
  
(* The chief case splitting used in the recursive case of Theorem 6. *)      
let rec six_cases col order1 order2 =
  let a1,b1,c1 = dest_bet (fst (dest_conj' (concl order1)))
  and a2,b2,c2 = dest_bet (fst (dest_conj' (concl order2))) in
    if a1 = a2 then
      if c1 = c2 then
	disj3
	  (UNDISCH_ALL
	     (REWRITE_RULE 
		[Incidence.col_subset (Bl.sort [b2;a2;b1]) col;CONJ_ACI]
		(SPECL [b2;a2;b1] four')))
	  (fun abc -> CONJ abc (change_origin abc order1))
	  (fun bac -> CONJ bac order1)
	  (fun bca -> CONJ bca order2)
      else CONJ (fst (DEST_CONJ' order1)) order2
    else
      if a1 = b2 then
	let abc =
	  MATCH_MP five2' (CONJ (fst (DEST_CONJ' order1))
			     (fst (DEST_CONJ' order2))) in
	  CONJ abc (change_origin abc order1)
      else
	six_cases col order1 (swap_order order2);;

(* Derive a contradiction from order and nbet. *)
let refute_order order nbet =
  MP (NOT_ELIM nbet) (from_canon order (dest_neg (concl nbet)))

let or_F = [TAUT `F \/ P <=> P`; TAUT `P \/ F <=> P`];;

(* Uses f providing thm is not F *)
let maybe_infer f thm =
  if concl thm = `F` then thm else f thm;;

let disj_f' f = maybe_infer (disj_f f);;

(* Delete orderings which are inconsistent with betweeness claims. *)
let resolve nbets orders =
  PURE_REWRITE_RULE or_F
    (disj_f'
       (maybe_infer
	  (fun order ->
	     let rec find_refute = function
		 [] -> order
	       | nb :: nbs -> 
		   try refute_order order nb
		   with Failure _ -> find_refute nbs in
	    find_refute nbets))
       orders);;

let g23d bet =
  [MATCH_MP g23 bet; MATCH_MP g23 (swap_bet bet)];;

let six bets nbets pts =
  let pts = Bl.sort pts in
  let mk_online pt = mk_comb (mk_comb (`on_line`, pt), `a:line`) in
  let col = 
    ASSUME (mk_exists (`a:line`,end_itlist (curry mk_conj)
      (map mk_online pts))) in
  let rec six nbets = function
    [a;b;c] ->
      resolve nbets
	(UNDISCH_ALL
	   (REWRITE_RULE ([Incidence.col_subset (Bl.sort [a;b;c]) col;
			   CONJ_ACI; SWAP_BETWEEN])
	      (SPECL [a;b;c] four')))
    | p :: q :: ps as pts ->
      resolve nbets
	(PURE_REWRITE_RULE disj_assoc
	   (disj_f'
	      (fun order ->
		let _,b,_ = dest_bet (fst (dest_conj' (concl order))) in
		let order' =
		  six (Bl.flatten (map g23d (CONJUNCTS order)) @ nbets) (Bl.remove pts b) in
		disj_f' (maybe_infer (six_cases col order)) order')
	      (six nbets (q :: ps))))
    | _ -> TRUTH
  in six (Bl.flatten (map g23d bets) @ nbets) pts;;

(* Derive an inequality from an ordering. *)
let neq_from_order neq order =
  let (p,q) = dest_eq (dest_neg neq) in
  let pts = dest_order (concl order) in
  let r = find (fun x -> not (x = p or x = q)) pts in
  let f x ps = if x = p or x = q or x = r then x :: ps else ps in
  match Bl.fold_right f pts [] with
      [p;q;r] ->
	find ((=) neq o concl)
	  (CONJUNCTS (MATCH_MP BETWEEN_NEQ (from_canon order (mk_bet p q r))))
    | _ -> raise (Failure "Cannot derive inequality.")

let SIX_TAC pts thms =
  let is_bet  tm = rator (rator (rator tm)) = `between` in
  let is_nbet    = is_bet o dest_neg in
  let conjs      = Bl.flatten (map CONJUNCTS thms) in
    MESON_TAC (six
                 (filter (and_can (is_bet o concl)) conjs)
                 (filter (and_can (is_nbet o concl)) conjs)
                 pts::thms);;
  
(* Assuming that thm is an implication whose hypotheses are inequalities, delete
   those equalities by deriving them from bets. We might be better off just deriving
   all inequalities from the betweeness claims in one go, rather than on-demand.
   That way, the inequalities can be fed directly into the algorithm. *)
(* let remove_neqs bets thm = *)
(*   if is_imp (concl thm) then *)
(*     let cs = chains bets in *)
(*     let f neq neqs = first_can (neq_from_order neq) cs @ neqs in *)
(*     let neqs = *)
(*       itlist f (striplist dest_conj (fst (dest_imp (concl thm)))) [] *)
(*     in REWRITE_RULE neqs thm *)
(*   else thm;; *)

(* (\* Runs six but adds non-betweeness claims from non-betweeness and eliminates inequality hypotheses *)
(*    via the betweeness claims. *\) *)
(* let six' col neqs bets pts = *)
(*   let hyps = Bl.unique *)
(*     (hyp col @ Bl.flatten (map hyp neqs) @ Bl.flatten (map hyp bets)) in *)
(*   let six_thm = six col neqs bets pts in *)
(*   let cases =  *)
(*     REWRITE_RULE [CONJ_ACI; SYM IMP_CONJ; EQ_SYM_EQ] *)
(*       (itlist (fun hyp thm -> if mem hyp hyps then thm else DISCH hyp thm) *)
(* 	 (hyp six_thm) six_thm) in *)
(*     disj_f (remove_neqs bets) cases *)
  
(* We would like to design another version of six which runs six' with
   the largest possible collinear sets which leave no inequality hypotheses.
   If we represent a list of inequalities by a list of two-element lists, then
   the following Haskell code produces the maximal collinear sets:

   import Data.List
   import Data.Function

   pts neqs = nub (concat neqs)
    
   f [] = [[]]
   f neqs = do p <- pts neqs
               let neqs' = map (delete p) neqs
               res <- f (filter ((> 1) . length) neqs')
               return $ p : res

   superset x y = sort (x `intersect` y) == sort y

   g neqs = nubBy superset (sortBy (compare `on` length) $ f neqs)

   h col neqs = map (deleteAll col) (g neqs)             
       where deleteAll xs ys = foldr delete xs ys *)
   
(* Return the supremums according to a partial order of a list ordered consistent
   with that ordering. *)
(* let rec subs f = function *)
(*     [] -> [] *)
(*   | (x :: xs) -> x :: subs f (filter (not o f x) xs) *)
	   
(* let subset' x y = *)
(*   let (x',y') = (Bl.sort x, Bl.sort y) in *)
(*     not (x = y) && List_set.intersect x' y' = x';; *)

(* (\* Retain the smallest of a list of sets. *\) *)
(* let smallest_sets neqs = subs subset' *)
(*   (Bl.sort ~cmp:(fun x y -> compare (length x) (length y)) (clear_neqs neqs));; *)

(* (\* Given a collinear claim and a set of inequalities, return all subsets of the *)
(*    collinear set for which the inequalities do not apply. *\) *)
(* let clear_neqs_col col neqs =  *)
(*   let removeAll xs ys = Bl.fold_left Bl.remove xs ys in *)
(*     map (removeAll col) (smallest_sets neqs);; *)

(* (\* Version of six which, given a collinear set, a list of inequalities, and a *)
(*    list of betweeness claims, returns all unconditional point orderings. *\) *)
(* let six'' col neqs bets = *)
(*   let pts = (dest_setenum o snd o dest_comb o concl) col in *)
(*   let (nc, _) = dest_imp (concl (six' col neqs bets pts)) in *)
(*   let pts = dest_setenum (snd (dest_comb (concl col))) in *)
(*   let colsets = filter ((<) 2 o length) (clear_neqs_col pts (pairneqs (conjuncts nc)))  *)
(*   in map (six' col neqs bets) colsets;; *)
