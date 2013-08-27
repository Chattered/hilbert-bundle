(* =============================================================================== *)
(*                                   Phil Scott                                    *)
(*               Centre for Intelligent Systems and their Applications             *)
(*                             University of Edinburgh                             *)
(*                                                                                 *)
(* This gives a convenient representation of finite linear orders, and tactics     *)
(* to extract data.                                                                *)
(* =============================================================================== *)

let SWAP_BETWEEN = prove (`!A B C. between A B C <=> between C B A`,
			  MESON_TAC [g21]);;

(* Shift will move the left most point to the origin A, while trans is transitivity
   if we take ABC to mean B < C wrt A. *)
let shift,trans =
  prove (`!A B C D. between A B C /\ between A C D ==> between B C D`,
	 MESON_TAC [five2]),
  prove (`!A B C D. between A B C /\ between A C D ==> between A B D`,
	 MESON_TAC [five2]);;

(* Given a list of points [A;B;C;D;...Y;Z], returns the conjunction
   `between A B C /\ between A C D /\ ... /\ between A Y Z` *)
let mk_order = function
    (p :: ps) ->
      let bet a b c =
	mk_comb (mk_comb (mk_comb (`between`,a), b), c) in
      let rec order_on = function
	  q :: r :: [] -> bet p q r
	| q :: r :: qs -> mk_conj (bet p q r, order_on (r :: qs))
	| _ -> `T` in
	order_on ps
  | _ -> `T`;;

(* Variant of dest_conj. *)
let dest_conj' tm =
  if is_conj tm then dest_conj tm else (tm, `T`);;

(* Variant of DEST_CONJ. *)
let DEST_CONJ' thm =
  if is_conj (concl thm) then (CONJUNCT1 thm, CONJUNCT2 thm)
  else (thm, TRUTH);;

(* Returns the triple of points in `between A B C`. *)
let dest_bet bet =
  let [a;b;c] = snd (strip_comb bet) in
    a,b,c;;

(* Returns the list of points in the order  *)
let dest_order term =
  let rec last_pts tm r =
    if is_conj tm then 
      let (bet,tm') = dest_conj tm in
	last_pts tm' (snd (dest_comb bet) :: r)
    else snd (dest_comb tm) :: r in
  let bet = fst (dest_conj' term) in
  let (a,b,c) = dest_bet bet in
    a :: b :: rev (last_pts term []);;

let rec map_thread f y = function
    [] -> (y, [])
  | x :: xs -> let (y',z) = f y x in
    let (y, zs) = map_thread f y' xs in
      (y, z :: zs);;

let disj_assoc = [TAUT `P \/ P <=> P`; TAUT `(P \/ Q) \/ R <=> P \/ Q \/ R`;
                  TAUT `P \/ Q \/ R <=> R \/ Q \/ P`
                  ; TAUT `P \/ P \/ Q <=> P \/ Q`];;

(* Given `between PQR`, we use shift to produce the new goals APQ AQR, from which
   PQR follows by transitivity. We destroy conjuncts in 'order' until we reach APX
   where P and X are adjacent, and then bring Q towards X by applying trans to
   successive conjuncts of order. The remaining conjuncts of order will then bring R
   towards Q. Special cases are needed when one of P or R is the origin, in which
   case we just use trans to bring the other point towards Q.

   The algorithm creates a fully deterministic tactic needing only one pass of the
   conjuncts in 'order'. *)
let split_order pred order =
  let rec f bets order =
    let b, order' = DEST_CONJ' order in
    let p',q',r' =
      try
	dest_bet (concl b)
      with  _ -> raise (Failure "Cannot derive betweeness from order.") in
      if pred p' q' r' then bets, order
      else f (b :: bets) order' in
    f [] order

let from_canon order bet =
  let (origin, _, _) =
    dest_bet (fst (dest_conj' (concl order))) in
  let p,q,r = dest_bet bet
  and find_bet pred = snd o split_order pred 
  in let rec transit order q =
      let (b, order') = DEST_CONJ' order in
      let (_,q',r') =
	try
	  dest_bet (concl b)
	with  _ -> raise (Failure "Cannot derive betweeness from order.") in
	if q = r' then (order', ACCEPT_TAC b)
	else
	  (I F_F
	     (fun tac -> MATCH_MP_TAC trans THEN EXISTS_TAC r' THEN CONJ_TAC THENL
		[ACCEPT_TAC b; tac])) (transit order' q) in
      if p = origin then
	prove (bet, snd (transit (find_bet (fun _ q' _ -> q = q') order) r))
      else if r = origin then
	prove (bet, SUBST1_TAC (SPECL [p;q;r] SWAP_BETWEEN)
		 THEN snd (transit (find_bet (fun _ q' _ -> q = q') order) p))
      else
	let order' = (find_bet (fun _ q' _ -> p = q' or r = q') order) in
	let _, q', _ =
	  try
	    dest_bet (fst (dest_conj' (concl order')))
	with  _ -> raise (Failure "Cannot derive betweeness from order.") in
	let first_tac, pts =
	  if q' = r then
	    SUBST1_TAC (SPECL [p;q;r] SWAP_BETWEEN), [q;p]
	  else ALL_TAC, [q;r] in
	  prove (bet, 
		 first_tac THEN
		   MATCH_MP_TAC shift THEN EXISTS_TAC origin
		   THEN CONJ_TAC THENL snd (map_thread transit order' pts));;

let swap_bet bet =
  let (a,b,c) = dest_bet (concl bet) in
    EQ_MP (SPECL [a;b;c] SWAP_BETWEEN) bet;;

(* Given ACDEF and BAC, we want to derive BACDEF which requires changing the
   origin in ACDEF. five1 achieve this. *)
let change_origin bet order =
  let f b1 b2 =
    DEST_CONJ' (MATCH_MP five1 (CONJ b1 (fst (DEST_CONJ' b2)))) in
    end_itlist CONJ (snd (map_thread f bet (CONJUNCTS order)));;

(* The following did not make the thesis, since I moved over to using
   ORDER_TAC. *)

(* Nasty case-splitting. If bet is a three-point ordering with origin A, and,
   assuming this origin, bet < bet', then we return the four point ordering
   with origin A. *)
    
(* let order bet bet' = *)
(*   let a,b,c = dest_bet (concl bet) *)
(*   and a',b',c' = dest_bet (concl bet') in *)
(*     if b' = c then *)
(*       begin *)
(* 	if a = a' then Some (CONJ bet bet') *)
(* 	else if a  = c' then Some (CONJ bet (swap_bet bet')) *)
(* 	else if b  = a' then *)
(* 	  Some (CONJ bet (CONJUNCT2 (MATCH_MP five1 (CONJ bet bet')))) *)
(* 	else if b  = c' then *)
(* 	  Some (CONJ bet (CONJUNCT2 (MATCH_MP five1 (CONJ bet (swap_bet bet'))))) *)
(* 	else None *)
(*       end *)
(*     else *)
(*       if b = a' && c = c' then *)
(* 	let sbet', sbet = *)
(* 	  CONJ_PAIR (MATCH_MP five2 (CONJ (swap_bet bet') (swap_bet bet))) *)
(* 	in Some (CONJ (swap_bet sbet) (swap_bet sbet')) *)
(*       else if b = c' && c = a' then *)
(* 	let sbet', sbet = *)
(* 	  CONJ_PAIR (MATCH_MP five2 (CONJ bet' (swap_bet bet))) *)
(* 	in Some (CONJ (swap_bet sbet) (swap_bet sbet')) *)
(*       else None;; *)

let five2_rev bet bet' =
  uncurry CONJ
    ((swap_bet F_F swap_bet)
       (CONJ_PAIR (MATCH_MP five2 (CONJ (swap_bet bet) (swap_bet bet')))));;

let swap_order order =
  let rec revconjs conj lst =
    if is_conj (concl conj) then
      let p,q = CONJ_PAIR conj in
	revconjs q (p :: lst)
    else conj :: lst in
  let f b1 b2 =
    let b1',b2' = DEST_CONJ' (MATCH_MP five2 (CONJ b2 b1)) in
      b1', swap_bet b2'
  and conj::conjs = revconjs order [] in
  let bet, bets = map_thread f conj conjs in
    end_itlist CONJ (bets @ [swap_bet bet]);;

let rec insert_order order bet =
  let mk_bet p q r = mk_comb (mk_comb (mk_comb (`between`, p), q), r) 
  and origin :: (m :: ps as pts) = dest_order (concl order)
  and a,b,c = dest_bet (concl bet) in
    if can (from_canon order) (concl bet) then order else
      if a = origin then
	if c = m then
	  (* Case AXB ABCDEF *)
	  CONJ bet order 
	else raise (Failure "Cannot insert.")
      else if b = last pts then
	insert_order (swap_order order) (swap_bet bet)
      else if b = origin then
	if mem c pts then
	  if c = m then
	    (* Case FAX AXBCDE *)
	    CONJ bet (change_origin bet order)
	  else
	    (* Case FAX ABCDXE *)
	    let bet' =
	      CONJUNCT2 (five2_rev (from_canon order (mk_bet origin m c)) bet)
	    in CONJ bet' (change_origin bet' order)
	else if mem a pts then
	  (* Case XAF ABCDXE *)
	  insert_order order (swap_bet bet)
	else raise (Failure "Cannot insert.")
      else if b = last pts then
	if mem c pts then
	  (* Case XAF BCDXEA *)
	  insert_order (swap_order order) (swap_bet bet)
	else if mem a pts then
	  (* Case FAX BCDXEA *)
	  insert_order (swap_order order) bet
	else
	  let (a,c,bet) =
      	    try
      	      if find (fun x -> x = a or x = c) pts = a then (a,c,bet)
      	      else (c,a,swap_bet bet)
      	    with Not_found -> raise (Failure "Cannot insert.") in
	  let (bets, order') =
      	    split_order (fun _ b' c' -> a = b' && c = c') order
	  in if is_conj (concl order') then
      	      let (toreplace, remaining) = CONJ_PAIR order'
      	      in let (r,l) = CONJ_PAIR (five2_rev bet toreplace)
      	      in CONJ l (CONJ r (itlist CONJ bets remaining))
      	    else let (r,l) = CONJ_PAIR (five2_rev bet order')
      	    in CONJ l (CONJ r (end_itlist CONJ bets))
      else raise (Failure "Cannot insert.");;

(* Derive all chains from a list of betweeness claims. *)	
(* Doesn't keep only the maximal sets. Bl.sort is doing a sort of the terms, not
   the lists, and some of the terms are not canonical in terms of starting with
   the smallest endpoint. *)
let chains bets =
  let try_insert bet order =
    try
      insert_order order bet
    with Failure "Cannot insert." -> order in
  let f = itlist try_insert bets in 
  let cs = map f bets in
    Bl.unique ~cmp:(fun ord ord' ->			
			subset (Bl.sort (dest_order (concl ord)))
			  (Bl.sort (dest_order (concl ord')))) (Bl.sort cs);;

let pairneqs =
  let f (x,y) = [x;y] in
    map (f o dest_eq o dest_neg) 
      
let pts_of_neqs neqs =
  Bl.unique (Bl.flatten neqs)

let mapf f xs = Bl.flatten (map f xs)

  

(* clear_neqs takes a list of point undesirable point inequalities. Our goal is to
   find sets of points which, if thrown out of the context, would eliminate
   all of the inequalities. For instance, given ~(A=B) and ~(A=C), we could either
   drop [A], or drop [B;C]. *)
let rec clear_neqs =
  function
    [] -> [[]]
  | neqs ->
      let f p =
	map (fun res -> p :: res) (clear_neqs (filter (not o mem p) neqs))
      in mapf f (pts_of_neqs neqs);;

