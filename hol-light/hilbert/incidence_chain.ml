(* Incidence discovery, but implemented using MATCH_MP, rewriting, and our
   point set rules. *)

module Incidence_chain =
struct
  let unset_lexer = unset_jrh_lexer

  (*  open Echo *)
  open LazyList
  module Bl =
    struct
      include List
      include BatList
    end
  open Chain

  let set_lexer = set_jrh_lexer

  let or_false f tm =
    tm = `F` or f tm
  
  let and_can f x =
    try
      f x
    with _ -> false 
  
  (* Filters. *)
  let is_neq, is_col, is_ncol, is_bet, is_nbet, is_plane, is_false =
    let is_neq tm = let (x,_) = dest_eq (dest_neg tm) in
      type_of x = `:point`
    and is_col tm =
      rator tm = `COLLINEAR` && Bl.length (dest_setenum (rand tm)) >= 3
    and is_ncol tm = rator (dest_neg tm) = `COLLINEAR` 
    and is_bet tm = fst (strip_comb tm) = `between`
    and is_nbet tm = let (b,pts) = strip_comb (dest_neg tm) in
      b = `between`
    and is_plane tm = rator tm = `PLANAR` && Bl.length (dest_setenum (rand tm)) >= 4
    and is_false tm = tm = `F`
    in
      or_false (and_can is_neq), or_false (and_can is_col),
    or_false (and_can is_ncol), or_false (and_can is_bet),
    or_false (and_can is_nbet), or_false (and_can is_plane),
    or_false (and_can is_false)

  let subset_rewrites = [EMPTY_SUBSET; IN_INSERT; INSERT_SUBSET]

  let chain_nd xss = sum (lift1 nd_rule xss)

  let contains p xs = not (is_empty (filter p xs))
    
  (* Chains based on applying individual incidence rules. *)

  (* COLLINEAR_UNION *)      
  let col_union cols =
    (chain_mp
       o unique (=)
       o pure_rewrite [EQ_SYM_EQ;INSERT_INSERT;INSERT_COMM
                      ;UNION_EMPTY;INSERT_UNION_EQ]
       o filter (fun tm -> is_binary "==>" tm && is_neq (lhand tm))
       o rewrite [IN_INSERT]
       o sum o lift1 conjuncts
       o pure_rewrite [FORALL_IN_INSERT;FORALL_AND_THM])
      (chain2 COLLINEAR_UNION cols cols)
      
  (* NON_COLL_INFER *)
  let ncol_col_ncol non_col_infer ncols cols =
    (chain_mp
       o pure_rewrite [EQ_SYM_EQ;INSERT_INSERT;INSERT_COMM
                      ;UNION_EMPTY;INSERT_UNION_EQ]
       o filter (fun tm -> is_binary "==>" tm && is_neq (lhand tm))
       o rewrite [IN_INSERT]
       o sum o lift1 conjuncts
       o pure_rewrite [FORALL_IN_INSERT;FORALL_AND_THM])
      (chain2 non_col_infer cols ncols)

  (* PLANAR_UNION *)
  let plane_union planes ncols =
    (pure_rewrite [INSERT_UNION_EQ;UNION_EMPTY;INSERT_COMM;INSERT_INSERT] 
      o filter (not o is_imp)
      o rewrite [EMPTY_SUBSET;IN_INSERT;INSERT_SUBSET]
      o pure_rewrite [SUBSET_INTER])
      (chain3 PLANAR_UNION planes planes ncols)

  (* INTER_COLLINEAR_PLANAR *)
  let inter_col_plane cols =
    (pure_rewrite [INSERT_UNION_EQ;UNION_EMPTY;INSERT_COMM;INSERT_INSERT] 
       o filter (not o is_imp)
       o filter (not o is_forall)
       o rewrite [IN_INSERT]
       o sum o lift1 conjuncts
       o pure_rewrite [FORALL_IN_INSERT])
      (chain2 INTER_COLLINEAR_PLANAR cols cols)

  (* COLL_PLANAR_UNION *)
  let col_plane_union cols planes =
    (chain_mp
      o pure_rewrite [EQ_SYM_EQ;INSERT_UNION_EQ;UNION_EMPTY
                     ;INSERT_COMM;INSERT_INSERT]
      o filter (fun tm -> is_binary "==>" tm &&
                  is_neq (lhand tm))
      o rewrite [IN_INSERT]
      o sum o lift1 conjuncts
      o pure_rewrite [FORALL_IN_INSERT;FORALL_AND_THM])
      (chain2 COLL_PLANAR_UNION cols planes)

  (* COLLINEAR_INTERSECT *)
  let col_intersect cols ncols = 
    (rewrite [IN_INSERT]
       o sum o lift1 conjuncts
       o pure_rewrite [FORALL_IN_INSERT;FORALL_AND_THM]       
       o rewrite []
       o lift1 ((CONV_RULE o BINDER_CONV o BINDER_CONV o LAND_CONV) 
                  (PURE_REWRITE_CONV [EMPTY_SUBSET;IN_INSERT;INSERT_SUBSET
                                     ;UNION_EMPTY;INSERT_UNION_EQ])))
      (chain3 COLLINEAR_INTERSECT cols cols ncols)

  let col_ncol_neq cols ncols =    
    (rewrite [IN_INSERT;EQ_SYM_EQ]
       o sum o lift1 conjuncts
       o pure_rewrite [FORALL_IN_INSERT;FORALL_AND_THM]
       o rewrite []
       o lift1 ((CONV_RULE o LAND_CONV)
              (PURE_REWRITE_CONV [EMPTY_SUBSET;IN_INSERT;INSERT_SUBSET
                                 ;UNION_EMPTY;INSERT_UNION_EQ])))
      (chain2 COL_NCOL_NEQ cols ncols)

  let monitor () = unique (=) (disjuncts (sum (lift1 conjuncts (monitor ()))))
      
  let ncol_plane =
    prove (`!P Q R. ~COLLINEAR {P,Q,R} ==> PLANAR {P,Q,R}`,
           REWRITE_TAC [PLANAR_LESS_FOUR])

  let bet_col =
    prove (`!A B C. between A B C ==> COLLINEAR {A,B,C}`,
           REWRITE_TAC [COLLINEAR_DEF; FORALL_IN_INSERT; NOT_IN_EMPTY]
             THEN MESON_TAC [g21])

  let col_contr =
    prove (`!As A B C. COLLINEAR As
           ==> ~COLLINEAR {A, B, C}
           ==> ~({A, B, C} SUBSET As)`,
           MESON_TAC [COLLINEAR_SUBSET])

  let bet_nbet = prove (`!A B C. between A B C ==>
                          ~between A C B /\ ~between C A B`,
                        MESON_TAC [SWAP_BETWEEN;g23])

  let on f p x y =
    p (f x) (f y)
    
  let compare_set x y =
    if rator x = rator y then
      on (of_list o dest_setenum o rand)
        subset x y
    else x < y
    
  let subst eqs xs =
    plus xs (sum (lift2 (fun eq x ->
                           let y = SUBS [eq] x in
                             if x = y then nil else
                               singleton (PURE_REWRITE_RULE
                                            [INSERT_INSERT; INSERT_COMM]
                                            y))
                    eqs xs))
      
  (* The complete inference system *)
  let inferred b =
    let rec cols = lazy
      (next
         (unique (=)
            (subst eqs
               (fix (fun cols ->
                       maxima compare_set
                         (difference compare_set
                            (filter is_col
                               (col_union cols neqs))
                               cols))
                  (plus 
                     (filter is_col b)
                     (rewrite [INSERT_COMM;INSERT_INSERT]
                        (chain1 bet_col bets)))))))

    and ncols = lazy
      (next
         (unique (=)
            (subst eqs
               (fix (fun ncols ->
                       filter is_ncol
                         (merge_all [ncol_col_ncol NON_COLL_INFER1
                                       ncols (delay cols) neqs
                                    ;ncol_col_ncol NON_COLL_INFER2
                                      ncols (delay cols) neqs
                                    ;ncol_col_ncol NON_COLL_INFER3
                                      ncols (delay cols) neqs]))
                  (filter is_ncol b)))))

    and bet_neqs =
      prove (`!A B C. between A B C ==> ~(A = B) /\ ~(A = C) /\ ~(B = C)`,
             MESON_TAC [g21])

    and bets = lazy (next (unique (=) (subst eqs (filter is_bet b))))

    and nbets = lazy
      (next (unique (=)
               (plus
                  (pure_rewrite [SWAP_BETWEEN]
                     (sum (lift1 conjuncts (chain1 bet_nbet bets))))
                  (subst eqs (filter is_nbet b)))))

    and neqs = lazy
      (next
         (unique (=)
            (subst eqs
               (rewrite [EQ_SYM_EQ]
                  (unique (=)
                     (merge_all [filter is_neq b
                                ;(sum o lift1 conjuncts o chain1 bet_neqs)
                                  bets
                                ;(sum o lift1 conjuncts
                                    o chain1 NON_COLL_NEQ) ncols
                                ;filter is_neq
                                  (col_ncol_neq cols ncols)]))))))
      
    and planes = lazy
      (next
         (maxima compare_set
            (subst eqs
               (fix
                  (fun planes ->
                     maxima compare_set
                       (difference compare_set
                          (filter is_plane
                             (plus (plane_union planes ncols)
                                (col_plane_union cols planes neqs)))
                          planes))
                  (merge_all [filter is_plane b
                             ;filter is_plane (inter_col_plane cols)
                             ;chain1 COLLINEAR_PLANAR cols
                             ;chain1 ncol_plane ncols])))))
      
    and eqs = lazy
      (next (Chain.delay
               (unique (=)
                  (filter is_eq (col_intersect cols ncols)))))

    and bots = lazy
      (next
         (unique (=)
            (filter ((=) `F`)
               (merge_all
                  [rewrite [INSERT_SUBSET; IN_INSERT; EMPTY_SUBSET]
                     (chain2 col_contr cols ncols)
                  ;contr eqs neqs
                  ;contr bets nbets]))))
        
    and paschs =
      let chain_nd xss yss =
        chain_nd (pure_rewrite [INSERT_COMM] (chain_mp xss yss)) in
      lazy
        (next
           (unique (=)
              (filter is_exists
                 (rewrite [INSERT_SUBSET;EMPTY_SUBSET;
                           IN_INSERT;SWAP_BETWEEN]
                    (chain_mp
                       (chain_mp
                          (chain_nd
                             (chain_nd
                                (chain_nd
                                   (chain_nd (return pasch_col) bets)
                                   ncols)
                                ncols)
                             ncols)
                          ncols)
                       planes)))))
    in cols, ncols, bets, nbets, planes, eqs, neqs, bots, paschs

  let all_inferred () =
    let cols, ncols, bets, nbets, planes, eqs, neqs, bots, paschs =
      inferred (monitor ()) in
      merge_all [cols;ncols;bets;nbets;planes;eqs;neqs;bots;paschs]

end
