(* ========================================================================= *)
(* Additions to the incidence discoverer, translating concrete claims of     *)
(* incidence into a form suitable for the rest of the incidence discovery.   *)
(*                                                                           *)
(*                                   Phil Scott                              *)
(*                                                                           *)
(*               Centre for Intelligent Systems and their Applications       *)
(*                             University of Edinburgh                       *)
(* ========================================================================= *)

(* Additions to the incidence discoverer, which abstracts concrete incidence
   claims. *)

module Incidence_discovery(Di : DISCOVERY) =
struct
  include Incidence_discovery(Di)
  module Di_m = Monad.MakeLazyPlus(Di)
  open Di_m

  let betcol =
    prove (`!A B C. between A B C
            ==> ?a. on_line A a /\ on_line B a /\ on_line C a`,
           MESON_TAC [g21]);;

  let betneqs =
    prove (`!A B C. between A B C
            ==> ~(A = B) /\ ~(A = C) /\ ~(B = C)`,
           MESON_TAC [g21]);;

  let add_bets b =
    Di_m.msum
      [b
      ;Di.rewrite [CONJ_ACI] (Di.rule1 betcol b)
      ;Di.rewrite [EQ_SYM_EQ] (Di.conjuncts (Di.rule1 betneqs b))]

  let intro_ncol = prove
    (`!A B C. ~(A = B) ==> on_line A a ==> on_line B a ==> ~on_line C a
     ==> ~(?a. on_line A a /\ on_line B a /\ on_line C a)`,
     MESON_TAC [g12]);;

  (* Note that you may have to explicitly have inequalities here,
     since this rule will not pick up discovered inequalities. We
     should have more mutual recursion here. *)
  let add_ncols b =
    unique 
      (Di_m.plus (Di.rewrite [CONJ_ACI] (Di.rule4 intro_ncol b b b b)) b)

  let intro_col = prove
    (`!A B C. on_line A a ==> on_line B a ==> on_line C a
     ==> (?a. on_line A a /\ on_line B a /\ on_line C a)`,
     MESON_TAC [])

  let add_cols b =
    maxima 
      (Di_m.plus (Di.rewrite [CONJ_ACI] (Di.rule3 intro_col b b b)) b)

  let intro_plane = prove
    (`!A B C D. on_plane A 'a ==> on_plane B 'a ==> on_plane C 'a
         ==> on_plane D 'a
         ==> (?'a. on_plane A 'a /\ on_plane B 'a /\ on_plane C 'a
                   /\ on_plane D 'a)`,
     MESON_TAC []);;

  let add_planes b =
    maxima 
      (Di_m.plus (Di.rewrite [CONJ_ACI] (Di.rule4 intro_plane b b b b)) b)

  let inferred = inferred o add_planes o add_cols o add_ncols o add_bets o unique 
    
  let pasch' = prove
    (`!A B D C E.
        between A D B 
     ==> ~(?a. on_line A a /\ on_line B a /\ on_line C a) 
     ==> ~(?a. on_line A a /\ on_line D a /\ on_line E a)
     ==> ~(?a. on_line C a /\ on_line D a /\ on_line E a)
     ==> (?'a. on_plane A 'a /\
               on_plane B 'a /\
               on_plane C 'a /\
               on_plane D 'a /\
               on_plane E 'a)
     ==> (?Fa. (?a. on_line D a /\ on_line E a /\ on_line Fa a) /\
               (between A Fa C \/ between B Fa C))`,
     REPEAT GEN_TAC THEN MP_TAC
       (SPECL [`A:point`;`B:point`;`C:point`
              ;`D:point`;`E:point`] pasch)
          THEN MESON_TAC [])

  let is_bet thm = fst (strip_comb (concl thm)) = `between`
    
  let dest_bet thm =
    let [a;b;c] = Bl.sort Pervasives.compare (snd (strip_comb (concl thm))) in
    a,b,c

  let new_point xs (a,b,c) =
    match Bl.find_all (not o C mem xs) [a;b;c] with
        [x] -> x

  let BET_SYM = prove
    (`between A B C <=> between C B A`,
     MESON_TAC [g21])
     
  let paschs bets base =
    let p (_,thm) (_,thm') =
      aconv (concl thm) (concl thm') in
    let conv = LAND_CONV (REWRITE_CONV [CONJ_ACI]) in
    Di.unique ~cmp:(fun thm thm' ->
      aconv (concl thm) (concl thm'))
      (Di.unique ~cmp:p
         (bets >>= (fun bet -> 
           let a,b,d = dest_bet bet in
           base.ncols >>= (fun ncol ->
             try
               let c = new_point [a;b;d] (Incidence.dest_ncol ncol) in
               let pasch' = SPECL [c] (MATCH_MP pasch' bet) in
               let pasch' =
                 MATCH_MP (CONV_RULE
                             (BINDER_CONV conv) pasch') ncol in
               base.ncols >>= (fun ncol ->
                 try 
                   let e = new_point [a;b;c;d] (Incidence.dest_ncol ncol) in
                   Di.return
                     (Bl.sort Pervasives.compare [a;b;c;d;e],
                      REWRITE_RULE [CONJ_ACI;BET_SYM]
                        (MATCH_MP (CONV_RULE conv (SPECL [e] pasch')) ncol))
                 with _ -> Di.zero ())
             with _ -> Di.zero ())))
           >>= (fun (pts,pasch') ->
             Di.rule1 pasch' base.ncols >>= (fun pasch' ->
               base.planes >>= (fun plane ->
                 try
                   Di.return (MATCH_MP pasch'
                             (Incidence.col_subset pts plane))
                 with _ -> Di.zero ()))))

  let by_pasch b =
    let base = inferred b in
    let bets = Di_m.filter is_bet b in
    paschs bets base

  let col_ncol_bot =
    let f col ncol =
      let a,b,c = Incidence.dest_ncol ncol in
      MP (NOT_ELIM ncol) (Incidence.col_subset [a;b;c] col) in
    lift2t f

  let bots bets base =
    let bet_nbet = prove
      (`between A B C ==> ~between B A C /\ ~between A C B`,
       MESON_TAC [g21;g23]) in
    let all =
      plus
        base.all
        (lift2 (fun eq thm -> PURE_ONCE_REWRITE_RULE [eq] thm)
           base.eqs base.all) in
    let bets =
      plus
        bets
        (lift2 (fun eq thm -> PURE_ONCE_REWRITE_RULE [eq] thm)
           base.eqs bets) in
    plus
      (contr all (plus all (conjuncts (rule1 bet_nbet bets))))
      (col_ncol_bot base.cols base.ncols)

  (* An inference rule which tries to discharge the hypotheses of Pasch's axiom. *)
  let pasch_on (a,b,c,d,e) chain =
    let base              = inferred chain in
    let pasch             = REWRITE_RULE [CONJ_ACI;swapbet] (SPECL [a;b;c;d;e] pasch) in
    let ants,conc         = dest_imp (concl pasch) in
    let plane :: ncol_tms = striplist dest_conj ants in
    let plane_thm =
      Ll.hd (Ll.concat (Di.to_thms (Di_m.filter
                                      (fun thm -> subset [a;b;c;d;e]
                                        (Incidence.dest_plane thm))
                                      base.planes))) in
    let ncol_thms =
      Ll.find_all (fun tm thm -> aconv tm (concl thm))
        ncol_tms (Ll.concat (Di.to_thms base.ncols)) in
    Di.return 
      (prove (conc,
              MATCH_MP_TAC (REWRITE_RULE ncol_thms pasch)
                THEN MESON_TAC [plane_thm]));;

  (* let run_pasch bets base = *)
  (*   function [] -> zero () *)
  (*     | v::vs -> *)
  (*       paschs bets base >>= *)
  (*         (fun p -> *)
  (*           let x,ex = dest_exists (concl p) in *)
  (*           let p' = ASSUME (vsubst [v,x] ex) in *)
  (*           let bots = *)
  (*             Id.to_dlist *)
  (*               (bots bets *)
  (*                  (Id.inferred *)
  (*                     (plus *)
  (*                        (Id.maxima (to_forced base.Id.all)) *)
  (*                        (Id.split p')))) in *)
  (*           Id.lift1 (fun b -> REWRITE_RULE [b]  *)
  (*           return (REWRITE_RULE [Ll.hd bots] p')) *)
end
