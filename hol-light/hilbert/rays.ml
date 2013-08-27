(* ========================================================================= *)
(* Theory of rays.                                                           *)
(*                                                                           *)
(*                                   Phil Scott                              *)
(*                                                                           *)
(*               Centre for Intelligent Systems and their Applications       *)
(*                             University of Edinburgh                       *)
(* ========================================================================= *)

(* We quotient a same side relation. All theorems are analogous to those for
   half planes. *)

(* We follow the approach used to define half planes. The type is that of
   directed line-segments. *)
let dsegment =
  new_type_definition "dsegment" ("mk_dsegment","dest_dsegment")
    (prove (`?(P:point,Q). ~(P = Q)`, REWRITE_TAC [EXISTS_PAIRED_THM]
      THEN MESON_TAC [EXISTS_PAIRED_THM;g13a]));;

let dest_dsegment = prove
  (`!P Q ds. dest_dsegment ds = P,Q ==> ~(P=Q)`,
   REPEAT GEN_TAC
     THEN DISCH_TAC THEN FIRST_ASSUM (MP_TAC o AP_TERM `mk_dsegment`)
     THEN DISCH_THEN (MP_TAC o AP_TERM `dest_dsegment`)
     THEN REWRITE_TAC [dsegment] THEN ASM_REWRITE_TAC []
     THEN MESON_TAC
     [REWRITE_RULE [FORALL_PAIRED_THM; LAMBDA_PAIR_THM] dsegment]);;

let same_side = new_definition
  `same_side ds ds' <=>
    let O,P = dest_dsegment ds
    and O',Q = dest_dsegment ds' in
    O = O' /\ (?a. on_line O a /\ on_line P a /\ on_line Q a)
    /\ (P = Q \/ between O P Q \/ between O Q P)`;;

(* Should have made this the definition. *)
let ugh_redundancy = prove
  (`same_side ds ds'
      <=> let O,P = dest_dsegment ds
          and O',Q = dest_dsegment ds' in
             O = O' /\ (P = Q \/ between O P Q \/ between O Q P)`,
          REWRITE_TAC [same_side] THEN REPEAT LET_TAC
            THEN MESON_TAC [g11_weak;g21]);;

let same_side_unfold = prove
  (`!ds ds'. same_side ds ds'
       <=> ?P Q O.
             dest_dsegment ds = O,P /\ dest_dsegment ds' = O,Q
               /\ ?a. on_line O a /\ on_line P a /\ on_line Q a
               /\ (P = Q \/ between O P Q \/ between O Q P)`,
   REPEAT GEN_TAC THEN REWRITE_TAC [same_side] THEN LET_TAC
     THEN REWRITE_TAC [PAIR_EQ] THEN MESON_TAC []);;

let same_side_refl = prove
  (`!ds. same_side ds ds`,
   GEN_TAC THEN REWRITE_TAC [same_side] THEN LET_TAC
     THEN POP_ASSUM (ASSUME_TAC o MATCH_MP dest_dsegment)
     THEN MESON_TAC [g11_weak]);;

let same_side_sym = prove
  (`!ds dt. same_side ds dt <=> same_side dt ds`,
   REPEAT GEN_TAC THEN REWRITE_TAC [same_side] THEN LET_TAC
     THEN EVERY_ASSUM (ASSUME_TAC o MATCH_MP dest_dsegment) 
     THEN CONV_TAC (TOP_DEPTH_CONV let_CONV) THEN MESON_TAC [BET_SYM]);; 

let same_side_trans = prove
  (`!ds dt du. same_side ds dt /\ same_side dt du ==> same_side ds du`,
   REPEAT GEN_TAC THEN REWRITE_TAC [same_side] THEN LET_TAC
     THEN EVERY_ASSUM (ASSUME_TAC o MATCH_MP dest_dsegment) THEN LET_TAC
     THEN CONV_TAC (TOP_DEPTH_CONV let_CONV)
     THEN DISCH_THEN (MAP_EVERY ASSUME_TAC o CONJUNCTS)
     THEN FULL_REWRITE_TAC []
     THEN SUBGOAL_THEN `?a. on_line O' a /\ on_line P a
                            /\ on_line P' a /\ on_line Q a` ASSUME_TAC
     THENL [discover_tac (by_cols o Di.split) ASM_MESON_TAC;
            CONJ_TAC THENL [ASM_MESON_TAC [];
                            ASSUM_LIST (ORDER_TAC `{O':point,P,P',Q}`)]]);;

let ray = 
  define_quotient_type "ray" ("mk_ray","dest_ray")
    `same_side`;;

let ray_origin_ds =
  new_definition `ray_origin_ds = FST o dest_dsegment`;;

let ray_origin =
  let line_wd = 
    prove (`!ds dt. same_side ds dt ==>
              ray_origin_ds ds = ray_origin_ds dt`,
           REPEAT GEN_TAC THEN REWRITE_TAC [same_side_unfold;ray_origin_ds]
             THEN DISCH_THEN (REPEAT_TCL CHOOSE_THEN MP_TAC)
             THEN SIMP_TAC [o_DEF]) in
  lift_function (snd ray)
    (same_side_refl, same_side_trans)
    "ray_origin" line_wd;;

let on_ray_ds = new_definition
  `on_ray_ds r P <=> let O,Q = dest_dsegment r in
                           (?a. on_line O a /\ on_line P a /\ on_line Q a)
                           /\ (P = Q \/ between O P Q \/ between O Q P)`;;

let on_ray_ds_same_side = prove
  (`on_ray_ds ds P <=> ~(P = ray_origin_ds ds)
                       /\ same_side ds (mk_dsegment (ray_origin_ds ds, P))`,
   REWRITE_TAC [on_ray_ds] THEN LET_TAC THEN ASM_REWRITE_TAC [same_side]
     THEN EQ_TAC THENL
     [ASM_REWRITE_TAC [o_DEF;ray_origin_ds]
         THEN FIRST_ASSUM (ASSUME_TAC o MATCH_MP dest_dsegment)
         THEN DISCH_TAC
         THEN SUBGOAL_THEN `~(O = P:point)` ASSUME_TAC
         THENL [ASM_MESON_TAC [BET_NEQS]; ALL_TAC]
         THEN SUBGOAL_THEN `dest_dsegment (mk_dsegment (O,P)) = O,P`
           ASSUME_TAC
         THENL [REWRITE_TAC [GSYM (CONJUNCT2 dsegment)]
                   THEN POP_ASSUM ACCEPT_TAC;ALL_TAC]
         THEN FULL_REWRITE_TAC [PAIR_EQ]
         THEN CONV_TAC (TOP_DEPTH_CONV let_CONV) THEN ASM_MESON_TAC []
     ;ASM_REWRITE_TAC [ray_origin_ds;o_DEF]
       THEN REWRITE_TAC [IMP_CONJ] THEN DISCH_TAC
       THEN SUBGOAL_THEN `dest_dsegment (mk_dsegment (O,P)) = O,P` ASSUME_TAC
       THENL [REWRITE_TAC [GSYM (CONJUNCT2 dsegment)]
             ;ASM_REWRITE_TAC [EQ_SYM_EQ]]
       THEN ASM_REWRITE_TAC [] THEN CONV_TAC (TOP_DEPTH_CONV let_CONV)
       THEN MESON_TAC []]);;

let on_ray = 
  let on_ray_wd = prove
    (`same_side ds dt ==> on_ray_ds ds = on_ray_ds dt`,
     ASSUME_ANT THEN REWRITE_TAC [same_side]  THEN LET_TAC
       THEN DISCH_TAC THEN MATCH_MP_TAC EQ_EXT THEN GEN_TAC
       THEN REWRITE_TAC [on_ray_ds_same_side]
       THEN ASM_REWRITE_TAC [ray_origin_ds;o_DEF]
       THEN ASM_MESON_TAC [same_side_trans;same_side_sym]) in 
  lift_function (snd ray)
    (same_side_refl, same_side_trans)
    "on_ray" on_ray_wd;;

let on_ray_disjoint =
  lift_theorem
    ray
    (same_side_refl,same_side_sym,same_side_trans)
    [snd ray_origin
    ;snd on_ray]
    (prove (`!r s. on_ray_ds r P ==> on_ray_ds s P
            ==> ray_origin_ds r = ray_origin_ds s
              ==> same_side r s`,
            REWRITE_TAC [on_ray_ds_same_side]
              THEN ASM_MESON_TAC [same_side_sym;same_side_trans]));; 

let on_ray_cover =
  lift_theorem
    ray
    (same_side_refl,same_side_sym,same_side_trans)
    [snd ray_origin
    ;snd on_ray]
    (theorem
       "!a P. on_line P a
           ==> ?r s. ~(same_side r s)
                     /\ P = ray_origin_ds r /\ P = ray_origin_ds s
                     /\ !X. on_line X a <=>
                        X = ray_origin_ds r 
                        \/ on_ray_ds r X \/ on_ray_ds s X"
     [fix ["a:line";"P:point"]
     ;assume "on_line P a" at [0]
     ;consider ["Q:point"] st "~(P = Q) /\ on_line Q a" at [1] by [g13a]
     ;so consider ["R:point"] st "between Q P R" at [2] by [g22]
     ;take ["mk_dsegment (P,Q)";"mk_dsegment (P,R)"]
     ;have "dest_dsegment (mk_dsegment (P,Q)) = P,Q" at [3] from [1] by
       [REWRITE_RULE [] (SPECL [`P:point,Q:point`] (CONJUNCT2 dsegment))]
     ;have "dest_dsegment (mk_dsegment (P,R)) = P,R" at [4] from [2] by
       [REWRITE_RULE [] (SPECL [`P:point,Q:point`] (CONJUNCT2 dsegment))
       ;BET_NEQS]
     ;unfolding from [3;4] by [ray_origin_ds;o_DEF]
     ;thus "~same_side (mk_dsegment (P,Q)) (mk_dsegment (P,R))"
       from [2;3;4] by [same_side_unfold;PAIR_EQ;g21;g23;BET_SYM]
       using REWRITE_TAC
     ;fix ["X:point"]
     ;unfolding by [TAUT `(p <=> q) <=> (p ==> q) /\ (q ==> p)`]
     ;thus ("on_line X a
               ==> X = P
                   \/ on_ray_ds (mk_dsegment (P,Q)) X
                   \/ on_ray_ds (mk_dsegment (P,R)) X")
       proof
       [assume "on_line X a" at [5]
       ;unfolding from [3;4] by [on_ray_ds;LET_DEF;LET_END_DEF]
       ;obviously by_cols
         (hence "?a. on_line P a /\ on_line X a /\ on_line Q a"
            from [0;1;5])
       ;obviously by_cols
         (hence "?a. on_line P a /\ on_line X a /\ on_line R a"
            from [0;1;2;5])
       ;qed from [2] using (ORDER_TAC `{P:point,Q:point,R:point,X:point}`)]
     ;unfolding from [3;4] by [on_ray_ds;LET_DEF;LET_END_DEF]
     ;obviously by_cols qed from [0;1;2] by [g12;BET_NEQS]]);;
     
let ray_not_empty = lift_theorem
  ray
  (same_side_refl,same_side_sym,same_side_trans)
  [snd on_ray]
  (prove
     (`!r. ?P. on_ray_ds r P`,
      REWRITE_TAC [on_ray_ds] THEN GEN_TAC THEN LET_TAC
        THEN MESON_TAC [g11_weak]));;

let origin_not_on_ray = lift_theorem
  ray
  (same_side_refl,same_side_sym,same_side_trans)
  [snd ray_origin;snd on_ray]
  (prove
     (`!r P. ~on_ray_ds r (ray_origin_ds r)`,
      REPEAT GEN_TAC THEN REWRITE_TAC [on_ray_ds] THEN LET_TAC
        THEN ASM_REWRITE_TAC [ray_origin_ds;o_DEF]
        THEN ASM_MESON_TAC [BET_NEQS;dest_dsegment]));;

let on_ray_not_bet =
  let left = prove
    (`!a ds P Q. (!R. on_ray_ds ds R ==> on_line R a)
        ==> on_ray_ds ds P ==> on_ray_ds ds Q
        ==> ~(Q = ray_origin_ds ds)
            /\ ~between P (ray_origin_ds ds) Q
            /\ on_line Q a`,
     REPEAT GEN_TAC THEN REWRITE_TAC [] THEN SIMP_TAC []
       THEN DISCH_TAC THEN REWRITE_TAC [on_ray_ds;ray_origin_ds]
       THEN LET_TAC THEN CONV_TAC (DEPTH_CONV let_CONV)
       THEN ASM_REWRITE_TAC [FST;o_DEF]
       THEN FIRST_ASSUM (ASSUME_TAC o MATCH_MP dest_dsegment)
       THEN DISCH_TAC THEN DISCH_TAC
       THEN SUBGOAL_THEN `dest_dsegment (mk_dsegment (O,P)) = (O,P)` ASSUME_TAC
       THENL [REWRITE_TAC [GSYM (CONJUNCT2 dsegment)]
              THEN ASM_MESON_TAC [BET_NEQS];ALL_TAC]
       THEN SUBGOAL_THEN `dest_dsegment (mk_dsegment (O,Q)) = (O,Q)` ASSUME_TAC
       THENL [REWRITE_TAC [GSYM (CONJUNCT2 dsegment)]
              THEN ASM_MESON_TAC [BET_NEQS]
             ;ALL_TAC]
       THEN SUBGOAL_THEN `same_side (mk_dsegment (O,P)) ds
                          /\ same_side (mk_dsegment (O,Q)) ds` ASSUME_TAC
       THENL [ASM_REWRITE_TAC [same_side]
              THEN CONJ_TAC THEN CONV_TAC (DEPTH_CONV let_CONV)
              THEN ASM_MESON_TAC []
             ;ALL_TAC]
       THEN SUBGOAL_THEN `same_side (mk_dsegment (O,P)) (mk_dsegment (O,Q))`
       MP_TAC THENL [ASM_MESON_TAC [same_side_sym;same_side_trans];ALL_TAC]
       THEN ASM_REWRITE_TAC [same_side;o_DEF]
       THEN CONV_TAC (DEPTH_CONV let_CONV)
       THEN DISCH_TAC THEN ASM_MESON_TAC [BET_NEQS;g21;g23]) in
  let right = theorem
    "!a ds P Q. (!R. on_ray_ds ds R ==> on_line R a)
      ==> ~(Q = ray_origin_ds ds)
          /\ ~between P (ray_origin_ds ds) Q
          /\ on_line Q a
      ==> on_ray_ds ds P ==> on_ray_ds ds Q"
    [fix ["a:line";"ds:dsegment";"P:point";"Q:point"]
    ;consider ["O:point";"R:point"] st "dest_dsegment ds = O,R"
      at [0] by [EXISTS_PAIR]
    ;unfolding from [this] by [ray_origin_ds;o_DEF]
    ;so consider ["X:point"] st "between O R X" at [1] by [dest_dsegment;g22]
    ;so consider ["Y:point"] st "between O X Y" at [2] by [BET_NEQS;g22]
    ;hence "between O R Y" at [3] from [1]
      using (ORDER_TAC `{O:point,R:point,X:point,Y:point}`)
    ;assume "(!S. on_ray_ds ds S ==> on_line S a)" at [4]
    ;have "on_line R a /\ on_line X a /\ on_line Y a" at [5]
      from [1;3] by [g11_weak;g21]
      using (K (POP_ASSUM MP_TAC THEN
                  ASM_REWRITE_TAC [on_ray_ds;LET_DEF
                                  ;LET_END_DEF]))
    ;hence "on_line O a" at [5] from [2;4] by [g12;g21]
    ;assume "on_line P a" at [6] from [4]
    ;unfolding from [0] by [on_ray_ds_same_side;ray_origin_ds;o_DEF;FST]
    ;assume "~(O = Q) /\ ~(O = P) /\ on_line Q a" at [7]
    ;assume "~between P O Q" at [8]
    ;have "same_side (mk_dsegment (O,P)) (mk_dsegment (O,Q))"
      proof
      [unfolding by [same_side]
      ;have "dest_dsegment (mk_dsegment (O,P)) = O,P"
        by [GSYM (CONJUNCT2 dsegment)] at [9] from [7]
      ;have "dest_dsegment (mk_dsegment (O,Q)) = O,Q"
        by [GSYM (CONJUNCT2 dsegment)] from [7]
      ;unfolding by [LET_DEF;LET_END_DEF] from [this;9]
      ;qed by [four] from [5;6;7;8]]
    ;qed by [same_side_sym;same_side_trans]]
  in
  lift_theorem
    ray
    (same_side_refl,same_side_sym,same_side_trans)
    [snd on_ray
    ;snd ray_origin]
    (prove
       (`!a r P Q.
           (!R. on_ray_ds r R ==> on_line R a) /\ on_ray_ds r P
           ==> (on_ray_ds r Q
                <=> ~(Q = ray_origin_ds r)
                     /\ ~between P (ray_origin_ds r) Q
                     /\ on_line Q a)`,
   MESON_TAC [left;right]));;

let ray_on_line =
  lift_theorem
    ray
    (same_side_refl,same_side_sym,same_side_trans)
    [snd on_ray
    ;snd ray_origin]
    (prove
       (`!a P r Q. on_ray_ds r P
         /\ on_line P a /\ on_line (ray_origin_ds r) a 
         ==> on_ray_ds r Q ==> on_line Q a`,
        REPEAT GEN_TAC THEN REWRITE_TAC [on_ray_ds] THEN LET_TAC
          THEN CONV_TAC (DEPTH_CONV let_CONV)
          THEN ASM_REWRITE_TAC [ray_origin_ds;FST;o_DEF] THEN REPEAT DISCH_TAC
          THEN FIRST_X_ASSUM (ASSUME_TAC o MATCH_MP dest_dsegment)
          THEN SUBGOAL_THEN `~(O:point = P)` ASSUME_TAC
          THEN ASM_MESON_TAC [BET_NEQS;g12]));;

(* Possibly a nicer form of on_ray_not_bet. *)
let on_ray_bet = theorem
  "!a r P Q.
         on_line (ray_origin r) a /\ on_line P a /\ on_ray r P
         ==> (on_ray r Q <=>
              P = Q
              \/ between (ray_origin r) P Q
              \/ between (ray_origin r) Q P)"
  [fix ["a:line";"r:ray";"P:point";"Q:point"]
  ;assume "on_line (ray_origin r) a /\ on_line P a /\ on_ray r P" at [0]
  ;hence "!R. on_ray r R ==> on_line R a" at [1] by [ray_on_line]
  ;have "on_ray r Q ==> P = Q 
                        \/ between (ray_origin r) P Q 
                        \/ between (ray_origin r) Q P" at [2] proof
    [assume "on_ray r Q" at [2]
    ;hence "on_line Q a" from [0] by [ray_on_line]
    ;qed by [four;on_ray_not_bet;origin_not_on_ray] from [0;1;2]]
  ;have "between (ray_origin r) P Q \/ between (ray_origin r) Q P
         ==> on_ray r Q" proof
    [assume "between (ray_origin r) P Q \/ between (ray_origin r) Q P" at [3]
    ;have "~(ray_origin r = P)" by [origin_not_on_ray] from [0]
    ;hence "on_line Q a" from [0;3] by [g21;g12]
    ;qed from [0;1;3] by [on_ray_not_bet;g23;BET_NEQS;BET_SYM]]
  ;qed from [0;2]];;     


