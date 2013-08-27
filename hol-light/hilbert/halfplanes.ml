(* ========================================================================= *)
(* Theory of half planes.                                                    *)
(*                                                                           *)
(*                                   Phil Scott                              *)
(*                                                                           *)
(*               Centre for Intelligent Systems and their Applications       *)
(*                             University of Edinburgh                       *)
(* ========================================================================= *)

(* We quotient a same half plane relation. *)

(* Proof that Pasch's Axiom can be stated without exclusive-or. The proof is
   based on Supplement I. This theorem is required to prove that no more than
   two half-planes can cover a plane and share a line. *)
let with_rewr b =
  Di.maxima (=)
    (Dim.lift2 (fun thm thm' ->
      PURE_ONCE_REWRITE_RULE [thm] thm') b b);;

let supplement1 =
  theorem "!A B C D E Fa a. ~(?a. on_line A a /\ on_line B a /\ on_line C a)
           /\ on_line D a /\ on_line E a /\ on_line Fa a 
           ==> ~between A D B \/ ~between A E C \/ ~between B Fa C"
    [fix ["A:point";"B:point";"C:point";"D:point";"E:point";"Fa:point";"a:line"]
    ;assume ("~(?a. on_line A a /\ on_line B a /\ on_line C a)
              /\ on_line D a /\ on_line E a /\ on_line Fa a") at [0;1]
    ;otherwise assume "between A D B /\ between A E C /\ between B Fa C" at [2]
    ;obviously (by_neqs o Di.conjuncts)
      (have "~(D = E) /\ ~(D = Fa) /\ ~(E = Fa)" from [0;2])
    ;hence "between D E Fa \/ between D Fa E \/ between Fa D E" from [1] by
      [four] at [3]
    ;have "!A' B' C' D' E' Fa'. 
              ~(?a. on_line A' a /\ on_line B' a /\ on_line C' a)
              /\ between A' Fa' B' /\ between A' E' C' /\ between B' D' C'
                 ==> ~between E' D' Fa'" proof
      [fix ["A':point";"B':point";"C':point";"D':point";"E':point";"Fa':point"]
      ;assume "~(?a. on_line A' a /\ on_line B' a /\ on_line C' a)" at [4]
      ;assume "between A' Fa' B' /\ between A' E' C'
             /\ between B' D' C' /\ between E' D' Fa'" at [5]
      ;obviously (by_ncols o Di.conjuncts)
        (consider ["G:point"] st "between A' G E' /\ between B' D' G")
        by [outer_pasch;BET_SYM] from [4;5]
      ;obviously (by_eqs o Di.conjuncts) qed from [4;5] by [g23]]
    ;qed from [0;2;3] by [BET_SYM]];;

let supplement1_col = theorem
  "(?a. on_line A a /\ on_line B a /\ on_line C a)
   /\ ~on_line A a /\ ~on_line B a /\ ~on_line C a
   /\ on_line D a /\ on_line E a /\ on_line Fa a
   ==> ~between A D B \/ ~between A E C \/ ~between B Fa C"
  [assume "?a. on_line A a /\ on_line B a /\ on_line C a" at [0]
  ;assume "~on_line A a /\ ~on_line B a /\ ~on_line C a" at [1]
  ;assume "on_line D a /\ on_line E a /\ on_line Fa a" at [2]
  ;assume "between A D B /\ between A E C /\ between B Fa C" at [3]
  ;hence "D = E /\ D = Fa /\ E = Fa" proof
     [otherwise assume "~(D = E) \/ ~(D = Fa) \/ ~(E = Fa)"
     ;obviously (by_eqs o Di.split) qed from [0;1;2;3]]
  ;qed using ORDER_TAC `{A:point,B,C,D,E,Fa}` from [0;1;2;3]];;

let supplement1_general = prove
  (`!A B C D E Fa.
      ~on_line A a /\ ~on_line B a /\ ~on_line C a
      /\ on_line D a /\ on_line E a /\ on_line Fa a
      ==> ~between A D B \/ ~between A E C \/ ~between B Fa C`,
   MESON_TAC [supplement1;supplement1_col]);;      

(* In order to use the quotienting facilities of HOL Light, we need an
   equivalence relation on a type. Unfortunately, the equivalence relation we
   want to define half-planes is only satisfied on subsets of points determined
   by a line. We move the line and the constraints into a new-type. *)
let half_plane_pt =
  new_type_definition "half_plane_pt"
  ("mk_half_plane_pt","dest_half_plane_pt")
    (prove (`?(P,a). ~on_line P a`,
            REWRITE_TAC [EXISTS_PAIRED_THM] THEN MESON_TAC [g13b]));;

let dest_half_plane_pt =
  prove (`!A a hp. dest_half_plane_pt hp = A,a
            ==> ~on_line A a`,
         REPEAT GEN_TAC
     THEN DISCH_TAC THEN FIRST_ASSUM (MP_TAC o AP_TERM `mk_half_plane_pt`)
     THEN DISCH_THEN (MP_TAC o AP_TERM `dest_half_plane_pt`)
     THEN REWRITE_TAC [half_plane_pt] THEN ASM_REWRITE_TAC []
     THEN MESON_TAC
           [REWRITE_RULE [FORALL_PAIRED_THM; LAMBDA_PAIR_THM] half_plane_pt]);;

let same_half_plane = new_definition
  `same_half_plane p q <=>
    let P,a = dest_half_plane_pt p
    and Q,b = dest_half_plane_pt q in
    a = b /\ (?'a. on_plane P 'a /\ on_plane Q 'a
                   /\ !P. on_line P a ==> on_plane P 'a)
    /\ ~on_line P a /\ ~on_line Q a
    /\ ~(?R. on_line R a /\ between P R Q)`;;

let same_half_plane_unfold = prove
  (`!p q. same_half_plane p q
       <=> ?P Q a 'a.
             dest_half_plane_pt p = P,a /\ dest_half_plane_pt q = Q,a
               /\ on_plane P 'a /\ on_plane Q 'a
               /\ ~on_line P a /\ ~on_line Q a
               /\ (!P. on_line P a ==> on_plane P 'a)
               /\ ~(?R. on_line R a /\ between P R Q)`,
   REPEAT GEN_TAC THEN REWRITE_TAC [same_half_plane] THEN LET_TAC
     THEN REWRITE_TAC [PAIR_EQ] THEN MESON_TAC []);;

let same_half_plane_refl = prove
  (`!p. same_half_plane p p`,
   GEN_TAC THEN REWRITE_TAC [same_half_plane] THEN LET_TAC
     THEN POP_ASSUM (MP_TAC o MATCH_MP dest_half_plane_pt)
     THEN FULL_REWRITE_TAC [PAIR_EQ]
     THEN MESON_TAC [BET_NEQS;point_line_plane]);;

let same_half_plane_sym = prove
  (`!p q. same_half_plane p q <=> same_half_plane q p`,
   REPEAT GEN_TAC THEN REWRITE_TAC [same_half_plane] THEN REPEAT LET_TAC
     THEN FULL_REWRITE_TAC [PAIR_EQ] THEN MESON_TAC [BET_SYM]);;

(* We strengthen g24. Thanks to Alan Bundy for spotting this. *)
let g24_strong = theorem
  "!A B C P a 'a.
         on_plane A 'a /\ on_plane B 'a /\ on_plane C 'a
         ==> (!P. on_line P a ==> on_plane P 'a)
         ==> ~on_line A a /\ ~on_line B a /\ ~on_line C a
         ==> on_line P a /\ between A P B
         ==> (?Q. on_line Q a /\ (between A Q C \/ between B Q C))"
  [fix ["A:point";"B:point";"C:point";"P:point";"a:line";"'a:plane"]
  ;assume "on_plane A 'a /\ on_plane B 'a /\ on_plane C 'a" at [0]
  ;assume "!P. on_line P a ==> on_plane P 'a" at [1]
  ;assume "~on_line A a /\ ~on_line B a /\ ~on_line C a" at [2]
  ;assume "on_line P a /\ between A P B" at [3]
  ;per cases
    [[suppose "~(?a. on_line A a /\ on_line B a /\ on_line C a)"
     ;qed by [g24] from [0;1;2;3]
       using K (MATCH_MP_TAC (REWRITE_RULE [IMP_IMP] g24))]
    ;[suppose "?a. on_line A a /\ on_line B a /\ on_line C a" at [4]
     ;take ["P:point"]
     ;thus "on_line P a" from [3]
     ;have "~(C = P)" from [2;3]
     ;qed using ORDER_TAC `{A:point,B,C,P}` from [0;1;2;3;4]]]];;

(* Just for the write-up *)
let g24_col_case = theorem
  "!A B C P a.
         on_line P a /\ ~on_line C a /\ between A P B
         /\ (?a. on_line A a /\ on_line B a /\ on_line C a)
         ==> ?Q. on_line Q a /\ (between A Q C \/ between B Q C)"
  [fix ["A:point";"B:point";"C:point";"P:point";"a:line"]
  ;assume "on_line P a /\ ~on_line C a /\ between A P B" at [0]
  ;assume "?a. on_line A a /\ on_line B a /\ on_line C a" at [1]
  ;take ["P:point"]
  ;thus "on_line P a" from [0]
  ;have "~(C = P)" from [0]
  ;hence "(between A P C \/ between B P C)"
    using ORDER_TAC `{A:point,B,C,P}` from [0;1]];;

let same_half_plane_trans = theorem
  "!x y z. same_half_plane x y /\ same_half_plane y z ==> same_half_plane x z"
  [fix ["x:half_plane_pt";"y:half_plane_pt";"z:half_plane_pt"]
  ;unfolding by
    [same_half_plane_unfold;IMP_CONJ;LEFT_IMP_EXISTS_THM;RIGHT_IMP_FORALL_THM]
  ;fix ["px:point"; "py:point";"a:line";"'a:plane"
       ;"py2:point";"pz:point";"b:line";"'b:plane"]
  ;assume "b = a /\ py2 = py" by [PAIR_EQ]
  ;so (K unfolding) ()
  ;assume "~on_line py a" by [dest_half_plane_pt] at [0]
  ;assume ("on_plane py 'a /\ on_plane py 'b" ^
              "/\ (!P. on_line P a ==> on_plane P 'a /\ on_plane P 'b)") at [1]
  ;hence "'b = 'a" from [0] by [point_line_plane]
  ;so (K unfolding) ()
  ;assume "~(px = py) /\ ~(py = pz) /\ ~(px = pz)" at [2] by [g21]
  ;assume ("~(?R. on_line R a /\ between px R py)" ^
              "/\ ~(?R. on_line R a /\ between py R pz)") at [3]
  ;assume ("~on_line px a /\ on_plane px 'a" ^
              "/\ ~on_line py a /\ on_plane py 'a" ^
              "/\ ~on_line pz a /\ on_plane pz 'a")
     at [4] from [1] by [dest_half_plane_pt]
  ;so assume "?R. on_line R a /\ between px R pz" from [1]
  ;so consider ["R:point"] st "on_line R a /\ between px R pz" at [5]
  ;assume "!P. on_line P a ==> on_plane P 'a" at [6]
  ;so consider ["P:point"] st
    "on_line P a /\ (between px P py \/ between pz P py)" from [4;5;6]
    using (K (MATCH_MP_TAC (REWRITE_RULE [IMP_IMP] g24_strong)))
  ;qed from [3] by [BET_SYM]];;

let half_plane =
  define_quotient_type "half_plane" ("mk_half_plane","dest_half_plane")
    `same_half_plane`;;

let line_of_half_plane_pt =
  new_definition `line_of_half_plane_pt = SND o dest_half_plane_pt`;;

let line_of_half_plane =
  let line_wd = 
    prove (`same_half_plane x y ==>
              line_of_half_plane_pt x = line_of_half_plane_pt y`,
           REWRITE_TAC [same_half_plane_unfold;line_of_half_plane_pt]
             THEN DISCH_THEN (REPEAT_TCL CHOOSE_THEN MP_TAC)
             THEN SIMP_TAC [o_DEF])
  in lift_function (snd half_plane)
  (same_half_plane_refl, same_half_plane_trans)
  "line_of_half_plane" line_wd;;

let EXISTS_UNIQUE_THM2 =
  prove (`!P. (?!x. P x) <=> (?x. P x /\ !y. P x /\ P y ==> x = y)`,
         MESON_TAC []);;

let on_half_plane_pt = new_definition
  `on_half_plane_pt p P <=> let Q,a = dest_half_plane_pt p in
                            ~on_line P a
                            /\ (?'a. on_plane P 'a /\ on_plane Q 'a
                                /\ !R. on_line R a ==> on_plane R 'a)
                            /\ ~(?R. on_line R a /\ between P R Q)`;;

let on_half_plane_same_half_plane = prove
  (`!P x. on_half_plane_pt x P
     <=> ~(on_line P (line_of_half_plane_pt x))
          /\ same_half_plane (mk_half_plane_pt
                                (P, line_of_half_plane_pt x)) x`,
   REPEAT GEN_TAC THEN EQ_TAC
     THEN REWRITE_TAC [IMP_CONJ;on_half_plane_pt;line_of_half_plane_pt]
     THEN LET_TAC THEN ASM_REWRITE_TAC [o_DEF;same_half_plane]
     THEN DISCH_TAC THEN
     (SUBGOAL_THEN `dest_half_plane_pt (mk_half_plane_pt (P,a)) = P,a`
       ASSUME_TAC
     THENL [ASM_MESON_TAC [REWRITE_RULE [FORALL_PAIRED_THM;LAMBDA_PAIR_THM]
                              half_plane_pt]
           ;ALL_TAC])
     THEN ASM_REWRITE_TAC [] THEN CONV_TAC (DEPTH_CONV let_CONV)
     THEN ASM_MESON_TAC [dest_half_plane_pt]);;

let on_half_plane =
  let on_half_plane_wd =
    let lemma =
      prove
        (`!P Q a x.
            dest_half_plane_pt x = Q,a
              /\ ~on_line P a
              /\ (?'a. on_plane P 'a /\ on_plane Q 'a /\ !R. on_line R a
                  ==> on_plane R 'a)
              ==> (~(?R. on_line R a /\ between P R Q)
                   <=> same_half_plane x (mk_half_plane_pt (P,a)))`,
         REPEAT GEN_TAC THEN DISCH_THEN (MAP_EVERY ASSUME_TAC o CONJUNCTS)
           THEN ASM_REWRITE_TAC [same_half_plane]
           THEN FIRST_X_ASSUM (ASSUME_TAC o MATCH_MP dest_half_plane_pt)
           THEN SUBGOAL_THEN `dest_half_plane_pt (mk_half_plane_pt (P,a)) = P,a`
             ASSUME_TAC
           THENL [ASM_REWRITE_TAC [GSYM (CONJUNCT2 half_plane_pt)]
                 ;ASM_REWRITE_TAC [] THEN CONV_TAC (DEPTH_CONV let_CONV)
                   THEN FULL_REWRITE_TAC [CONJ_ACI;BET_SYM]]) in
    prove (`same_half_plane x y ==>
              on_half_plane_pt x = on_half_plane_pt y`,
           ASSUME_ANT
             THEN REWRITE_TAC [same_half_plane_unfold;FUN_EQ_THM;on_half_plane_pt]
             THEN DISCH_THEN (REPEAT_TCL CHOOSE_THEN MP_TAC) THEN SIMP_TAC []
             THEN DISCH_TAC THEN CONV_TAC (DEPTH_CONV let_CONV) THEN X_GEN_TAC `P':point`
             THEN EXTRACT `~on_line P' a` THEN EQ_TAC
             THEN (REWRITE_TAC [IMP_CONJ]
                     THEN DISCH_THEN (X_CHOOSE_TAC `'b:plane`)
                     THEN DISCH_TAC
                     THEN SUBGOAL_THEN `'a:plane = 'b` ASSUME_TAC
                 THENL [ASM_MESON_TAC [REWRITE_RULE [EXISTS_UNIQUE_THM]
                                          point_line_plane]; ALL_TAC])
             THENL [MP_TAC (SPECL [`P':point`;`P:point`
                                  ;`a:line`;`x:half_plane_pt`] lemma)
                       THEN ASM_MESON_TAC
                       [lemma;same_half_plane_sym;same_half_plane_trans]
                      ;MP_TAC (SPECL [`P':point`;`Q:point`
                                     ;`a:line`;`y:half_plane_pt`] lemma)
                        THEN ASM_MESON_TAC
                        [lemma;same_half_plane_sym;same_half_plane_trans]]) in
  lift_function (snd half_plane)
    (same_half_plane_refl, same_half_plane_trans)
    "on_half_plane" on_half_plane_wd;;

let on_half_plane_disjoint =
  lift_theorem
    half_plane
    (same_half_plane_refl,same_half_plane_sym,same_half_plane_trans)
    [snd line_of_half_plane
    ;snd on_half_plane]
    (prove 
       (`!P p q. on_half_plane_pt p P ==> on_half_plane_pt q P
        ==> line_of_half_plane_pt p = line_of_half_plane_pt q
          ==> same_half_plane p q`,
        REPEAT GEN_TAC THEN REWRITE_TAC [on_half_plane_same_half_plane]
          THEN ASM_MESON_TAC [same_half_plane_sym;same_half_plane_trans]));;

let by_planes b = (Id.inferred b).Id.planes;;
  
let half_plane_cover = lift_theorem
  half_plane
  (same_half_plane_refl,same_half_plane_sym,same_half_plane_trans)
  [snd line_of_half_plane
  ;snd on_half_plane]
  (theorem
     "(!P. on_line P a ==> on_plane P 'a)
     ==> ?p q. ~(same_half_plane p q)
           /\ a = line_of_half_plane_pt p
           /\ a = line_of_half_plane_pt q
           /\ (!P. on_plane P 'a <=>
                   (on_line P a
                      \/ on_half_plane_pt p P
                      \/ on_half_plane_pt q P))"  
     [unfolding by [line_of_half_plane_pt]
     ;assume "(!P. on_line P a ==> on_plane P 'a)" at [0]
     ;consider ["X:point";"Y:point"]
       st "~(X = Y) /\ on_line X a /\ on_line Y a"
       at [1;2;3] by [g13a]
     ;so consider ["P:point"] st "on_plane P 'a /\ ~on_line P a" at
       [4;5] by [g12;plane_three]
     ;so consider ["Q:point"] st "between P X Q" at [6]
       from [2;5] by [g22]
     ;obviously by_planes
       (hence "?'a. on_plane P 'a /\ on_plane Q 'a
               /\ on_plane X 'a /\ on_plane Y 'a")
       at [7] from [2;3;6]
     ;clearly by_ncols
       (have "~(?a. on_line P a /\ on_line X a /\ on_line Y a)"
          at [8] from [1;2;3;5])
     ;hence "on_plane P 'a /\ on_plane Q 'a
               /\ on_plane X 'a /\ on_plane Y 'a"
          by [SPECL [`P:point`;`X:point`;`Y:point`] g15]
          at [9] from [0;2;3;4;7]
     ;take ["mk_half_plane_pt (P,a)";"mk_half_plane_pt (Q,a)"]
     ;have "dest_half_plane_pt (mk_half_plane_pt (P,a)) = P,a" at [10] by
       [REWRITE_RULE [] (SPECL [`P:point,a:line`] (CONJUNCT2 half_plane_pt))]
       from [5]
     ;unfolding from [this] by [o_DEF]
     ;obviously by_ncols
       (thus "dest_half_plane_pt (mk_half_plane_pt (Q,a)) = Q,a" at [11] by
          [REWRITE_RULE []
              (SPECL [`Q:point,a:line`] (CONJUNCT2 half_plane_pt))]
          from [1;2;3;5;6] by [g12])
     ;unfolding from [10;this] by [o_DEF]
     ;hence "~same_half_plane (mk_half_plane_pt (P,a)) (mk_half_plane_pt (Q,a))" 
       from [2;6;8;10] by [same_half_plane_unfold;PAIR_EQ]
       using REWRITE_TAC
     ;fix ["R:point"]
     ;unfolding by [TAUT `(p <=> q) <=> (p ==> q) /\ (q ==> p)`]
     ;thus ("on_plane R 'a
          ==> on_line R a
              \/ on_half_plane_pt (mk_half_plane_pt (P,a)) R
              \/ on_half_plane_pt (mk_half_plane_pt (Q,a)) R")
       proof
       [unfolding from [10;11] by [on_half_plane_pt;LET_DEF;LET_END_DEF]
       ;so assume "(?U. on_line U a /\ between R U P) 
             /\ (?V. on_line V a /\ between R V Q)"
         from [0;9]
       ;so consider ["U:point";"V:point"] at [12] st
         "on_line U a /\ between R U P /\ on_line V a /\ between R V Q"
       ;per cases
         [[suppose "?a. on_line P a /\ on_line Q a /\ on_line R a"
          ;obviously (by_eqs o Di.conjuncts)
            (hence "between P X R /\ between Q X R"
               from [2;3;6;8;12] by [BET_SYM])
          ;qed from [1;6] using (ORDER_TAC `{P:point,Q,R,X:point}`)]
         ;[suppose "~(?a. on_line P a /\ on_line Q a /\ on_line R a)"
          ;obviously by_ncols qed from [2;6;12] by [BET_SYM;supplement1]]]]
     ;unfolding from [10;11]
       by [on_half_plane_pt;LET_DEF;LET_END_DEF]
     ;obviously by_ncols (have "~on_line Q a" from [2;3;6;8])
     ;qed from [0;5;9]
       by [REWRITE_RULE [EXISTS_UNIQUE_THM]
              (SPECL [`R:point`;`a:line`] point_line_plane)]]);;

let half_plane_not_empty = lift_theorem
  half_plane
  (same_half_plane_refl,same_half_plane_sym,same_half_plane_trans)
  [snd line_of_half_plane
  ;snd on_half_plane]
  (prove
     (`!p. ?P. on_half_plane_pt p P`,
      REWRITE_TAC [on_half_plane_pt] THEN GEN_TAC THEN LET_TAC
        THEN POP_ASSUM (ASSUME_TAC o MATCH_MP dest_half_plane_pt)
        THEN EXISTS_TAC `Q:point`
        THEN ASM_MESON_TAC [BET_NEQS;point_line_plane]));;

let half_plane_not_on_line = lift_theorem
  half_plane
  (same_half_plane_refl,same_half_plane_sym,same_half_plane_trans)
  [snd line_of_half_plane
  ;snd on_half_plane]
  (prove
     (`!p P. on_half_plane_pt p P
        ==> ~(on_line P (line_of_half_plane_pt p))`,
      REPEAT GEN_TAC THEN REWRITE_TAC [on_half_plane_pt] THEN LET_TAC
        THEN ASM_REWRITE_TAC [line_of_half_plane_pt;o_DEF]
        THEN MESON_TAC []));;

let EXISTS_PAIR = prove
  (`!p. ?a b. p = (a,b)`,
   REWRITE_TAC [GSYM EXISTS_PAIR_THM] THEN MESON_TAC []);;

let on_half_plane_not_bet =
  let left = prove
    (`!hp P Q. (!R. on_half_plane_pt hp R ==> on_plane R 'a)
          ==> on_half_plane_pt hp P
              /\ on_half_plane_pt hp Q
              ==> ~(?R. on_line R (line_of_half_plane_pt hp)
                        /\ between P R Q)
                  /\ on_plane Q 'a
                  /\ ~on_line Q (line_of_half_plane_pt hp)`,
     REPEAT GEN_TAC THEN DISCH_TAC THEN ASM_SIMP_TAC []
       THEN REWRITE_TAC [on_half_plane_pt;line_of_half_plane_pt]
       THEN LET_TAC THEN CONV_TAC (DEPTH_CONV let_CONV)
       THEN FIRST_ASSUM (ASSUME_TAC o MATCH_MP dest_half_plane_pt)
       THEN STRIP_TAC THEN SUBGOAL_THEN
       `dest_half_plane_pt (mk_half_plane_pt (P,a)) = P,a`
         ASSUME_TAC 
       THEN ASM_REWRITE_TAC [GSYM (CONJUNCT2 half_plane_pt)]
       THEN SUBGOAL_THEN
       `dest_half_plane_pt (mk_half_plane_pt (Q,a)) = Q,a`
         ASSUME_TAC
       THENL [ASM_REWRITE_TAC [GSYM (CONJUNCT2 half_plane_pt)]
             ;ALL_TAC]
       THEN SUBGOAL_THEN `same_half_plane (mk_half_plane_pt (P,a)) hp
         /\ same_half_plane (mk_half_plane_pt (Q,a)) hp` ASSUME_TAC
       THENL [ASM_REWRITE_TAC [same_half_plane]
                 THEN CONJ_TAC THEN CONV_TAC (DEPTH_CONV let_CONV)
                 THEN ASM_MESON_TAC [dest_half_plane_pt]
             ;ALL_TAC]
       THEN SUBGOAL_THEN
         `same_half_plane (mk_half_plane_pt (P,a))
          (mk_half_plane_pt (Q,a))` MP_TAC
       THENL [ASM_MESON_TAC [same_half_plane_sym
                            ;same_half_plane_trans]
             ;ALL_TAC]
       THEN ASM_REWRITE_TAC [same_half_plane;o_DEF]
       THEN CONV_TAC (DEPTH_CONV let_CONV) THEN ASM_SIMP_TAC [o_DEF]) in
    let right = theorem
      "!p P Q. (!R. on_half_plane_pt p R ==> on_plane R 'a)
           ==> ~(?R. on_line R (line_of_half_plane_pt p) /\ between P R Q)
                   /\ on_plane Q 'a
                   /\ ~on_line Q (line_of_half_plane_pt p)
               ==> on_half_plane_pt p P
                    ==> on_half_plane_pt p Q"
      [fix ["p:half_plane_pt";"P:point";"Q:point"]
      ;consider ["R:point";"a:line"] st "dest_half_plane_pt p = R,a"
        at [0] by [EXISTS_PAIR]
      ;unfolding from [this] by [line_of_half_plane_pt;o_DEF]
      ;hence "~on_line R a" at [1] by [dest_half_plane_pt]
      ;consider ["A:point";"B:point"] st
        "~(A = B) /\ on_line A a /\ on_line B a" at [2;3;4]
        by [g13a]
      ;consider ["C:point";"D:point"] st "between A R C /\ between B R D"
         by [g22] from [1;3;4] at [5;6]
      ;obviously by_ncols
         (have "~(?a. on_line C a /\ on_line D a /\ on_line R a)"
            at [7] from [1;2;3;4;5;6])
      ;consider ["'b:plane"] st
         "on_plane R 'b /\ (!P. on_line P a ==> on_plane P 'b)"
         at [8] from [1] by [point_line_plane]
      ;hence "on_plane A 'b /\ on_plane B 'b /\ on_plane R 'b"
        at [9] from [3;4]
      ;clearly by_ncols
         (have "~(?a. on_line A a /\ on_line B a /\ on_line R a)"
            at [10] from [1;2;3;4])
      ;obviously by_planes
         (hence "on_plane C 'b /\ on_plane D 'b" at [11] from [5;6;9] by [g15])
      ;obviously by_ncols
         (hence "~on_line C a /\ ~on_line D a"
            at [12] from [2;3;4;5;6;10] by [g12])
      ;have "~(?X. on_line X a /\ between D X R)" at [13] proof
        [otherwise consider ["X:point"] st "on_line X a /\ between D X R" 
        ;obviously (by_eqs o Di.split) qed from [3;4;6;10] by [g21;g23]]
      ;have "~(?X. on_line X a /\ between C X R)" at [14] proof
        [otherwise consider ["X:point"] st "on_line X a /\ between C X R"
        ;obviously (by_eqs o Di.split) qed from [3;4;5;10] by [g21;g23]]
      ;assume "(!R. on_half_plane_pt p R ==> on_plane R 'a)" at [15]
      ;hence ("!P. ~on_line P a
                   /\ (?'a. on_plane P 'a /\ on_plane R 'a
                            /\ !R. on_line R a ==> on_plane R 'a)
                   /\ ~(?X. on_line X a /\ between P X R)
                   ==> on_plane P 'a") at [16]
        using (K (POP_ASSUM MP_TAC THEN
                    ASM_REWRITE_TAC [on_half_plane_pt;LET_DEF
                                    ;LET_END_DEF]))
      ;hence "on_plane C 'a /\ on_plane D 'a" at [17] from [0;8;11;12;13;14]
      ;have "on_plane R 'a" at [18] from [1;16;8] by [BET_NEQS]
      ;hence "!P. on_line P a ==> on_plane P 'a"
        at [19] from [7;8;11;17] by [g15]
      ;assume "~on_line Q a" at [20]
      ;assume "on_plane Q 'a" at [21]
      ;assume "~(?R. on_line R a /\ between P R Q)" at [22]
      ;assume "on_plane P 'a" at [23] from [15]
      ;unfolding
        by [on_half_plane_same_half_plane;line_of_half_plane_pt;o_DEF;SND]
        from [0]
      ;assume "~on_line P a" at [24]
      ;have "same_half_plane (mk_half_plane_pt (P,a)) (mk_half_plane_pt (Q,a))"
        proof
        [unfolding by [same_half_plane]
        ;hence "dest_half_plane_pt (mk_half_plane_pt (P,a)) = P,a"
          at [25] by [GSYM (CONJUNCT2 half_plane_pt)]
        ;have "dest_half_plane_pt (mk_half_plane_pt (Q,a)) = Q,a"
          at [26] by [GSYM (CONJUNCT2 half_plane_pt)] from [20]
        ;unfolding by [LET_DEF;LET_END_DEF] from [this;25]
        ;qed from [19;20;21;22;23;24]]
      ;qed from [20] by [same_half_plane_sym;same_half_plane_trans]] in
    lift_theorem
      half_plane
      (same_half_plane_refl,same_half_plane_sym,same_half_plane_trans)
      [snd line_of_half_plane
      ;snd on_half_plane]
      (prove
         (`!'a p P Q. (!R. on_half_plane_pt p R
                    ==> on_plane R 'a)
          /\ on_half_plane_pt p P
          ==> (on_half_plane_pt p Q
               <=> ~(?R. on_line R (line_of_half_plane_pt p)
                     /\ between P R Q)
                   /\ on_plane Q 'a
                   /\ ~on_line Q (line_of_half_plane_pt p))`,
          MESON_TAC [left;right]));;

let half_plane_on_plane =
  lift_theorem half_plane
      (same_half_plane_refl,same_half_plane_sym,same_half_plane_trans)
      [snd line_of_half_plane
      ;snd on_half_plane]
    (prove
       (`!'a P hp Q. on_half_plane_pt hp P
             /\ on_plane P 'a /\
             (!R. on_line R (line_of_half_plane_pt hp) ==> on_plane R 'a)
             ==> on_half_plane_pt hp Q ==> on_plane Q 'a`,
        REWRITE_TAC [] THEN REPEAT GEN_TAC
          THEN REWRITE_TAC [on_half_plane_pt;line_of_half_plane_pt;IMP_CONJ]
          THEN LET_TAC THEN CONV_TAC (DEPTH_CONV let_CONV)
          THEN ASM_REWRITE_TAC [o_DEF;SND;IMP_CONJ]
          THEN FIRST_X_ASSUM
          (ASSUME_TAC o CONJUNCT2 o REWRITE_RULE
             [EXISTS_UNIQUE_THM] o MATCH_MP point_line_plane
             o MATCH_MP dest_half_plane_pt)
          THEN DISCH_THEN
          (ASSUME_TAC o CONJUNCT2 o REWRITE_RULE [EXISTS_UNIQUE_THM]
             o MATCH_MP point_line_plane)
          THEN DISCH_THEN (X_CHOOSE_TAC `'b:plane`) THEN DISCH_THEN (K ALL_TAC)
          THEN DISCH_TAC THEN DISCH_TAC THEN DISCH_THEN (K ALL_TAC)
          THEN DISCH_THEN (X_CHOOSE_TAC `'c:plane`)
          THEN SUBGOAL_THEN `'b = 'a:plane` (fun thm -> REWRITE_ASM_TAC [thm])
          THENL [ASM_MESON_TAC [];ALL_TAC]
          THEN SUBGOAL_THEN `'c = 'a:plane` (fun thm -> REWRITE_ASM_TAC [thm]) 
          THENL [ASM_MESON_TAC [];ALL_TAC]
          THEN ASM_REWRITE_TAC []));;

let half_plane_cover2 = prove
  (`!hp hq P. (!P. on_line P (line_of_half_plane hp) ==> on_plane P 'a)
         /\ (!P. on_half_plane hq P ==> on_plane P 'a)
         /\ ~(hp = hq)
         /\ line_of_half_plane hp = line_of_half_plane hq
         /\ (!P. on_half_plane hp P ==> on_plane P 'a)
         ==> (on_plane P 'a <=> on_line P (line_of_half_plane hp)
             \/ on_half_plane hp P 
             \/ on_half_plane hq P)`,
   REWRITE_TAC [IMP_CONJ] THEN REPEAT GEN_TAC
     THEN DISCH_THEN
     (MAP_EVERY_TCL X_CHOOSE_THEN [`hp':half_plane`;`hq':half_plane`]
        ASSUME_TAC o MATCH_MP half_plane_cover)
     THEN DISCH_TAC
     THEN X_CHOOSE_TAC `X:point` (SPECL [`hp:half_plane`] half_plane_not_empty)
     THEN X_CHOOSE_TAC `Y:point` (SPECL [`hq:half_plane`] half_plane_not_empty)
     THEN REPEAT DISCH_TAC
     THEN SUBGOAL_THEN `(on_half_plane hp' X \/ on_half_plane hq' X) 
                        /\ (on_half_plane hp' Y \/ on_half_plane hq' Y)`
     ASSUME_TAC
     THEN ASM_MESON_TAC [half_plane_on_plane;half_plane_not_on_line
                        ;on_half_plane_disjoint]);;
