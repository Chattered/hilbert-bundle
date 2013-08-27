(* ========================================================================= *)
(* Theory of linear orders, culminating in a proof that there are infinitely *)
(* many points on the segment AB and a decision procedure for betweenness    *)
(* problems via reduction to ARITH_TAC.                                      *)
(*                                                                           *)
(*                                   Phil Scott                              *)
(*                                                                           *)
(*               Centre for Intelligent Systems and their Applications       *)
(*                             University of Edinburgh                       *)
(* ========================================================================= *)

let COLLINEAR =
  new_definition `COLLINEAR Ps <=> ?a. !P. P IN Ps ==> on_line P a`;; 

let BET_COL = prove
  (`!A B C. between A B C ==> COLLINEAR {A,B,C}`,
   REWRITE_TAC [COLLINEAR;FORALL_IN_INSERT;NOT_IN_EMPTY]
     THEN MESON_TAC [COLLINEAR;g21]);;

let BOUNDS = new_definition
  `BOUNDS P Q X <=> P IN X /\ Q IN X
   /\ !R. R IN (X DIFF {P,Q}) ==> between P R Q`;;

let set_two = prove
  (`!A:a B. CARD {A,B} <= 2`,
   SIMP_TAC [CARD_CLAUSES;FINITE_INSERT;FINITE_EMPTY] THEN ARITH_TAC);;

let BOUNDS_REFL = prove
  (`!P X. BOUNDS P P X <=> X = {P}`,
   REWRITE_TAC [BOUNDS;MESON [BET_NEQS] `!P Q. ~between P Q P`]
     THEN SET_TAC []);;

let BOUNDS_ONE = prove
  (`!P Q. BOUNDS P Q {P} ==> P = Q`,
   MESON_TAC [BOUNDS;IN_INSERT;NOT_IN_EMPTY]);;

let BOUNDS_TWO = prove
  (`!P Q. ~(P = Q) ==> (BOUNDS P Q {P,Q})`,
   REWRITE_TAC [BOUNDS] THEN SET_TAC []);;

let BOUNDS_IN = prove
  (`!P Q X. BOUNDS P Q X ==> P IN X /\ Q IN X`, MESON_TAC [BOUNDS]);;

let BET_BOUNDS = prove
  (`!A B C. between A C B ==> BOUNDS A B {A,B,C}`,
   REWRITE_TAC [BOUNDS; IN_DIFF;IN_INSERT;NOT_IN_EMPTY] THEN MESON_TAC []);;

let BOUNDS_SYM = prove
  (`!X P Q. BOUNDS P Q X <=> BOUNDS Q P X`,
   REWRITE_TAC [BOUNDS] THEN SET_TAC[BET_SYM]);;

let BOUNDS_NOT_BET =
  let lemma = prove
    (`!A B P Q. between P A Q ==> between P B Q ==> ~between B P A`,
     MESON_TAC [five1;g23;BET_SYM]) 
  in prove
       (`!P Q X. BOUNDS P Q X ==> !A B. A IN X /\ B IN X ==> ~between A P B`,
        REWRITE_TAC [BOUNDS;IN_DIFF; IN_INSERT; NOT_IN_EMPTY]
          THEN REPEAT STRIP_TAC
          THEN SUBGOAL_THEN `~(A:point = P) /\ ~(A = Q)
                             /\ ~(B = P) /\ ~(B = Q)` MP_TAC
          THENL [ASM_MESON_TAC [BET_NEQS;g23;BET_SYM]
                ;ASM_MESON_TAC [lemma]]);;
    
let NOT_BET_BOUND = prove
  (`!P Q R X. BOUNDS P Q X ==> R IN X
     ==> (!A B. A IN X /\ B IN X ==> ~between A R B) ==> R = P \/ R = Q`,
   REPEAT GEN_TAC THEN REWRITE_TAC [BOUNDS;IN_INSERT;IN_DIFF;NOT_IN_EMPTY]
     THEN MESON_TAC [g23]);;

let BOUND_EQ = prove
  (`!X A B P Q. BOUNDS A B X /\ BOUNDS P Q X ==> A = P \/ A = Q`,
   REPEAT GEN_TAC THEN REWRITE_TAC [IMP_CONJ] THEN DISCH_TAC
     THEN FIRST_MATCH MP_TAC BOUNDS_NOT_BET
     THEN FIRST_MATCH MP_TAC BOUNDS_IN
     THEN ASM_MESON_TAC [NOT_BET_BOUND]);;

let BOUND_EQ2 = prove
  (`!X A B P Q. BOUNDS A B X /\ BOUNDS P Q X
   ==> A = P /\ B = Q \/ A = Q /\ B = P`,
   MESON_TAC [BOUNDS_SYM;BOUND_EQ;BOUNDS_REFL]);;

let CARD_3_BOUNDS = prove
  (`!X. X HAS_SIZE 3 /\ COLLINEAR X ==> ?P Q. BOUNDS P Q X`,
   GEN_TAC THEN REWRITE_TAC [IMP_CONJ]
     THEN DISCH_THEN (REPEAT_TCL CHOOSE_THEN ASSUME_TAC
                        o CONV_RULE HAS_SIZE_CONV)
     THEN ASM_REWRITE_TAC [COLLINEAR;FORALL_IN_INSERT;NOT_IN_EMPTY]
     THEN ASM_MESON_TAC [four;BET_BOUNDS;INSERT_COMM]);;

let ORDERING  = new_definition
  `ORDERING f X <=> (!n. (FINITE X ==> n < CARD X) ==> f n IN X)
                    /\ (!x. x IN X ==> ?n. (FINITE X ==> n < CARD X)
                        /\ f n = x)                   
                    /\ !n n' n''. (FINITE X ==> n'' < CARD X)
                          /\ n < n' /\ n' < n'' 
                          ==> between (f n) (f n') (f n'')`;;

let UNWIND_FORALL_OR = prove
  (`!P R y. (!x. x = y \/ P x ==> R x) <=> R y /\ !x. P x ==> R x`,
   MESON_TAC []);;

let BET_ORDERING = prove
  (`!P Q R. between P Q R ==> ?f. ORDERING f {P,Q,R}`,
   REPEAT GEN_TAC THEN DISCH_TAC
     THEN EXISTS_TAC `\n. if n = 0 then P:point else if n = 1 then Q else R` 
     THEN REWRITE_TAC [ORDERING] THEN SIMP_TAC [FINITE_INSERT;FINITE_EMPTY]
     THEN FIRST_MATCH ASSUME_TAC BET_NEQS
     THEN PURE_SIMP_TAC [IN_INSERT;NOT_IN_EMPTY;CARD_CLAUSES
                        ;FINITE_INSERT;FINITE_EMPTY]
     THEN ASM_REWRITE_TAC [] THEN REPEAT CONJ_TAC
     THENL [ARITH_TAC
           ;REWRITE_TAC [ARITH_RULE `!n. n < SUC (SUC (SUC 0))
                                      <=> n = 0 \/ n = 1 \/ n = 2`
                        ;UNWIND_FORALL_OR;FORALL_UNWIND_THM2]
             THEN REPEAT CONJ_TAC THENL (map EXISTS_TAC [`0`;`1`;`2`])
             THEN ARITH_TAC
           ;REPEAT GEN_TAC THEN DISCH_TAC
             THEN SUBGOAL_THEN `n = 0 /\ n' = 1 /\ n'' = 2` ASSUME_TAC
         THENL [ASM_ARITH_TAC;ASM_REWRITE_TAC [ONE;TWO;NOT_SUC;SUC_INJ]]]);;

let EMPTY_ORDERING = prove
  (`?f. ORDERING f {}`,
   EXISTS_TAC `\n:num. @x:point. T` THEN REWRITE_TAC [ORDERING]
     THEN SIMP_TAC [FINITE_EMPTY;CARD_CLAUSES;LT;NOT_IN_EMPTY]);;

let SING_ORDERING = prove
  (`!x. ?f. ORDERING f {x}`,
   GEN_TAC THEN REWRITE_TAC [ORDERING]
     THEN SIMP_TAC [FINITE_EMPTY;FINITE_INSERT;CARD_CLAUSES;NOT_IN_EMPTY]
     THEN REWRITE_TAC [IMP_CONJ] THEN ASM_SIMP_TAC [LT]
     THEN EXISTS_TAC `\n:num. x:point` THEN SET_TAC []);;

let TWO_ORDERING = prove
  (`!x y. ?f. ORDERING f {x,y}`,
   REPEAT GEN_TAC THEN ASM_CASES_TAC `(x:point = y)`
     THENL [ASM_REWRITE_TAC [INSERT_INSERT;SING_ORDERING];ALL_TAC]
     THEN EXISTS_TAC `\n:num. if n = 0 then x:point else y`
       THEN REWRITE_TAC [ORDERING]
       THEN ASM_SIMP_TAC [FINITE_EMPTY;FINITE_INSERT;CARD_CLAUSES
                         ;IN_INSERT;NOT_IN_EMPTY]
       THEN REPEAT CONJ_TAC
       THENL [ARITH_TAC
             ;REWRITE_TAC [LT] THEN ASM_MESON_TAC [NOT_SUC]
             ;ARITH_TAC]);;

let THREE_ORDERING = prove
  (`!x y z. COLLINEAR {x,y,z} ==> ?f. ORDERING f {x,y,z}`,
   REPEAT GEN_TAC THEN ASM_CASES_TAC `(x:point=y) \/ x=z \/ y=z`
       THENL [FIRST_X_ASSUM (REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC)
                 THEN ASM_REWRITE_TAC [INSERT_INSERT;INSERT_COMM;TWO_ORDERING]
             ;ALL_TAC]
       THEN REWRITE_TAC [COLLINEAR;IN_INSERT;NOT_IN_EMPTY
                        ;UNWIND_FORALL_OR;FORALL_UNWIND_THM2]
       THEN ASM_MESON_TAC [four;BET_ORDERING;INSERT_COMM]);;
         
let CHOOSE_INFINITE = prove
  (`!n X:a->bool. INFINITE X ==> ?Y. Y SUBSET X /\ Y HAS_SIZE n`,
     ONCE_REWRITE_TAC [SWAP_FORALL_THM] THEN GEN_TAC
       THEN MATCH_MP_TAC num_INDUCTION THEN REWRITE_TAC [HAS_SIZE_CLAUSES] 
       THEN CONJ_TAC THENL [MESON_TAC [EMPTY_SUBSET]; ALL_TAC]
       THEN GEN_TAC THEN REWRITE_TAC [TAUT `P ==> Q ==> R <=> Q ==> P ==> R`]
       THEN SIMP_TAC []
       THEN DISCH_TAC THEN DISCH_THEN CHOOSE_TAC
       THEN SUBGOAL_THEN `INFINITE ((X:a->bool) DIFF Y)`
       (CHOOSE_TAC o REWRITE_RULE [GSYM MEMBER_NOT_EMPTY]
          o MATCH_MP INFINITE_NONEMPTY)
       THENL [ASM_MESON_TAC [INFINITE_DIFF_FINITE;HAS_SIZE];ALL_TAC]
       THEN EXISTS_TAC `x:a INSERT Y`
       THEN CONJ_TAC THENL [ASSUM_LIST SET_TAC
                           ;EXISTS_TAC `x:a` THEN EXISTS_TAC `Y:a->bool`
                             THEN ASSUM_LIST SET_TAC]);;

let ORDERING_INJ =
  let INFINITE_ORDERING_INJ = prove
    (`!f X m n. INFINITE X /\ ORDERING f X
     /\ (FINITE X ==> m < CARD X) /\ (FINITE X ==> n < CARD X)
     /\ f m = f n ==> m = n`,
     REWRITE_TAC [ORDERING] THEN SIMP_TAC [INFINITE]
       THEN REWRITE_TAC [IN_ELIM_THM]
       THEN GEN_TAC THEN GEN_TAC THEN MATCH_MP_TAC WLOG_LT
       THEN REWRITE_TAC [EQ_SYM_EQ;CONJ_ACI] THEN REPEAT GEN_TAC
       THEN REWRITE_TAC [IMP_CONJ] THEN DISCH_TAC
       THEN DISCH_THEN (MP_TAC o SPECL [`m:num`;`n:num`;`SUC n`])
       THEN ASM_REWRITE_TAC [LT] THEN MESON_TAC [BET_NEQS]) in
  let FINITE_ORDERING_INJ = prove
    (`!f X m n. FINITE X /\ ORDERING f X
     /\ (FINITE X ==> m < CARD X) /\ (FINITE X ==> n < CARD X)
     /\ f m = f n ==> m = n`,
     REPEAT GEN_TAC THEN REWRITE_TAC [IMP_CONJ;ORDERING]
       THEN SIMP_TAC [] THEN REPLICATE_TAC 3 DISCH_TAC
       THEN SUBGOAL_THEN `X = IMAGE (f:num->point) {n | n < CARD X}` ASSUME_TAC
         THENL [REWRITE_TAC [EXTENSION;IMAGE;IN_ELIM_THM]
                  THEN SIMP_TAC [CARD_NUMSEG_LT]
                  THEN ASM_MESON_TAC []; ALL_TAC]
         THEN MP_TAC (ISPECL [`{n | n < CARD (X:point->bool)}`;
                              `X:point->bool`;`f:num->point`]
                        IMAGE_IMP_INJECTIVE_GEN)
         THEN ASM_REWRITE_TAC [IN_ELIM_THM;FINITE_NUMSEG_LT;CARD_NUMSEG_LT]
         THEN ASM_MESON_TAC [])
  in prove
       (`!f X m n. ORDERING f X ==>
           (FINITE X ==> m < CARD X) /\ (FINITE X ==> n < CARD X)
           /\ f m = f n ==> m = n`,
        MESON_TAC [INFINITE;INFINITE_ORDERING_INJ;FINITE_ORDERING_INJ]);;

let SUBGOAL_ANT ttac thm =
  SUBGOAL_THEN (fst (dest_imp (concl thm))) (ttac o MATCH_MP thm);;

let ORDERING_REV =
  let split = TAUT `(p ==> a) /\ (q ==> b) ==> p /\ q ==> a /\ b` in
  let ariths =
    [ARITH_RULE `!n m x. m < x ==> x - m - 1 < x`
    ;ARITH_RULE `!n x. n < x ==> x - (x - n - 1) - 1 = n`
    ;ARITH_RULE `!m n x. m < x /\ n < x ==> x - n - 1 = x - m - 1 ==> n = m`
    ;ARITH_RULE `!m n x. m < x /\ n < x ==> m < n
      ==> x - n - 1 < x - m - 1`] in
    prove
      (`!f X. FINITE X ==> (ORDERING f X <=>
                              ORDERING (\n. f (CARD X - n - 1)) X)`,
       REPEAT GEN_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC [ORDERING]
         THEN EQ_TAC THEN
         (MATCH_MP_TAC split THEN CONJ_TAC
            THENL [MESON_TAC ariths;
                   DISCH_TAC THEN ONCE_REWRITE_TAC [BET_SYM]
                     THEN CONJ_TAC
                     THENL [ASM_MESON_TAC ariths
                           ;REPEAT GEN_TAC THEN DISCH_TAC
                             THEN SUBGOAL_THEN `n < CARD (X:point->bool)
                                                /\ n' < CARD X` MP_TAC
                             THENL [POP_ASSUM MP_TAC THEN ARITH_TAC
                                   ;ASM_MESON_TAC ariths]]]));;

let ORDERING_REV' = prove
  (`!f X. FINITE X ==> ORDERING f X
           ==> ?g. ORDERING g X /\ f 0 = g (CARD X - 1)
                   /\ f (CARD X - 1) = g 0`,
      REPEAT STRIP_TAC
        THEN EXISTS_TAC `\n. (f (CARD (X:point->bool) - n - 1)):point`
        THEN ASM_SIMP_TAC [GSYM ORDERING_REV]
        THEN REWRITE_TAC [ARITH_RULE `x - (x - 1) - 1 = 0`
                         ;ARITH_RULE `x - 0 - 1 = x - 1`]);;

let ORDER_THREE =
  prove (`!f X. FINITE X /\ 3 <= CARD X /\ ORDERING f X
                 ==> f 0 IN X /\ f 1 IN X /\ f (CARD X - 1) IN X
                     /\ between (f 0) (f 1) (f (CARD X - 1))`,
         REWRITE_TAC [IMP_CONJ] THEN SIMP_TAC [ORDERING] THEN
           MESON_TAC [ARITH_RULE `!x. 3 <= x ==> 0 < x /\ 1 < x
                      /\ x - 1 < x /\ 0 < 1 /\ 1 < x - 1`]);;

let ORDERING_BOUNDS = prove
  (`!f X x. ORDERING f X /\ x IN X /\ FINITE X
      ==> BOUNDS (f 0) (f (CARD X - 1)) X`,
   REPEAT GEN_TAC THEN REWRITE_TAC [IMP_CONJ;ORDERING;BOUNDS
                                   ;IN_DIFF;IN_INSERT;NOT_IN_EMPTY]
     THEN REPEAT DISCH_TAC
     THEN SUBGOAL_THEN `0 < CARD (X:point->bool)` ASSUME_TAC
     THENL [ASM_SIMP_TAC [LT_NZ;CARD_EQ_0] THEN ASSUM_LIST SET_TAC; ALL_TAC]
     THEN ASM_SIMP_TAC [ARITH_RULE `0 < x ==> x - 1 < x`]
     THEN REWRITE_TAC [IMP_CONJ] THEN GEN_TAC
     THEN DISCH_THEN (fun thm -> FIRST_ASSUM (CHOOSE_TAC o C MATCH_MP thm))
     THEN DISCH_TAC
     THEN SUBGOAL_THEN `~(n = 0) /\ ~(n = CARD (X:point->bool) - 1)` ASSUME_TAC
     THENL [ASM_MESON_TAC []
           ;ASM_MESON_TAC [ARITH_RULE
                             `~(n = 0) /\ ~(n = x - 1) /\ n < x
                                ==> 0 < n /\ n < x - 1`
                          ;ARITH_RULE `0 < x ==> x - 1 < x`]]);;

let five21,five22 =
  prove (`!A B C D. between A B C /\ between A C D ==> between A B D`,
         MESON_TAC [five2]),
  prove (`!A B C D. between A B C /\ between A C D ==> between B C D`,
         MESON_TAC [five2]);;

let ORDER_EXTEND =
  prove (`!f x X. FINITE X /\ ORDERING f X /\ between (f 0) (f (CARD X - 1)) x
         ==> ?g. ORDERING g (x INSERT X)`,
         REPEAT GEN_TAC THEN REWRITE_TAC [IMP_CONJ] THEN DISCH_TAC
           THEN ASM_CASES_TAC `x:point IN X`
           THENL [ASM_SIMP_TAC [SET_RULE `!x:a X. x IN X ==> x INSERT X = X`]
                    THEN MESON_TAC []; ALL_TAC]
           THEN ASM_CASES_TAC `X:point->bool = {}`
           THENL [ASM_SIMP_TAC [SING_ORDERING];ALL_TAC]
           THEN SUBGOAL_THEN `0 < CARD X /\ CARD (X:point->bool) - 1 < CARD X`
             ASSUME_TAC
           THENL [MATCH_MP_TAC (ARITH_RULE `~(x = 0) ==> 0 < x /\ x - 1 < x`)
                    THEN ASM_SIMP_TAC [CARD_EQ_0]; ALL_TAC]
           THEN FIRST_X_ASSUM (X_CHOOSE_TAC `y:point`
                                 o REWRITE_RULE [GSYM MEMBER_NOT_EMPTY])
           THEN ASSUME_ANT THEN REWRITE_TAC [ORDERING;FORALL_IN_INSERT]
           THEN ASM_SIMP_TAC [FINITE_INSERT;CARD_CLAUSES]
           THEN MP_TAC (SPECL [`f:num->point`;`X:point->bool`;`y:point`]
                          ORDERING_BOUNDS)
           THEN ASM_REWRITE_TAC [BOUNDS;IN_DIFF;IN_INSERT;NOT_IN_EMPTY]
           THEN DISCH_THEN (ASSUME_TAC o last o CONJUNCTS)
           THEN REPEAT DISCH_TAC
           THEN EXISTS_TAC `\n:num. if n < CARD (X:point->bool)
                                    then f n else x:point`
           THEN REPEAT CONJ_TAC
           THENL [REWRITE_TAC [LT;LT_REFL] THEN ASM_MESON_TAC [LT]
                 ;EXISTS_TAC `CARD (X:point->bool)`
                   THEN REWRITE_TAC [LT;LT_REFL]
                 ;ASM_MESON_TAC [LT]
                 ;ALL_TAC]
           THEN REPEAT GEN_TAC THEN REPEAT DISCH_TAC
           THEN ASM_CASES_TAC `n'' < CARD (X:point->bool)`
           THENL [ASM_MESON_TAC [LT_TRANS];ALL_TAC]
           THEN POP_ASSUM MP_TAC
           THEN ASM_SIMP_TAC [ARITH_RULE `n < SUC m ==> (~(n < m) <=> n = m)`]
           THEN DISCH_THEN (fun thm -> FULL_REWRITE_TAC [LT;LT_REFL;thm])
           THEN ASM_CASES_TAC `n = 0`
           THEN ASM_CASES_TAC `n' = CARD (X:point->bool) - 1`
           THENL [ASM_MESON_TAC []
                 ;MATCH_MP_TAC five21
                    THEN EXISTS_TAC `f (CARD (X:point->bool) - 1):point`
                    THEN ASM_MESON_TAC [LT_REFL;ORDERING_INJ]
                 ;MATCH_MP_TAC five22 THEN EXISTS_TAC `f 0:point`
                   THEN ASM_MESON_TAC [LT_REFL;LT_TRANS;ORDERING_INJ]
                 ;MATCH_MP_TAC five22 THEN EXISTS_TAC `f 0:point`
                   THEN CONJ_TAC
                   THENL [ASM_MESON_TAC [LT_NZ;LT_TRANS]
                         ;MATCH_MP_TAC five21
                           THEN EXISTS_TAC `f (CARD (X:point->bool) - 1):point` 
                           THEN ASM_MESON_TAC [LT;ORDERING_INJ]]]);;

let CHOOSE_ORDER =
  prove (`!f P Q X x. ORDERING f X /\ x IN X /\ FINITE X ==> BOUNDS P Q X
         ==> ?f'. ORDERING f' X /\ f' 0 = P /\ f' (CARD X - 1) = Q`,
         REPEAT GEN_TAC THEN DISCH_TAC THEN FIRST_ASSUM
           (MP_TAC o MATCH_MP ORDERING_BOUNDS)
           THEN REWRITE_TAC [IMP_IMP]
           THEN DISCH_THEN (DISJ_CASES_TAC o MATCH_MP BOUND_EQ2)
           THENL [ASM_MESON_TAC []
                 ;EXISTS_TAC `\n. (f:num->point)
                   (CARD (X:point->bool) - n - 1)`
                   THEN REWRITE_TAC [GSYM ORDERING_REV;SUB_0]
                   THEN ASM_MESON_TAC
                   [BOUNDS_SYM;BOUND_EQ;ORDERING
                   ;ORDERING_REV;MEMBER_NOT_EMPTY;CARD_EQ_0
                   ;ARITH_RULE `!x. ~(x = 0) ==> x - (x - 1) - 1 = 0`]]);;

let ORDERING_COL =
  prove (`ORDERING f X ==> COLLINEAR X`,
         REWRITE_TAC [ORDERING;COLLINEAR;IMP_CONJ] THEN DISCH_TAC
           THEN DISCH_THEN (LABEL_TAC "onto")
           THEN ASM_CASES_TAC `?x y. x:point IN X /\ y IN X /\ ~(x=y)`
           THENL
             [FIRST_X_ASSUM
                (REPEAT_TCL CHOOSE_THEN (MAP_EVERY ASSUME_TAC o CONJUNCTS))
                THEN FIRST_ASSUM (CHOOSE_TAC o MATCH_MP g11)
                THEN DISCH_TAC THEN EXISTS_TAC `a:line` THEN GEN_TAC
                THEN DISCH_TAC THEN REMOVE_THEN "onto"
                  (fun thm -> REPEAT (FIRST_X_ASSUM
                                        (CHOOSE_TAC o MATCH_MP thm)))
                THEN SUBGOAL_THEN
                  `!x y z. (FINITE (X:point->bool) ==> x < CARD X)
                     /\ (FINITE (X:point->bool) ==> y < CARD X)
                     /\ (FINITE (X:point->bool) ==> z < CARD X)
                     ==> ?a. on_line (f x) a /\ on_line (f y) a
                             /\ on_line (f z) a`
                  (ASSUME_TAC o SPECL [`n:num`;`n':num`;`n'':num`])
                THENL [MATCH_MP_TAC WLOG_LT3
                         THEN REPEAT CONJ_TAC
                         THENL [MESON_TAC [g11_weak]
                               ;REWRITE_TAC [CONJ_ACI]
                               ;REWRITE_TAC [CONJ_ACI]
                               ;REPEAT GEN_TAC
                                 THEN FIRST_X_ASSUM
                                 (MP_TAC o SPECL [`x':num`;`y':num`;`z:num`])
                                 THEN MESON_TAC [g21]]
                      ;ASM_MESON_TAC [g12]]
             ;ASM_MESON_TAC [g11_weak]]);;
           
let COLLINEAR_INSERT =
  prove (`!X x. COLLINEAR (x INSERT X) ==> COLLINEAR X`,
         REWRITE_TAC [COLLINEAR] THEN SET_TAC []);;

let lemma =
  prove (`!X f n. 2 <= n /\ X HAS_SIZE n /\ ORDERING f X
         ==> ~(f 0 = f (n - 1)) /\ f 0 IN X /\ f (n - 1) IN X`,
         REPEAT GEN_TAC THEN REWRITE_TAC [HAS_SIZE] THEN DISCH_TAC
           THEN MP_TAC (ISPEC `X:point->bool` CHOOSE_SUBSET)
           THEN ASM_REWRITE_TAC []
           THEN DISCH_THEN (MP_TAC o SPEC `2`) THEN ASM_REWRITE_TAC []
           THEN DISCH_THEN (CHOOSE_THEN MP_TAC)
           THEN CONV_TAC (ONCE_DEPTH_CONV HAS_SIZE_CONV) THEN DISCH_TAC
           THEN SUBGOAL_THEN `BOUNDS (f 0) (f (n - 1)) X` MP_TAC
           THENL [ASSUM_LIST (fun thms -> SET_TAC (ORDERING_BOUNDS :: thms))
                 ; ALL_TAC]
           THEN DISCH_TAC THEN CONJ_TAC
           THENL [DISCH_TAC THEN SUBGOAL_THEN `X = {(f 0):point}` MP_TAC
                  THENL [ASM_MESON_TAC [BOUNDS_REFL];ALL_TAC]
                  THEN ASSUM_LIST SET_TAC
                 ;ASSUM_LIST (fun thms -> SET_TAC (BOUNDS :: thms))]);;

g `!X. FINITE X /\ COLLINEAR X ==> ?f. ORDERING f X`;;
e (REWRITE_TAC [FINITE_HAS_SIZE]);;
e GEN_TAC;;
e (SPEC_TAC (`CARD (X:point->bool)`,`n:num`));;
e (SPEC_TAC (`X:point->bool`,`X:point->bool`));;
e (ONCE_REWRITE_TAC [SWAP_FORALL_THM]);;
e (MATCH_MP_TAC num_INDUCTION);;
e (CONJ_TAC THENL [ASM_MESON_TAC [HAS_SIZE_0;EMPTY_ORDERING]; ALL_TAC]);;
e GEN_TAC;;
e (DISCH_THEN (LABEL_TAC "ind_hyp"));;
e GEN_TAC;;
e (ASM_CASES_TAC `n < 3`);;
e (POP_ASSUM (REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC o MATCH_MP (ARITH_RULE `n < 3 ==> SUC n = 1 \/ SUC n = 2 \/ SUC n = 3`)) THEN ASM_REWRITE_TAC [] THEN CONV_TAC (ONCE_DEPTH_CONV HAS_SIZE_CONV)
     THEN ASM_MESON_TAC [SING_ORDERING;TWO_ORDERING;THREE_ORDERING]);;
e (FIRST_X_ASSUM (ASSUME_TAC o MATCH_MP (ARITH_RULE `!n. ~(n < 3) ==> 2 <= n`)));;
e (REWRITE_TAC [IMP_CONJ]);;
e (REWRITE_TAC [HAS_SIZE_CLAUSES]);;
e (DISCH_THEN (REPEAT_TCL CHOOSE_THEN (LABEL_TAC "inserted")));;
e DISCH_TAC;;
e (SUBGOAL_THEN `?f. ORDERING f t` CHOOSE_TAC);;
e (ASM_MESON_TAC [COLLINEAR_INSERT]);;

e (SUBGOAL_THEN `CARD (t:point -> bool) = n` ASSUME_TAC);;
e (ASM_MESON_TAC [HAS_SIZE]);;

e (SUBGOAL_THEN `~((f 0):point = f (n - 1)) /\ f 0 IN t /\ f (n - 1) IN t` ASSUME_TAC);;
e (ASM_MESON_TAC [lemma]);;

e (SUBGOAL_THEN `between (f 0) a (f (n - 1))
                 \/ between a (f 0) (f (n - 1))
                 \/ between (f 0) (f (n - 1)) a` MP_TAC);;

e (SUBGOAL_THEN `?b. on_line (f 0) b /\ on_line (f (n - 1)) b /\ on_line a b` ASSUME_TAC);;
e (ASM_MESON_TAC [REWRITE_RULE [BOUNDS] ORDERING_BOUNDS;IN_INSERT;COLLINEAR]);;
e (ASM_MESON_TAC [four]);;

e (DISCH_THEN DISJ_CASES_TAC);;

e (SUBGOAL_THEN `?s. f (n - 1) INSERT s = X:point->bool /\ s HAS_SIZE n /\ ~(f (n - 1) IN s)`
   (CHOOSE_TAC o GSYM));;
e (EXISTS_TAC `X DELETE (f (n - 1)):point`);;

e CONJ_TAC;;
e (ASM_MESON_TAC [INSERT_DELETE;IN_INSERT;IN_DELETE]);;

e (SUBGOAL_THEN `f (n - 1) IN X:point->bool` ASSUME_TAC);;
e (ASM_MESON_TAC [BOUNDS;ORDERING_BOUNDS;IN_INSERT]);;

e (SUBGOAL_THEN `X:point->bool HAS_SIZE SUC n` ASSUME_TAC);;
e (ASM_MESON_TAC [HAS_SIZE_CLAUSES]);;
e (ASM_MESON_TAC [HAS_SIZE_SUC;IN_DELETE]);;

e (SUBGOAL_THEN `f 0 IN s:point->bool` ASSUME_TAC);;
e (ASM_MESON_TAC [ORDERING_BOUNDS;BOUNDS;IN_INSERT;ORDER_THREE;BET_NEQS]);;

e (SUBGOAL_THEN `t SUBSET X:point->bool` ASSUME_TAC);;
e (ASSUM_LIST SET_TAC);;

(*e (REMOVE_THEN "inserted" (ASSUME_TAC o GSYM));;*)

e (SUBGOAL_THEN `?g. ORDERING g (s:point->bool)` CHOOSE_TAC);;
e (ASM_MESON_TAC [COLLINEAR_INSERT]);;

e (SUBGOAL_THEN `?h. ORDERING h (s:point->bool) /\ (f 0):point = h 0` (CHOOSE_THEN (CONJUNCTS_THEN ASSUME_TAC)));;

e (SUBGOAL_THEN `!A B. A IN s /\ B IN s ==> ~between A (f 0) B` MP_TAC);;

e (ONCE_REWRITE_TAC [TAUT `P <=> ~(~P)`]);;
e (PURE_REWRITE_TAC [NOT_FORALL_THM]);;
e (ONCE_REWRITE_TAC [TAUT `~((P /\ Q) ==> ~R) <=> P /\ Q /\ R`]);;
e (DISCH_THEN (REPEAT_TCL CHOOSE_THEN ASSUME_TAC));;

e (SUBGOAL_THEN `~(A:point IN t /\ B IN t)` ASSUME_TAC);;
e (ASM_MESON_TAC [ORDERING_BOUNDS;BOUNDS_NOT_BET;HAS_SIZE]);;
e (SUBGOAL_THEN `A:point = a \/ B = a` DISJ_CASES_TAC);;
e (ASM_MESON_TAC [IN_INSERT]);;

(* !!!!!!!!!!!!!!!!!!!!!! *)
  e (SUBGOAL_THEN `B:point IN t` ASSUME_TAC);;
  e (ASM_MESON_TAC [g21;IN_INSERT]);;

  e (SUBGOAL_THEN `~(B:point = f (n - 1))` ASSUME_TAC);;
  e (ASM_MESON_TAC [BET_SYM;g23]);;
  e (SUBGOAL_THEN `between (f 0) B (f (n - 1))` ASSUME_TAC);;
  e (ASM_MESON_TAC [REWRITE_RULE [IN_DIFF;NOT_IN_EMPTY;IN_INSERT] BOUNDS; ORDERING_BOUNDS; BET_NEQS; HAS_SIZE]);;

  e (ASM_MESON_TAC [five1;g23;BET_SYM]);;

(* HOW DO WE DO WLOG HERE!? *) 
  e (SUBGOAL_THEN `A:point IN t` ASSUME_TAC);;
  e (ASM_MESON_TAC [g21;IN_INSERT]);;

  e (SUBGOAL_THEN `~(A:point = f (n - 1))` ASSUME_TAC);;
  e (ASM_MESON_TAC [BET_SYM;g23]);;
  e (SUBGOAL_THEN `between (f 0) A (f (n - 1))` ASSUME_TAC);;
  e (ASM_MESON_TAC [REWRITE_RULE [IN_DIFF;NOT_IN_EMPTY;IN_INSERT] BOUNDS; ORDERING_BOUNDS; BET_NEQS; HAS_SIZE]);;

  e (ASM_MESON_TAC [five1;g23;BET_SYM]);;

e DISCH_TAC;;
e (SUBGOAL_THEN `(f 0):point = g 0 \/ f 0 = g (CARD (s:point->bool) - 1)` ASSUME_TAC);;
e (MATCH_MP_TAC (REWRITE_RULE [IMP_IMP] NOT_BET_BOUND));;
e (EXISTS_TAC `s:point->bool`);;
e (ASM_REWRITE_TAC []);;
e (ASM_MESON_TAC [HAS_SIZE;ORDERING_BOUNDS]);;

e (ASM_MESON_TAC [BOUNDS_SYM;ORDERING_BOUNDS;CHOOSE_ORDER;HAS_SIZE]);;
(* We've got an ordering of X - {f (CARD t - 1)} starting at the point f 0. *)
e (ASM_CASES_TAC `a:point = h (n - 1)`);;
e (ASM_MESON_TAC [ORDER_EXTEND;HAS_SIZE]);;

e (SUBGOAL_THEN `n = CARD (s:point->bool)` ASSUME_TAC);;
e (ASM_MESON_TAC [HAS_SIZE]);;
e (SUBGOAL_THEN `~(h (n - 1) = (f 0):point) /\ ~(h (n - 1) = f (n - 1))` ASSUME_TAC);;
e (MP_TAC (SPECL [`h:num->point`;`s:point->bool`] ORDERING_INJ));;
e (SUBGOAL_THEN `h (n - 1) IN s:point->bool` ASSUME_TAC);;
e (ASM_MESON_TAC [ORDERING_BOUNDS;BOUNDS;HAS_SIZE]);;
e (ASM_MESON_TAC [ARITH_RULE `!n.2 <= n ==> ~(n - 1 = 0) /\ n - 1 < n /\ 0 < n`;HAS_SIZE]);;

e (SUBGOAL_THEN `h (n - 1) IN t:point->bool` ASSUME_TAC);;
e (SUBGOAL_THEN `h (n - 1) IN X:point->bool` ASSUME_TAC);;
e (ASM_MESON_TAC [ORDERING_BOUNDS;BOUNDS;IN_INSERT;HAS_SIZE]);;
e (ASM_MESON_TAC [IN_INSERT]);;
e (SUBGOAL_THEN `between ((f 0):point) (h (n - 1)) (f (n - 1))` ASSUME_TAC);;
e (ASM_MESON_TAC [REWRITE_RULE [IN_DIFF;NOT_IN_EMPTY;IN_INSERT] BOUNDS; ORDERING_BOUNDS;HAS_SIZE]);;
e (ASM_MESON_TAC [ORDER_EXTEND;HAS_SIZE]);;

(* Hard case done! *)
(* The last two cases are symmetric. We can eliminate them to one *)
e (SUBGOAL_THEN `?g. ORDERING g t /\ between (g 0) (g (n - 1)) a` ASSUME_TAC);;
e (ASM_MESON_TAC [ORDERING_REV';BET_SYM;HAS_SIZE]);;
e (ASM_MESON_TAC [ORDER_EXTEND;HAS_SIZE]);;
let theorem6 = top_thm ();;

let ORDERING_LT = prove
  (`!f X n. (FINITE X ==> n <= CARD X) /\ ORDERING f X
   ==> ORDERING f (IMAGE f {m | m < n})`,
   REPEAT GEN_TAC THEN REWRITE_TAC [IMP_CONJ] THEN ASM_REWRITE_TAC []
     THEN DISCH_TAC THEN ASSUME_ANT_THEN (MP_TAC o MATCH_MP ORDERING_INJ)
     THEN ASM_REWRITE_TAC [] THEN DISCH_TAC
     THEN SUBGOAL_THEN `!m p. m < n ==> p < n ==> (f m):point = f p ==> m = p`
         (ASSUME_TAC o MATCH_MP
            (REWRITE_RULE [IN_ELIM_THM;IMP_CONJ;FINITE_NUMSEG_LT]
               (ISPECL [`f:num->point`;`{m | m < n}`] CARD_IMAGE_INJ)))
     THENL [ASM_MESON_TAC [LTE_TRANS]; ALL_TAC] 
     THEN ASM_REWRITE_TAC [ORDERING;CARD_NUMSEG_LT;IN_IMAGE;IN_ELIM_THM]
     THEN SIMP_TAC [FINITE_IMAGE;FINITE_NUMSEG_LT]
     THEN ASM_MESON_TAC [LTE_TRANS]);;

let ORDERING_PRED =
  prove (`!f X. ORDERING f X /\ x IN X /\ FINITE X
         ==> ORDERING f (X DELETE f (CARD X - 1))`,
         REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC [ORDERING]
           THEN SUBGOAL_THEN `f (CARD X - 1) IN X:point->bool` ASSUME_TAC
         THENL [ASM_MESON_TAC [ORDERING_BOUNDS;BOUNDS];ALL_TAC]
         THEN ASM_SIMP_TAC [FINITE_DELETE;CARD_DELETE]
         THEN REWRITE_TAC [IN_DELETE]
             THEN SUBGOAL_THEN `~(CARD (X:point->bool) = 0)` ASSUME_TAC
         THENL [ASM_MESON_TAC [NOT_IN_EMPTY;CARD_EQ_0]; ALL_TAC]
         THEN REPEAT CONJ_TAC 
         THENL [ASM_MESON_TAC [ARITH_RULE `(~(x=0) ==> x - 1 < x)
                                /\ (n < x - 1 ==> n < x)`
                              ;ORDERING;ORDERING_INJ;LT_REFL]
               ;X_GEN_TAC `y:point` THEN DISCH_TAC
                 THEN SUBGOAL_THEN
                 `?n. n < CARD (X:point->bool) /\ f n = y:point` CHOOSE_TAC
                 THENL [ASM_MESON_TAC [ORDERING];ALL_TAC]
                 THEN EXISTS_TAC `n:num` THEN ASM_MESON_TAC
                 [ARITH_RULE `n < x /\ ~(n = x - 1) ==> n < x - 1`]
               ;ASM_MESON_TAC
                 [ARITH_RULE `(~(x=0) ==> x - 1 < x) /\ (n < x - 1 ==> n < x)`
                 ;ORDERING]]);;

let Z_NBET =
  let lemma =
    MESON [g23;BET_SYM;BET_NEQS]
      `A = B \/ A = C \/ B = C \/ between A B C \/ between B A C
                  ==> ~between A C B` in
  prove
    (`!f A B x X. A IN X /\ B IN X /\ ORDERING f X ==> ~between A (f 0) B`,
     REPEAT GEN_TAC THEN REWRITE_TAC [ORDERING] THEN STRIP_TAC
       THEN MATCH_MP_TAC lemma THEN ONCE_REWRITE_TAC [BET_SYM] 
       THEN FIRST_X_ASSUM (fun thm -> FIRST_ASSUM
         (CHOOSE_TAC o ONCE_REWRITE_RULE [EQ_SYM_EQ] o C MATCH_MP thm))
       THEN FIRST_X_ASSUM (fun thm -> FIRST_ASSUM
         (CHOOSE_TAC o ONCE_REWRITE_RULE [EQ_SYM_EQ] o C MATCH_MP thm))
       THEN ASM_MESON_TAC [ARITH_RULE `~(x=y) ==> x < y \/ y < x`
                          ;ARITH_RULE `~(x=0) ==> 0 < x`]);;

let rec permutations = function
    []             -> [[]]
  | (x::xs) as xss ->
      Bl.concat
        (map (fun y ->
                map (fun ps -> y :: ps)
                  (permutations (Bl.remove xss y))) xss);;

let ORDERING_BET = prove
  (`!f X m n p. ORDERING f X 
    /\ (FINITE X ==> m < CARD X)
    /\ (FINITE X ==> n < CARD X)
    /\ (FINITE X ==> p < CARD X)
    ==> (m < n /\ n < p \/ p < n /\ n < m
         <=> between (f m) (f n) (f p))`,
   REWRITE_TAC [ORDERING] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN EQ_TAC
     THENL [ASM_MESON_TAC [BET_SYM]; ALL_TAC]
     THEN FIRST_X_ASSUM (fun thm -> MAP_EVERY
                           (fun ps -> (MP_TAC (SPECL ps thm)))
                           (permutations [`m:num`;`n:num`;`p:num`]))
     THEN REPEAT DISCH_TAC THEN SIMP_ASM_TAC
     [BET_SYM;MESON [BET_SYM;g23]
        `!A B C. between A B C ==> ~between A C B /\ ~between B A C
                                   /\ ~between B C A /\ ~between C A B`]
     THEN SUBGOAL_THEN `~(n:num = m) /\ ~(n = p) /\ ~(m = p)` ASSUME_TAC
     THENL [POP_ASSUM MP_TAC THEN MESON_TAC [BET_NEQS]; ALL_TAC]
     THEN REPLICATE_TAC 8 (POP_ASSUM MP_TAC) THEN ARITH_TAC);;

(* We prove by induction. The base-case is trivial. For the step case, we
   assume that
     f(n+1) != g(n+1)
   and consider the split
     f0 f(n+1) g(n+1)
     f0 g(n+1) f(n+1)
     f(n+1) f0 g(n+1)

   The last case contradicts Z_NBET. For
     f0 f(n+1) g(n+1)
   we obtain gn f(n+1) g(n+1) (if n!=0, we use five22 with f0 fn f(n+1))
   whence we have a contradiction since there can be no value between gn and
   g(n+1). We do similarly for the other case.*)

let ORDERING_START_UNIQUE = prove
  (`!f g X. ORDERING f X /\ ORDERING g X /\ f 0 = g 0
  ==> !n. (FINITE X ==> n < CARD X) ==> f n = g n`,
   REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC num_INDUCTION
     THEN ASM_REWRITE_TAC [] THEN GEN_TAC
     THEN REWRITE_TAC [TAUT `P ==> Q ==> R <=> Q ==> P ==> R`]
     THEN SIMP_TAC [TAUT `(Q <=> R) ==> ((P ==> Q) <=> (P ==> R))`
                   ;ARITH_RULE `SUC n < x ==> n < x`]
     THEN REPEAT DISCH_TAC THEN REFUTE_THEN ASSUME_TAC
     THEN SUBGOAL_THEN `between (f 0) (f (SUC n)) (g (SUC n))
                        \/ between (f (SUC n)) (f 0) (g (SUC n))
                        \/ between (f 0) (g (SUC n)) (f (SUC n))` MP_TAC
     THENL [MATCH_MP_TAC (REWRITE_RULE [IMP_IMP]
                            (SPECL [`f 0:point`;`f(SUC n):point`
                                   ;`g(SUC n):point`] four))
               THEN REWRITE_TAC [LEFT_EXISTS_AND_THM] THEN STRIP_TAC
               THENL [FIRST_ASSUM (ASSUME_TAC o REWRITE_RULE [COLLINEAR]
                                     o MATCH_MP ORDERING_COL)
                         THEN ASM_MESON_TAC [ORDERING
                                            ;ARITH_RULE `SUC n < x ==> 0 < x`]
                     ;ASM_MESON_TAC [ORDERING_INJ;ORDERING
                                    ;ARITH_RULE `SUC n < x ==> 0 < x`]]
           ;ALL_TAC]
     THEN PURE_ONCE_REWRITE_TAC [TAUT `P \/ Q \/ R <=> Q \/ (P \/ R)`]
     THEN DISCH_THEN DISJ_CASES_TAC
     THENL [ASM_MESON_TAC [Z_NBET;ORDERING]; ALL_TAC]
     THEN FIRST_X_ASSUM DISJ_CASES_TAC
     THENL [SUBGOAL_THEN `?m. (FINITE X ==> m < CARD (X:point->bool))
             /\ f (SUC n) = (g m):point` CHOOSE_TAC
         THENL [ASM_MESON_TAC [ORDERING]; ALL_TAC]
         THEN SUBGOAL_THEN `between (f n) (f (SUC n)) (g (SUC n))` MP_TAC
         THENL [ASM_CASES_TAC `n = 0` THENL
             [ASM_MESON_TAC [];
              MATCH_MP_TAC five22 THEN EXISTS_TAC `f 0:point`
                THEN ASM_MESON_TAC [ORDERING;ARITH_RULE
                  `~(n=0) ==> 0 < n /\ n < SUC n`]]
               ;ASM_REWRITE_TAC [] THEN SUBGOAL_THEN
                 `(FINITE (X:point->bool) ==> 0 < CARD X)
                 /\ (FINITE X ==> n < CARD X)` ASSUME_TAC
                 THENL [ASM_MESON_TAC
                           [ARITH_RULE `SUC n < x ==> n < x /\ 0 < x`];ALL_TAC]
                 THEN MP_TAC (SPECL [`g:num->point`;`X:point->bool`]
                                (GSYM ORDERING_BET))
                 THEN ASM_SIMP_TAC [GSYM ORDERING] THEN ARITH_TAC]
           ;ONCE_REWRITE_ASM_TAC [EQ_SYM_EQ]
             THEN SUBGOAL_THEN
             `?m. (FINITE X ==> m < CARD (X:point->bool))
                  /\ g (SUC n) = (f m):point` CHOOSE_TAC
             THENL [ASM_MESON_TAC [ORDERING]; ALL_TAC]
             THEN SUBGOAL_THEN `between (g n) (g (SUC n)) (f (SUC n))` MP_TAC
             THENL [ASM_CASES_TAC `n = 0` THENL
                     [ASM_MESON_TAC [];
                      MATCH_MP_TAC five22 THEN EXISTS_TAC `g 0:point`
                        THEN ASM_MESON_TAC [ORDERING
                                           ;ARITH_RULE `~(n=0) ==> 0 < n
                                             /\ n < SUC n`]]
                   ;ASM_REWRITE_TAC []
                     THEN SUBGOAL_THEN
                     `(FINITE (X:point->bool) ==> 0 < CARD X)
                     /\ (FINITE X ==> n < CARD X)` ASSUME_TAC
                     THENL [ASM_MESON_TAC
                               [ARITH_RULE `SUC n < x ==> n < x /\ 0 < x`]
                           ;ALL_TAC]
                     THEN MP_TAC (SPECL [`f:num->point`;`X:point->bool`]
                                    (GSYM ORDERING_BET))
                     THEN ASM_SIMP_TAC [GSYM ORDERING] THEN ARITH_TAC]]);;

let TWO_ORDERS = prove
  (`!f g X. FINITE X /\ ORDERING f X /\ ORDERING g X ==>
               (!n. (FINITE X ==> n < CARD X) ==> f n = g n)
               \/ !n. (FINITE X ==> n < CARD X) ==> f n = g (CARD X - n - 1)`,
   REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_CASES_TAC `?x:point. x IN X`
     THENL [FIRST_X_ASSUM CHOOSE_TAC THEN MP_TAC
               (CONJ (SPECL [`f:num->point`;`X:point->bool`;`x:point`]
                        ORDERING_BOUNDS)
                  (SPECL [`g:num->point`;`X:point->bool`;`x:point`]
                     ORDERING_BOUNDS))
               THEN ASM_REWRITE_TAC []
               THEN DISCH_THEN (DISJ_CASES_TAC o MATCH_MP BOUND_EQ2)
               THEN ASM_MESON_TAC
               [ARITH_RULE `CARD (X:point->bool) - 0 - 1 = CARD X - 1`
               ;ORDERING_REV;ORDERING_START_UNIQUE]
           ;ASM_MESON_TAC [MEMBER_NOT_EMPTY;CARD_EQ_0;LT]]);;

let INVERSE = new_definition
  `INVERSE (f:a->b) g X Y <=> (!x. x IN X ==> f x IN Y /\ g (f x) = x)
                              /\ (!y. y IN Y ==> g y IN X /\ f (g y) = y)`;;

let INVERSE_INJ =
  prove (`!f g X Y. INVERSE f g X Y ==> INJ f X Y`,
         REWRITE_TAC [INVERSE;INJ] THEN MESON_TAC []);;

let INVERSE_SURJ =
  prove (`!f g X Y. INVERSE f g X Y ==> SURJ f X Y`, 
         REWRITE_TAC [INVERSE;SURJ] THEN MESON_TAC []);;

let bet_leq =
  let order_inverse = prove
    (`!f X. ORDERING f X ==>
        ?g. (!x. x IN X ==> g x IN {n | FINITE X ==> n < CARD X}) /\
        (!x. x IN X ==> f (g x) = x) /\
        (!n. (FINITE X ==> n < CARD X) ==> g (f n) = n)`,
     REPEAT GEN_TAC THEN DISCH_TAC
       THEN FIRST_ASSUM (MP_TAC o MATCH_MP ORDERING_INJ)
       THEN FIRST_ASSUM (MP_TAC o REWRITE_RULE [ORDERING])
       THEN REWRITE_TAC [IMP_CONJ;IN_ELIM_THM]
       THEN DISCH_TAC THEN DISCH_TAC THEN DISCH_THEN (K ALL_TAC)
       THEN DISCH_TAC THEN FIRST_X_ASSUM
       (ASSUME_TAC o MATCH_MP
          (REWRITE_RULE [IMP_IMP;IN_ELIM_THM]
             (ISPECL [`f:num->point`;
                      `{n | FINITE X ==> n < CARD (X:point->bool)}`
                      ;`X:point->bool`] BIJECTIVE_ON_LEFT_RIGHT_INVERSE)))
       THEN FIRST_X_ASSUM (ASSUME_TAC o MATCH_MP EQ_IMP)
       THEN REWRITE_TAC [IMP_IMP]
       THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC []) in
  prove (`!X. FINITE X /\ COLLINEAR X ==>
            ?g. (!A B C. A IN X /\ B IN X /\ C IN X ==>
                    (between A B C <=> (g A < g B /\ g B < g C)
                       \/ (g C < g B /\ g B < g A)))           
            /\ (!A B. A IN X /\ B IN X ==> ((A = B) <=> (g A = g B)))`,
         GEN_TAC THEN DISCH_TAC
           THEN FIRST_ASSUM (CHOOSE_TAC o MATCH_MP theorem6)
           THEN FIRST_ASSUM (CHOOSE_TAC o REWRITE_RULE [IN_ELIM_THM]
                               o MATCH_MP order_inverse)
           THEN EXISTS_TAC `g:point->num` THEN CONJ_TAC
           THEN REPEAT GEN_TAC THEN DISCH_TAC 
           THEN ASSUME_TAC
             (SPECL [`f:num->point`;`X:point->bool`;`g (A:point):num`;
                     `g (B:point):num`;`g (C:point):num`] ORDERING_BET)
           THEN ASM_MESON_TAC []);;

(* The tactic works as follows: find collinear theorems then obtain an
   ordering. Rewrite all hypotheses and conclusion to replace between and
   equality formulas with formulas about linear ordering of natural
   numbers. *)
let (ORDER_TAC' : term -> thm list -> tactic) = 
  let bet_leq = prove (`!X. FINITE X /\ COLLINEAR X
         ==> (?g. (!C B A.
                       A IN X ==> B IN X ==> C IN X
                       ==> (between A B C <=>
                            g A < g B /\ g B < g C \/ g C < g B /\ g B < g A))
              /\ (!B A. A IN X ==> B IN X ==> (A = B <=> g A = g B)))`,
   REWRITE_TAC [SWAP_FORALL_THM;IMP_IMP;CONJ_ACI;REWRITE_RULE [CONJ_ACI]
     bet_leq]) in
  fun set thms ->
    POP_ASSUM_LIST (K (MAP_EVERY ASSUME_TAC thms))
      THEN SUBGOAL_THEN (mk_comb (`COLLINEAR`,set)) (fun col -> 
        MP_TAC (SPEC set bet_leq)
          THEN CONV_TAC
          (LAND_CONV (LAND_CONV
                        (REWRITE_CONV
                           [FINITE_INSERT;FINITE_EMPTY;col]))
             THENC REWRITE_CONV
             [FORALL_IN_INSERT;FORALL_AND_THM;NOT_IN_EMPTY])
          THEN DISCH_THEN (CHOOSE_THEN (FULL_REWRITE_TAC o CONJUNCTS)))
      THENL [REWRITE_TAC [COLLINEAR;FORALL_IN_INSERT;NOT_IN_EMPTY]
                THEN ASM_REWRITE_TAC [] THEN discover_tac
                (by_cols o Di.conjuncts) MESON_TAC
            ;ALL_TAC];;

let (ORDER_TAC : term -> thm list -> tactic) = 
  let bet_leq = prove (`!X. FINITE X /\ COLLINEAR X
         ==> (?g. (!C B A.
                       A IN X ==> B IN X ==> C IN X
                       ==> (between A B C <=>
                            g A < g B /\ g B < g C \/ g C < g B /\ g B < g A))
              /\ (!B A. A IN X ==> B IN X ==> (A = B <=> g A = g B)))`,
   REWRITE_TAC [SWAP_FORALL_THM;IMP_IMP;CONJ_ACI;REWRITE_RULE [CONJ_ACI]
     bet_leq]) in
  fun set thms ->
    POP_ASSUM_LIST (K (MAP_EVERY ASSUME_TAC thms))
      THEN SUBGOAL_THEN (mk_comb (`COLLINEAR`,set)) (fun col -> 
        MP_TAC (SPEC set bet_leq)
          THEN CONV_TAC
          (LAND_CONV (LAND_CONV
                        (REWRITE_CONV
                           [FINITE_INSERT;FINITE_EMPTY;col]))
             THENC REWRITE_CONV
             [FORALL_IN_INSERT;FORALL_AND_THM;NOT_IN_EMPTY])
          THEN DISCH_THEN (CHOOSE_THEN (FULL_REWRITE_TAC o CONJUNCTS))
          THEN ASM_ARITH_TAC)
      THEN REWRITE_TAC [COLLINEAR;FORALL_IN_INSERT;NOT_IN_EMPTY]
      THEN ASM_REWRITE_TAC [] THEN discover_tac
      (by_cols o Di.conjuncts) MESON_TAC;;

let theorem7 = theorem
  "!P Q. ~(P = Q) ==> INFINITE {R | between P R Q}"
  [fix ["P:point";"Q:point"]
  ;assume "~(P = Q)" at [0]
  ;set "X = {R | between P R Q}"
  ;otherwise assume "FINITE {R | between P R Q}" at [1] by [INFINITE]
  ;per cases
    [[suppose "0 < CARD X /\ 1 < CARD X" at [2]
     ;consider ["a:line"] st "on_line P a /\ on_line Q a"
       at [3] from [0] by [g11]
     ;hence "COLLINEAR X"
       from [0;1] using
       (K (ASM_REWRITE_TAC [COLLINEAR;IN_ELIM_THM] THEN EXISTS_TAC `a:line`))
       at [4] by [g12;g21]
     ;so consider ["f:num->point"] st "ORDERING f X"
       at [5] from [1] by [theorem6;FINITE_INSERT]
     ;have "~(f 0 = f 1) /\ f 0 IN X /\ f 1 IN X" at [6] from [2;4;5]
       by [NOT_SUC;ONE;FINITE_INSERT;ORDERING_INJ;ORDERING]
     ;so consider ["D:point"] st "between (f 0) D (f 1)" at [7] by [three]
     ;have "between P (f 0) Q /\ between P (f 1) Q" at [8]
       using (MAP_EVERY MP_TAC) from [6] by [IN_ELIM_THM]
     ;hence "between P D Q" from [6;7]
       using (ORDER_TAC `{P:point,Q,D,f 0,f 1}`)
     ;so consider ["n:num"] st "f n = D /\ n < CARD X" at [10] from [5]
       using (fun thms -> MP_TAC (SPECL [`X:point->bool`;`f:num->point`]
                                    ORDERING)
         THEN ASM_REWRITE_TAC [IN_ELIM_THM]) 
     ;hence "1 < n" from [5;7]
       by [ORDERING;INJ;BET_NEQS;ARITH_RULE `1 < n <=> ~(n = 0) /\ ~(n = 1)`] 
     ;hence "between (f 0) (f 1) D" from [2;5;10]
       by [ORDERING;SUC_INJ;LT_0;ONE]
     ;qed from [7;10] by [g23;BET_SYM]]
    ;[suppose "CARD X < 2" at [2]
     ;consider ["R:point"] at [3] st "between P R Q" from [0] by [three]
     ;so consider ["S:point"] at [4] st "between P S R" by [BET_NEQS;three]
     ;hence "{R,S} SUBSET X /\ ~(R = S)" at [5] from [0;3;4] 
       by [BET_NEQS;EMPTY_SUBSET;INSERT_SUBSET;IN_ELIM_THM;five2]
     ;hence "CARD {R,S} <= CARD X" at [6] from [1] by [CARD_SUBSET]
     ;have "CARD {R,S} = 2" from [5] using SIMP_TAC
       by [CARD_SUBSET;CARD_CLAUSES;FINITE_INSERT;FINITE_EMPTY
          ;IN_INSERT;NOT_IN_EMPTY;TWO;ONE]
     ;qed from [2;6] by [CARD_SUBSET;CARD_CLAUSES;LTE_ANTISYM]]]
    ;qed using (K ASM_ARITH_TAC)]

(* I thought I would need this for the PJCT. I might well need it for my
   point-in-polygon proof. *)
let ORDERING_ADJACENT = theorem
  "!f Ps P. ORDERING f Ps /\ between (f 0) P (f (CARD Ps - 1))
      ==> P IN Ps \/ ?n. n < CARD Ps - 1 /\ between (f n) P (f (SUC n))"
  [fix ["f:num->point";"Ps:point->bool";"P:point"]
  ;assume "ORDERING f Ps" at [0]
  ;assume "between (f 0) P (f (CARD Ps - 1))" at [1]
  ;assume "~(P IN Ps)" at [2]
  ;set "S = { M | between (f M) P (f (CARD Ps - 1))} INTER (0..CARD Ps - 1)"
  ;have "?x. x IN S" by [IN_ELIM_THM;IN_INTER;IN_NUMSEG;LE_0;ARITH_RULE `0<=x`]
    from [1]
  ;hence "~(S = {})" by [MEMBER_NOT_EMPTY]
  ;so consider ["m:num";"M:num"] at [3] st
    "m IN S /\ M IN S /\ !n. n IN S ==> m <= n /\ n <= M"
    using SIMP_TAC by [FINITE_INTER;FINITE_NUMSEG;SET_MIN_MAX]
  ;take ["M"]
  ;hence "between (f M) P (f (CARD Ps - 1))" at [4] using SET_TAC
  ;thus "M < CARD Ps - 1" proof
    [hence "~(M = CARD Ps - 1)" by [BET_NEQS]
    ;qed using MESON_TAC from [3]
       by [ARITH_RULE `(M < x - 1 <=> ~(M = x - 1) /\ M <= (x-1))`
          ;IN_INTER;IN_NUMSEG]]
  ;so assume "SUC M < CARD Ps - 1" at [5] from [4]
    by [ARITH_RULE `~(SUC M < x - 1) /\ M < x - 1 <=> SUC M = x - 1`]
  ;hence "between (f M) (f (SUC M)) (f (CARD Ps - 1))" at [6]
     from [0;1;4]
     by [ORDERING;LT;ARITH_RULE `SUC M < x - 1 ==> x - 1 < x`]
  ;hence "~between P (f M) (f (SUC M))" at [7]
     using ORDER_TAC `{P:point, f M, f (SUC M), f (CARD (Ps:point->bool) - 1)}`
     from [4]
  ;have "~(P = f M) /\ ~(P = f (SUC M)) /\ ~(f M = f (SUC M))" at [8]
     by [MEM;ORDERING;ORDERING_INJ
        ;ARITH_RULE `(SUC M < x - 1 ==> M < x /\ SUC M < x)
                     /\ ~(M = SUC M)`]
     from [0;2;5]
  ;obviously by_cols
     (so assume "between (f M) (f (SUC M)) P" from [1;4;6;7;8] by [four])
  ;hence "between (f (SUC M)) P (f (CARD Ps - 1))"
     using ORDER_TAC `{P:point, f M, f (SUC M), f (CARD (Ps:point->bool) - 1)}`
     from [4]
  ;hence "SUC M IN S" from [3;5] by [IN_ELIM_THM;IN_INTER;IN_NUMSEG;LE_LT;LE_0]
  ;qed from [3] by [ARITH_RULE `~(SUC M <= M)`]];;
