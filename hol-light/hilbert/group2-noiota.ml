(* THEOREM THREE *)
h "!A C. ~(A = C) ==> ?D. between A D C";;
f (fix ["A:point";"C:point"]);;
f (assume "~(A = C)");;
f (so consider ["E:point"] st "~(?a. on_line A a /\ on_line C a /\ on_line E a)"
     by [triangle]);;
f (obviously Ic.neqs (consider ["Fa:point"] at 0 st "between A E Fa" by [g22]));;
f (obviously Ic.neqs (consider ["G:point"] at 1 st "between Fa C G" by [g22]));;
f (consider ["D:point"] st
     ("(?a. on_line E a /\ on_line D a /\ on_line G a)" ^
         "/\ (between A D C \/ between C D Fa)") 
     by [pasch_on (`A:point`,`Fa:point`,`C:point`,`E:point`,`G:point`)]
     at 2 from [0]);;
f (obviously one_eq (qed from [1] by [g21;g23]));;

let three = top_thm ();;

(* THEOREM FOUR *)
h ("!A B C. (?a. on_line A a /\ on_line B a /\ on_line C a) " ^
     "==> ~(A = B) /\ ~(A = C) /\ ~(B = C) " ^
     "==> ~between A C B /\ ~between B A C ==> between A B C");;
f (fix ["A:point";"B:point";"C:point"]);;
f (assume ("(?a. on_line A a /\ on_line B a /\ on_line C a)" ^
           "/\ ~(A = B) /\ ~(A = C) /\ ~(B = C)" ^
           "/\ ~between A C B /\ ~between B A C") at 0);;
f (so consider ["D:point"] st "~(?a. on_line A a /\ on_line B a /\ on_line D a)"
     by [triangle]);;
f (obviously Ic.neqs (consider ["G:point"] st "between B D G" by [g22] at 1));;
f (consider ["E:point"] st
     ("(?a. on_line A a /\ on_line D a /\ on_line E a)" ^
        "/\ between C E G") at 2);;
  f (consider ["E:point"] st
       ("(?a. on_line A a /\ on_line D a /\ on_line E a)" ^
          "/\ (between B E C \/ between C E G)") 
       by [pasch_on (`B:point`,`G:point`,`C:point`,`D:point`,`A:point`)]
       from [1]);;
  f (obviously one_eq (qed from [0] by [g21;g23]));;
f (consider ["Fa:point"] st
     ("(?a. on_line C a /\ on_line D a /\ on_line Fa a) " ^
        "/\ between A Fa G") at 3);;
  f (consider ["Fa:point"] st
       ("(?a. on_line C a /\ on_line D a /\ on_line Fa a)" ^
          "/\ (between A Fa B \/ between A Fa G)") 
       by [pasch_on (`B:point`,`G:point`,`A:point`,`D:point`,`C:point`)]
       from [1]);;
  f (obviously one_eq (qed from [0] by [g21;g23]));;
f (have "between A D E");;
  f (consider ["D':point"] st
       ("(?a. on_line C a /\ on_line D' a /\ on_line Fa a)" ^
          "/\ (between A D' E \/ between E D' G)")
       by [pasch_on (`A:point`,`G:point`,`E:point`,`Fa:point`,`C:point`)]
       at 4 from [3]);;
  f (obviously two_eqs (qed from [2] by [g21;g23]));;
f (so consider ["B':point"] st
     ("(?a. on_line B a /\ on_line B' a /\ on_line D a)" ^
        "/\ (between A B' C \/ between C B' E)")
     by [pasch_on (`A:point`,`E:point`,`C:point`,`D:point`,`B:point`)]);;
f (obviously two_eqs (qed from [2] by [g21;g23]));;
     
let four = top_thm ();;

(* We don't need to assume that ABCD are collinear, since this is implied by the betweeness hypotheses. *)
(* THEOREM FIVE --- PART 1 *)
h "!A B C D. between A B C /\ between B C D ==> between A C D";;
f (fix ["A:point";"B:point";"C:point";"D:point"]);;
f (assume "between A B C /\ between B C D" at 0);;
f (consider ["E:point"] st
     "~(?a. on_line A a /\ on_line B a /\ on_line E a)"
     from [0] by [g21;triangle]);;
f (obviously Ic.neqs
     (consider ["Fa:point"] st "between C E Fa" at 1 by [g22]));;
(* This step is needed so we can eliminate the case-split when we find H. *)
f (consider ["G:point"] st
     ("(?a. on_line B a /\ on_line Fa a /\ on_line G a) /\ between A G E")
  at 2);;
  f (consider ["G:point"] st
       ("(?a. on_line B a /\ on_line Fa a /\ on_line G a)" ^
          "/\ (between A G E \/ between C G E)")
       by [pasch_on (`A:point`,`C:point`,`E:point`,`B:point`,`Fa:point`)]
       from [0]);;
  f (obviously one_eq (qed by [g21;g23] from [1]));;
f (have "between B G Fa" at 3);;
  f (consider ["G':point"] st
       ("(?a. on_line A a /\ on_line G' a /\ on_line E a)" ^
          "/\ (between B G' C \/ between B G' Fa)")
       by [pasch_on (`C:point`,`Fa:point`,`B:point`,`E:point`,`A:point`)]
       from [1]);;
  f (obviously two_eqs (qed by [g21;g23] from [0]));;
f (consider ["H:point"] st
     ("(?a. on_line C a /\ on_line Fa a /\ on_line H a) /\ between D H G")
     at 4);;
  f (consider ["H:point"] st
       ("(?a. on_line C a /\ on_line Fa a /\ on_line H a)" ^
          "/\ (between B H G \/ between D H G)")
       by [pasch_on (`B:point`,`D:point`,`G:point`,`C:point`,`Fa:point`)]
       from [0]);;
  f (obviously one_eq (qed by [g21;g23] from [3]));;
f (have "~(A = D)" from [0] by [g21;g23]);;
f (consider ["C':point"] st
     ("(?a. on_line C' a /\ on_line E a /\ on_line H a)" ^
        "/\ (between A C' D \/ between A C' G)")
     by [pasch_on (`D:point`,`G:point`,`A:point`,`H:point`,`E:point`)]
     from [4]);;
f (obviously two_eqs (qed from [2] by [g21;g23]));;

let five1 =
  MESON [top_thm ();g21]
    `!A B C D. between A B C /\ between B C D
       ==> between A B D /\ between A C D`;;

h "!A B C D. between A B C /\ between A C D ==> between B C D";;
f (fix ["A:point";"B:point";"C:point";"D:point"]);;
f (assume "between A B C /\ between A C D" at 0);;
f (consider ["G:point"] st
     "~(?a. on_line A a /\ on_line B a /\ on_line G a)"
     from [0] by [g21;triangle]);;
f (obviously Ic.neqs
     (consider ["Fa:point"] st "between B G Fa" at 1 by [g22]));;
f (have ("~(?P. (?a. on_line C a /\ on_line Fa a /\ on_line P a)" ^
            "/\ between A P G)") at 2);;
  f (otherwise consider ["P:point"] st
       ("(?a. on_line C a /\ on_line Fa a /\ on_line P a) /\ between A P G"));;
  f (so consider ["Q:point"] st
       ("(?a. on_line C a /\ on_line P a /\ on_line Q a)" ^
          "/\ (between A Q B \/ between B Q G)")
       by [pasch_on (`A:point`,`G:point`,`B:point`,`P:point`,`C:point`)]);;
  f (obviously two_eqs (qed from [0;1] by [g21;g23]));;
f (consider ["H:point"] st
     "(?a. on_line C a /\ on_line Fa a /\ on_line H a) /\ between D H G"
   by [pasch_on (`A:point`,`D:point`,`G:point`,`C:point`,`Fa:point`)]
     from [0;2] at 3);;
f (have "~(B = D)" from [0] by [g21;g23]);;
f (consider ["C':point"] st
     ("(?a. on_line C' a /\ on_line Fa a /\ on_line H a)" ^
        "/\ (between B C' D \/ between B C' G)")
     by [pasch_on (`D:point`,`G:point`,`B:point`,`H:point`,`Fa:point`)]
     from [3]);;
f (obviously two_eqs (qed from [1] by [g21;g23]));;

let five2 =
  MESON [five1;top_thm ()]
    `!A B C D. between A B C /\ between A C D
       ==> between A B D /\ between B C D`;;

(* We carve out a type that we can prove infinite. *)
g `?(A,X,B). ~(A = B) /\ !P. P IN X ==> between A P B`;;
e (REWRITE_TAC [EXISTS_TRIPLED_THM]);;
e (REPEAT_TCL CHOOSE_THEN ASSUME_TAC (SPEC_ALL g13a));;
e (MAP_EVERY EXISTS_TAC [`A:point`;`{}:point -> bool`;`B:point`]);;
e (ASSUM_LIST SET_TAC);;

let IND = new_type_definition "ind" ("mk_ind","dest_ind") (top_thm ());;

(* We define the successor function explicitly. *)
let suc_def = new_definition
    `ind_suc n = let (A,X,B) = dest_ind n in
                 mk_ind (A, {B} UNION X, @C.
                   !P. P IN {B} UNION X ==> between A P C)`;;

let LAMBDA_TRIPLE_THM = prove
   (`!t. (\p. t p) = (\(x,y,z). t(x,y,z))`,
  REWRITE_TAC[FORALL_PAIR_THM; FUN_EQ_THM]);;

let dest_ind = prove (`!A X B x. dest_ind x = A,X,B ==> ~(A = B) /\
  (!P. P IN X ==> between A P B)`,
   REPEAT GEN_TAC
     THEN DISCH_TAC THEN FIRST_ASSUM (MP_TAC o AP_TERM `mk_ind`)
     THEN DISCH_THEN (MP_TAC o AP_TERM `dest_ind`)
     THEN REWRITE_TAC [IND]
     THEN ASM_REWRITE_TAC []
     THEN MESON_TAC
     [REWRITE_RULE [FORALL_TRIPLED_THM; LAMBDA_TRIPLE_THM] IND]);;

let suc_exists =
  prove (`!A X B. (!P. P IN X ==> between A P B)
         ==> ?C. (!P. P IN {B} UNION X ==> between A P C)`,
       REPEAT GEN_TAC
         THEN REWRITE_TAC [IN_UNION;IN_INSERT;NOT_IN_EMPTY]
         THEN DISCH_TAC
         THEN X_CHOOSE_TAC `C:point` (SPECL [`A:point`;`B:point`] g22)
         THEN EXISTS_TAC `C:point`
         THEN GEN_TAC THEN DISCH_THEN DISJ_CASES_TAC
         THEN ASM_MESON_TAC [five2]);;

let ind_closed =
  prove (`dest_ind (ind_suc x) = let A,X,B = dest_ind x in
                               A,{B} UNION X,@C. 
                                 !P. P IN {B} UNION X ==> between A P
                                 C`,
  REWRITE_TAC [suc_def]
  THEN REPEAT LET_TAC
  THEN POP_ASSUM (ASSUME_TAC o MATCH_MP dest_ind)
  THEN REWRITE_TAC [GSYM IND]
  THEN POP_ASSUM (ASSUME_TAC o
                    MATCH_MP (REWRITE_RULE
                                [IN_UNION;IN_INSERT;NOT_IN_EMPTY]
                                suc_exists) o CONJUNCT2)
  THEN REWRITE_TAC [IN_INSERT;NOT_IN_EMPTY;IN_UNION]
  THEN CONJ_TAC THEN ASM_MESON_TAC
  [prove (`!A B C. between A B C ==> ~(A=C)`,MESON_TAC [g21])]);;

let ind_one_one =
  prove (`!n n. ind_suc n = ind_suc n' ==> n = n'`,
      REPEAT GEN_TAC
      THEN DISCH_TAC
      THEN SUBGOAL_THEN `dest_ind n = dest_ind n'` ASSUME_TAC
      THENL [POP_ASSUM MP_TAC
                THEN DISCH_THEN (MP_TAC o AP_TERM `dest_ind`)
                THEN REWRITE_TAC [ind_closed]
                THEN REPEAT (LET_TAC THEN POP_ASSUM (ASSUME_TAC o MATCH_MP dest_ind))
                THEN REWRITE_TAC [PAIR_EQ;IMP_CONJ]
                THEN POP_ASSUM_LIST (fun thms -> DISCH_TAC THEN MAP_EVERY MP_TAC thms)
                THEN ASM_REWRITE_TAC []
                THEN REWRITE_TAC [IN_UNION;IN_INSERT;NOT_IN_EMPTY]
                THEN REWRITE_TAC [IMP_CONJ]
                THEN REPLICATE_TAC 5 DISCH_TAC
                THEN SUBGOAL_THEN `~(B':point IN X) /\ ~(B:point IN X')` ASSUME_TAC
                THENL [CONJ_TAC
                          THEN DISCH_THEN (fun thm -> FIRST_ASSUM (fun thm' -> ASSUME_TAC
                            (MATCH_MP thm' thm) THEN ASSUME_TAC thm))
                          THEN (SUBGOAL_THEN `~(B:point=B')` ASSUME_TAC
                                  THENL [ASM_MESON_TAC [g21]
                                        ;ASSUME_TAC g23 THEN ASSUM_LIST SET_TAC])
                      ; ASSUM_LIST SET_TAC]
            ;ASM_MESON_TAC [IND]]);;

let zero_exists =
  prove (`!A B. ~(A:point = B) ==> dest_ind (mk_ind (A,{},B)) = (A,{},B)`,
         REPEAT GEN_TAC
           THEN DISCH_TAC THEN REWRITE_TAC [GSYM (CONJUNCT2 IND)]
           THEN ASSUM_LIST SET_TAC);;

let ind_not_onto =
  prove (`?n'. !n. ~(ind_suc n = n')`,
         REPEAT_TCL CHOOSE_THEN (MAP_EVERY ASSUME_TAC o CONJUNCTS) (SPEC_ALL g13a)
           THEN EXISTS_TAC `mk_ind (A,{},B)`
           THEN GEN_TAC
           THEN DISCH_THEN (MP_TAC o AP_TERM `dest_ind`)
           THEN REWRITE_TAC [ind_closed]
           THEN FIRST_ASSUM (ASSUME_TAC o MATCH_MP zero_exists)
           THEN ASM_REWRITE_TAC []
           THEN LET_TAC
           THEN REWRITE_TAC [PAIR_EQ]
           THEN SET_TAC []);;

let ONE_ONE = new_definition
  `ONE_ONE(f:A->B) = !x1 x2. (f x1 = f x2) ==> (x1 = x2)`;;

let ONTO = new_definition
  `ONTO(f:A->B) = !y. ?x. y = f x`;;

let INFINITY_AX =
  prove (`?f:ind->ind. ONE_ONE f /\ ~(ONTO f)`,
    EXISTS_TAC `ind_suc`
      THEN REWRITE_TAC [ONE_ONE;ONTO]
      THEN MESON_TAC [ind_one_one;ind_not_onto]);;
