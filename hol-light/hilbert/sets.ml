(* Needed for ORDER_ADJACENT, which I don't think is needed! *)

let SET_MIN_MAX = prove
  (`!s:num->bool. FINITE s ==> ~(s = {})
       ==> ?m M. m IN s /\ M IN s /\ !x. x IN s ==> m <= x /\ x <= M`,
    MATCH_MP_TAC FINITE_INDUCT THEN CONJ_TAC THEN REWRITE_TAC []
      THEN REPEAT GEN_TAC THEN ASM_CASES_TAC `s:num->bool = {}`
      THENL [ONCE_REWRITE_TAC [SWAP_EXISTS_THM]
                THEN ASM_REWRITE_TAC [EXISTS_IN_INSERT;FORALL_IN_INSERT
                                     ;LE_REFL;NOT_IN_EMPTY;NOT_EMPTY_INSERT]
            ;ASM_REWRITE_TAC [NOT_INSERT_EMPTY;IN_INSERT] THEN STRIP_TAC
              THEN DISJ_CASES_TAC (SPECL [`m:num`;`x:num`] LE_CASES)
              THEN DISJ_CASES_TAC (SPECL [`M:num`;`x:num`] LE_CASES)
              THEN ASM_MESON_TAC [LE_TRANS;LE_REFL]]);;

let DISJOINT_IMP = prove
  (`!s:a->bool t. DISJOINT s t <=> !x. x IN s ==> ~(x IN t)`,
   REWRITE_TAC [DISJOINT] THEN SET_TAC []);;
