(* Generalisation of WLOG_LT. Could go for more. *)
let WLOG_LT3 =
  prove (`(!m:num n:num. P m m n) /\ (!m:num n:num p:num. P m n p <=> P n m p)
          /\ (!m:num n:num p:num. P m n p <=> P n p m) /\ (!m n p. m < n /\ n < p ==> P m n p)
          ==> (!m:num n:num p:num. P m n p)`,
         DISCH_TAC THEN REPEAT GEN_TAC
           THEN REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC (SPEC_ALL LT_CASES)
           THEN ASSUME_TAC (SPECL [`n:num`;`p:num`] LT_CASES)
           THEN ASSUME_TAC (SPECL [`m:num`;`p:num`] LT_CASES)
           THEN ASM_MESON_TAC []);;

let ARITH_TAC_THMS thms = MAP_EVERY MP_TAC thms THEN ARITH_TAC;;
