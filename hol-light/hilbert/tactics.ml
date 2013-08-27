let (MAP_EVERY_TCL : ('a -> thm_tactical) -> 'a list -> thm_tactical) =
  fun f xs -> EVERY_TCL (map f xs);;

let rec CONJUNCTS_TAC tm =
  (TRY (CONJ_TAC THENL [ALL_TAC;CONJUNCTS_TAC])) tm;;

(* Copy the antecedent of the goal into the assumptions. *)
let ASSUME_ANT = DISCH_THEN (fun thm -> ASSUME_TAC thm THEN MP_TAC thm)

let ASSUME_ANT_THEN ttac =
  DISCH_THEN (fun thm -> MP_TAC thm THEN ttac thm);;

(* As Mizar_light's assume. *)
let EXTRACT tm =
  ASM_CASES_TAC tm THEN ASM_REWRITE_TAC [];;

let EXTRACT_THEN tm ttac =
  ASM_CASES_TAC tm THEN ASM_REWRITE_TAC []
    THEN POP_ASSUM ttac

let FULL_SIMP_TAC thl =
  SIMP_ASM_TAC thl THEN ASM_SIMP_TAC thl;;

let PROVE_ANT_THEN ttac thm =
  let ant,c = dest_imp (concl thm) in
  SUBGOAL_THEN ant (ttac o MATCH_MP thm);;

let FIRST_MATCH ttac thm = FIRST_ASSUM (ttac o MATCH_MP thm);;

let FIRST_X_MATCH ttac imp = FIRST_X_ASSUM (ttac o MATCH_MP imp);;
