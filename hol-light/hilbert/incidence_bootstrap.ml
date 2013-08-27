(* These are all the rules for dealing with point sets. *)

let COLLINEAR =
  new_definition `COLLINEAR Ps <=> ?a. !P. P IN Ps ==> on_line P a`;; 

let COLLINEAR_LESS_THREE =
  let two = 
    prove (`!A B. COLLINEAR {A, B}`,
	   REWRITE_TAC [COLLINEAR; IN_INSERT; NOT_IN_EMPTY]
	     THEN REPEAT GEN_TAC
	     THEN ASM_CASES_TAC `(A : point = B)`
	     THENL [ASM_MESON_TAC [g11;g13a]; ASM_MESON_TAC [g11]]) in
    prove (`!P Q. COLLINEAR {} /\ COLLINEAR {P} /\ COLLINEAR {P,Q}`,
	   MESON_TAC [INSERT_INSERT; COLLINEAR; NOT_IN_EMPTY; two]);;

let set_rewrites = [EMPTY_SUBSET; INSERT_SUBSET; IN_INTER; IN_INSERT; NOT_IN_EMPTY;
		    IN_UNION; INSERT_INSERT; INSERT_COMM; INSERT_UNION_EQ; UNION_EMPTY;
		    IN_INTER; INTER_SUBSET; INTER_EMPTY ];;

let NON_COLL_NEQ =
  prove (`!A B C. ~COLLINEAR {A, B, C} ==> ~(A = B)`,
	REPEAT GEN_TAC THEN CONV_TAC CONTRAPOS_CONV
          THEN REWRITE_TAC [] THEN DISCH_TAC
          THEN ASM_REWRITE_TAC (COLLINEAR_LESS_THREE :: set_rewrites));;

let COLLINEAR_SUBSET =
  prove (`!As Bs. As SUBSET Bs ==> COLLINEAR Bs ==> COLLINEAR As`,
	   REWRITE_TAC [COLLINEAR] THEN ASM SET_TAC [COLLINEAR]);;

let COLLINEAR_UNION =
  prove (`!As Bs B A.
           COLLINEAR As ==> COLLINEAR Bs
           ==> A IN As ==> B IN As ==> A IN Bs ==> B IN Bs
           ==> ~(A = B)
	   ==> COLLINEAR (As UNION Bs)`,
    	 REWRITE_TAC [COLLINEAR; IN_UNION] THEN MESON_TAC [g11;g12]);;

let PLANAR_DEF =
  new_definition `PLANAR Ps <=> ?a'. !P. P IN Ps ==> on_plane P a'`;;

let PLANAR_SUBSET =
  prove (`!As Bs. As SUBSET Bs ==> PLANAR Bs ==> PLANAR As`,
	 REWRITE_TAC [PLANAR_DEF] THEN ASM SET_TAC [PLANAR_DEF]);;

let SECOND_POINT = 
  prove (`!A : point. ?B. ~(A = B)`,
	 MESON_TAC [g13a]);;

let EXISTS_TRIANGLE =
  prove (`!A B. ~(A = B) ==> ?C. ~COLLINEAR {A, B, C}`,
       REPEAT GEN_TAC
	 THEN REWRITE_TAC
           [EXISTS_NOT_THM; COLLINEAR; IN_INSERT; NOT_IN_EMPTY]
	 THEN (MAP_EVERY_TCL X_CHOOSE_THEN
		 [`D : point`; `E : point`; `Fa : point`]) ASSUME_TAC g13b
	 THEN REPEAT DISCH_TAC
	 THEN (MAP_EVERY (fun x -> FIRST_ASSUM (ASSUME_TAC o SPEC x))
		 [`D : point`; `E : point`; `Fa : point`])
	 THEN REPEAT (FIRST_X_ASSUM (X_CHOOSE_THEN `a : line` ASSUME_TAC))
	 THEN FIRST_X_ASSUM (ASSUME_TAC o SPEC `a : line`)
	 THEN ASM_MESON_TAC [g12]);;

(* Generalise this as a function from int -> thm *)
let three_eq =
  MESON [] `!P A B C. (!X. X = A \/ X = B \/ X = C ==> P X a)
            <=> P A a /\ P B a /\ P C a`;;

let COLL_SUBSETS' =
  prove (`!A B S. ~(A = B) /\ A IN S /\ B IN S /\
	   (!C. C IN S ==> COLLINEAR {A, B, C}) ==> COLLINEAR S`,
	 REWRITE_TAC ([COLLINEAR; three_eq] @ set_rewrites)
	   THEN MESON_TAC [g12]);;

let COLL_SUBSETS'' =
  prove (`!A S. A IN S /\ (!B C. B IN S /\ C IN S ==> COLLINEAR {A, B, C})
	 ==> COLLINEAR S`,
	 REPEAT GEN_TAC THEN
	 ASM_CASES_TAC `?B' : point. ~(A = B') /\ B' IN S`
	   THENL [ ASM_MESON_TAC [COLL_SUBSETS']
		 ; DISCH_TAC
                   THEN SUBGOAL_THEN `S = {A : point}` ASSUME_TAC
	           THENL [ASM SET_TAC []
                         ;ASM_REWRITE_TAC [COLLINEAR_LESS_THREE]]]);;

let COLL_SUBSETS''' =
  prove (`!S. (!A B C. {A, B, C} SUBSET S
               ==> COLLINEAR {A, B, C}) ==> COLLINEAR S`,
	 REWRITE_TAC (three_eq :: set_rewrites)
           THEN GEN_TAC THEN DISCH_TAC
           THEN ASM_CASES_TAC `S : point -> bool = {}`
	   THENL [ ASM_REWRITE_TAC [COLLINEAR_LESS_THREE]
		 ; SUBGOAL_THEN `?A. A : point IN S` MP_TAC
		   THENL [ ASM SET_TAC []
			 ; ASM_MESON_TAC [COLL_SUBSETS'']]]);;
  
let COLL_SUBSETS =
  prove (`!S. (!A B C. {A, B, C} SUBSET S
               ==> COLLINEAR {A, B, C}) ==> COLLINEAR S`,
	 GEN_TAC THEN ASM_CASES_TAC
	     `S : point -> bool = {}
              \/ (?A. S : point -> bool = {A})` THENL
	      [FIRST_X_ASSUM DISJ_CASES_TAC
	         THEN REPEAT (ASM_MESON_TAC [COLLINEAR_LESS_THREE]);
	       SUBGOAL_THEN
                 `?A : point B. ~(A = B) /\ A IN S /\ B IN S` ASSUME_TAC
               THENL [ASM SET_TAC []
                     ;FIRST_X_ASSUM (MAP_EVERY_TCL X_CHOOSE_THEN
			               [`A : point`; `B: point`]
			               (MAP_EVERY ASSUME_TAC o CONJUNCTS))
		      THEN FIRST_ASSUM
                           (X_CHOOSE_TAC `a : line` o MATCH_MP g11)
                      THEN REWRITE_TAC [COLLINEAR]
		      THEN DISCH_THEN
		  	   (ASSUME_TAC o SPECL [`A : point`; `B : point`])
                      THEN EXISTS_TAC `a : line`
                      THEN X_GEN_TAC `P : point`
                      THEN FIRST_X_ASSUM (ASSUME_TAC o SPEC `P : point`)
                      THEN ASM SET_TAC [g12]]]);;

let NON_COLL_TRIANGLE =
  MESON [COLL_SUBSETS]
    `!As. ~COLLINEAR As
      ==> ?A B C. {A, B, C} SUBSET As /\ ~COLLINEAR {A, B, C}`;;

let NON_COL_SUBSET =
  REWRITE_RULE [IMP_IMP]
    (CONV_RULE
       (ONCE_DEPTH_CONV (RAND_CONV CONTRAPOS_CONV))
       COLLINEAR_SUBSET);;

let PLANAR_UNION =
  let weak = 
    prove (`!As Bs. ~COLLINEAR (As INTER Bs) 
           ==> PLANAR As /\ PLANAR Bs ==> PLANAR (As UNION Bs)`,
	   REPEAT GEN_TAC
	     THEN DISCH_THEN (MP_TAC o MATCH_MP NON_COLL_TRIANGLE)
	     THEN (REWRITE_TAC (COLLINEAR :: set_rewrites))
	     THEN (DISCH_THEN
                     (MAP_EVERY_TCL X_CHOOSE_THEN
                        [`A:point`; `B:point`; `C :point`] MP_TAC))
	     THEN REWRITE_TAC [three_eq; NOT_EXISTS_THM]
	     THEN DISCH_THEN (MAP_EVERY ASSUME_TAC o CONJUNCTS)
             THEN FIRST_ASSUM (MP_TAC o MATCH_MP g15)
	     THEN REWRITE_TAC [PLANAR_DEF; IN_UNION]
	     THEN ASM_MESON_TAC [])
  in prove (`!As Bs Cs. PLANAR As ==> PLANAR Bs ==>
              ~COLLINEAR Cs ==> Cs SUBSET (As INTER Bs)
              ==> PLANAR (As UNION Bs)`,
            REPEAT GEN_TAC
              THEN DISCH_THEN
              (fun c ->
                 DISCH_THEN (fun c' -> REPEAT DISCH_TAC
                               THEN MP_TAC (CONJ c c')))
              THEN MATCH_MP_TAC weak
              THEN MATCH_MP_TAC NON_COL_SUBSET
              THEN EXISTS_TAC `Cs:point -> bool`
             THEN CONJ_TAC
             THEN REPEAT (FIRST_ASSUM ACCEPT_TAC));;
       
let g13b_col =
  prove (`?A B C. ~COLLINEAR {A, B, C}`,
	 REWRITE_TAC (COLLINEAR :: set_rewrites)
	   THEN MESON_TAC [g13b]);;

let g14a_col =
  prove (`!A B C. ~COLLINEAR {A, B, C} ==> PLANAR {A, B, C}`,
	 REWRITE_TAC ([COLLINEAR; PLANAR_DEF; three_eq] @ set_rewrites)
	   THEN MESON_TAC [g14a]);;

let two_planar =
  let strict = 
    prove (`!A B. ~(A = B) ==> PLANAR {A, B}`,
	   REPEAT GEN_TAC
	     THEN DISCH_THEN (CHOOSE_TAC o MATCH_MP EXISTS_TRIANGLE)
	     THEN MATCH_MP_TAC (REWRITE_RULE [SYM IMP_CONJ] PLANAR_SUBSET)
	     THEN EXISTS_TAC `{A : point, B, C}`
	     THEN REWRITE_TAC set_rewrites
	     THEN MATCH_MP_TAC g14a_col
	     THEN FIRST_ASSUM ACCEPT_TAC) in
    prove (`!A B. PLANAR {A, B}`,
	   REPEAT GEN_TAC
	     THEN (ASM_CASES_TAC `A : point = B`)
 	     THENL [ MATCH_MP_TAC
                       (REWRITE_RULE [SYM IMP_CONJ] PLANAR_SUBSET)
	             THEN X_CHOOSE_TAC `C : point`
                       (SPEC `A : point` SECOND_POINT)
		     THEN EXISTS_TAC `{A : point, C}`
		     THEN REWRITE_TAC set_rewrites
		     THEN ASM_MESON_TAC [strict]
		   ; ASM_MESON_TAC [strict] ]);;

let ASM_CASES_THEN tm ttac =
  DISJ_CASES_THEN ttac (SPEC tm EXCLUDED_MIDDLE);;

(* Notice that a claim of mere collinearity contains very little
   information. We effectively have a case-split when the set is empty,
   is a singleton, and contains more than one point. When it contains
   more than one point, we still have to find a point off the line to
   get a plane, giving us a nasty mess of cases to consider.*)
let COLLINEAR_PLANAR =
  let two = 
    prove (`!A B. ~(A = B) /\ A IN S /\ B IN S /\ COLLINEAR S
            ==> PLANAR S`,
	   REPEAT GEN_TAC THEN
	   DISCH_THEN (MAP_EVERY ASSUME_TAC o CONJUNCTS)
	     THEN FIRST_ASSUM (X_CHOOSE_TAC `C : point` o
				   MATCH_MP EXISTS_TRIANGLE)
	     THEN FIRST_X_ASSUM
  	       (X_CHOOSE_TAC `a' : plane` o
		  REWRITE_RULE ([PLANAR_DEF; three_eq] @ set_rewrites) o
		  MATCH_MP g14a_col)
	     THEN ASM_MESON_TAC [COLLINEAR; PLANAR_DEF; g16; g12]) in
    prove (`!S. COLLINEAR S ==> PLANAR S`,
	   GEN_TAC THEN
	     ASM_CASES_THEN
               `?A : point B. ~(A = B) /\ A IN S /\ B IN S` MP_TAC
	     THENL [ MESON_TAC [two]
		   ; ASM_CASES_THEN `S : point -> bool = {}` ASSUME_TAC
		     THENL [ ASM_REWRITE_TAC (PLANAR_DEF :: set_rewrites) 
		           ; DISCH_TAC THEN SUBGOAL_THEN
                               `?C : point. S = {C}`
                               (X_CHOOSE_TAC `C : point`)
			     THENL [ ASM SET_TAC []
			           ; SUBGOAL_THEN `?C' : point. ~(C = C')`
 			               (X_CHOOSE_TAC `C' : point`)
				     THENL [ ASM_MESON_TAC [g13a]
					   ; DISCH_TAC 
					     THEN MATCH_MP_TAC
                                               (REWRITE_RULE
                                                  [SYM IMP_CONJ]
                                                  PLANAR_SUBSET)
					     THEN EXISTS_TAC
                                               `{C : point, C'}`
					     THEN CONJ_TAC
					     THENL [ ASM SET_TAC []
						   ; MATCH_MP_TAC two
						     THEN EXISTS_TAC
                                                       `C : point`
						     THEN EXISTS_TAC
                                                       `C' : point`
						     THEN ASM_REWRITE_TAC
                                                       (COLLINEAR_LESS_THREE :: set_rewrites)]]]]]);;

let PLANAR_LESS_FOUR =
  let three =
    prove (`PLANAR {A, B, C}`, 
	   ASM_CASES_THEN `COLLINEAR {A, B, C}` MP_TAC 
           THENL [ MATCH_ACCEPT_TAC COLLINEAR_PLANAR
		 ; MATCH_ACCEPT_TAC g14a_col ]) in
    prove (`!P Q R. PLANAR {} /\ PLANAR {P}
             /\ PLANAR {P,Q} /\ PLANAR {P, Q, R}`,
	   MESON_TAC [INSERT_INSERT; PLANAR_DEF; NOT_IN_EMPTY; three]);;

let TRIANGLE'' =
  prove (`!A As. ~COLLINEAR As ==> A IN As ==> ?B C. {A, B, C} SUBSET As /\ ~COLLINEAR {A, B, C}`, 
	 REPEAT GEN_TAC THEN
	   REWRITE_TAC [SYM IMP_CONJ] THEN
	   CONV_TAC CONTRAPOS_CONV THEN
	   REWRITE_TAC [NOT_EXISTS_THM; DE_MORGAN_THM] THEN
	   REWRITE_TAC (TAUT `~P \/ Q <=> P ==> Q` :: set_rewrites) THEN
	   ASM_CASES_TAC `A : point IN As` THEN
	   ASM_REWRITE_TAC [] THEN
	   DISCH_TAC THEN
	   MATCH_MP_TAC COLL_SUBSETS''
	   THEN EXISTS_TAC `A : point`
	   THEN ASM_REWRITE_TAC set_rewrites);;

let COLL_INSERT_PLANAR =
  prove(`COLLINEAR S ==> PLANAR (P INSERT S)`,
	REWRITE_TAC [COLLINEAR] THEN
	  DISCH_THEN (X_CHOOSE_TAC `a : line`) THEN
	  ASM_CASES_TAC `COLLINEAR (P INSERT S)`
	  THENL [MATCH_MP_TAC COLLINEAR_PLANAR THEN FIRST_ASSUM ACCEPT_TAC
		;FIRST_ASSUM (MP_TAC o SPEC `P : point` o MATCH_MP TRIANGLE'') THEN
		  REWRITE_TAC set_rewrites THEN
		  DISCH_THEN
		    (MAP_EVERY_TCL X_CHOOSE_THEN [`B:point`; `C :point`] MP_TAC) THEN
		  PURE_REWRITE_TAC [IMP_CONJ] THEN
		  DISCH_THEN DISJ_CASES_TAC THENL
		    [ASM_REWRITE_TAC (COLLINEAR_LESS_THREE :: set_rewrites)
		    ;DISCH_THEN DISJ_CASES_TAC THENL
		      [ASM_REWRITE_TAC (COLLINEAR_LESS_THREE :: set_rewrites)
	              ;DISCH_TAC THEN
			FIRST_ASSUM (X_CHOOSE_TAC `a' : plane` o
				       REWRITE_RULE
				         ([PLANAR_DEF; three_eq] @ set_rewrites) o
				       MATCH_MP g14a_col) THEN
			FIRST_ASSUM (ASSUME_TAC o MATCH_MP NON_COLL_NEQ) THEN
			REWRITE_TAC [PLANAR_DEF] THEN
			EXISTS_TAC `a' : plane` THEN
			REWRITE_TAC set_rewrites THEN
			GEN_TAC THEN
			DISCH_THEN DISJ_CASES_TAC
			  THENL [ASM_REWRITE_TAC []
				;MATCH_MP_TAC (PURE_REWRITE_RULE [SYM IMP_CONJ] g16)
				  THEN MAP_EVERY EXISTS_TAC
				    [`B:point`;`C:point`;`a:line`]
				  THEN ASM_MESON_TAC []]]]]);;

let COLL_PLANAR_UNION =
  prove (`!As Bs B A.
           COLLINEAR As ==> PLANAR Bs ==> 
	   A IN As ==> B IN As ==> A IN Bs ==> B IN Bs 
           ==> ~(A = B) ==> PLANAR (As UNION Bs)`,
	 PURE_REWRITE_TAC [COLLINEAR; PLANAR_DEF] THEN
	   REWRITE_TAC set_rewrites THEN
	   ASM SET_TAC [g16]);;
	   
let INTER_COLLINEAR_PLANAR =
  let lemma = prove (`D : point IN As ==> E IN Bs ==> As UNION Bs = (E INSERT As) UNION (D INSERT Bs)`, ASM SET_TAC []) in
    prove (`!As Bs P.
             COLLINEAR As ==> COLLINEAR Bs
             ==> P IN As ==> P IN Bs
             ==> PLANAR (As UNION Bs)`,
	 REPEAT GEN_TAC THEN
	 ASM_CASES_TAC `COLLINEAR (As UNION Bs)` THENL
	   [REPEAT DISCH_TAC THEN MATCH_MP_TAC COLLINEAR_PLANAR THEN
	      FIRST_ASSUM ACCEPT_TAC
	   ;REPEAT STRIP_TAC THEN
	     FIRST_ASSUM (MP_TAC o SPEC `P : point` o MATCH_MP TRIANGLE'')
             THEN ASM_REWRITE_TAC set_rewrites THEN
	     DISCH_THEN
               (MAP_EVERY_TCL
		  X_CHOOSE_THEN [`B : point`; `C : point`] MP_TAC)
             THEN DISCH_TAC
             THEN SUBGOAL_THEN
               `?A B. A IN As /\ B IN Bs /\ ~COLLINEAR {A, B, P}`
	       MP_TAC
             THENL
	     [POP_ASSUM MP_TAC THEN
		STRIP_TAC THENL
		[MP_TAC (REWRITE_RULE set_rewrites
			   (SPECL [`{B : point, C, P}`; `As : point -> bool`]
			      COLLINEAR_SUBSET)) THEN
		   ASM_REWRITE_TAC set_rewrites
	        ;ASM_MESON_TAC []
		;ASM_MESON_TAC [INSERT_COMM]
		;MP_TAC (REWRITE_RULE set_rewrites
			   (SPECL [`{B : point, C, P}`; `Bs : point -> bool`]
			      COLLINEAR_SUBSET)) THEN
		  ASM_REWRITE_TAC set_rewrites]
	     ;DISCH_THEN (MAP_EVERY_TCL X_CHOOSE_THEN [`D:point`; `E:point`] MP_TAC)
	       THEN REWRITE_TAC [IMP_CONJ] THEN
	       DISCH_TAC THEN DISCH_TAC THEN
	       MP_TAC lemma THEN
	       ASM_REWRITE_TAC [] THEN
	       DISCH_TAC THEN
	       ASM_REWRITE_TAC [] THEN
	       DISCH_TAC THEN
	       MATCH_MP_TAC
               (PURE_REWRITE_RULE [SYM IMP_CONJ]
                  PLANAR_UNION) THEN
               EXISTS_TAC `E : point INSERT As INTER D INSERT Bs` THEN
	       REPEAT CONJ_TAC THENL
	       [MATCH_MP_TAC COLL_INSERT_PLANAR THEN
		  FIRST_ASSUM ACCEPT_TAC
               ;MATCH_MP_TAC COLL_INSERT_PLANAR THEN
		  FIRST_ASSUM ACCEPT_TAC
               ;FIRST_ASSUM
                  (MP_TAC o MATCH_MP
		     (CONV_RULE (BINDER_CONV (BINDER_CONV CONTRAPOS_CONV))
			(PURE_REWRITE_RULE [SYM IMP_CONJ] COLLINEAR_SUBSET))) THEN
		  SUBGOAL_THEN `(E : point) INSERT As UNION D INSERT Bs =
		   As UNION Bs` ASSUME_TAC THENL
		     [ASM SET_TAC []
		     ;CONV_TAC CONTRAPOS_CONV THEN
		       REWRITE_TAC [NOT_FORALL_THM] THEN
		       DISCH_TAC THEN
		       EXISTS_TAC `(E : point) INSERT As INTER D INSERT Bs` THEN
		       ASM_REWRITE_TAC set_rewrites]
               ;SET_TAC []]]]);;

let NON_COLL_INFER =
  prove (`!As B A X Y Z. COLLINEAR As ==> ~COLLINEAR {X,Y,Z}
         ==> A IN As ==> B IN As
         ==> X IN As ==> Y IN As
         ==> ~(A=B)
         ==> ~COLLINEAR {A,B,Z}`,
	 PURE_REWRITE_TAC [RIGHT_IMP_FORALL_THM]
	   THEN REPEAT GEN_TAC
	   THEN PURE_REWRITE_TAC [TRANS IMP_IMP IMP_CONJ_ALT]
	   THEN CONV_TAC
	     ((RAND_CONV o RAND_CONV o RAND_CONV o RAND_CONV o RAND_CONV
               o RAND_CONV) CONTRAPOS_CONV)
           THEN REWRITE_TAC
             [INSERT_SUBSET;IN_INSERT; NOT_IN_EMPTY; EMPTY_SUBSET]
	   THEN REPEAT DISCH_TAC
	   THEN MATCH_MP_TAC
             (PURE_REWRITE_RULE [SYM IMP_CONJ] COLLINEAR_SUBSET)
	   THEN EXISTS_TAC `{A:point,B,Z} UNION As`
	   THEN CONJ_TAC
	   THENL [ASM SET_TAC []
                 ;MATCH_MP_TAC
                   (PURE_REWRITE_RULE [SYM IMP_CONJ] COLLINEAR_UNION)
		   THEN MAP_EVERY EXISTS_TAC [`A:point`;`B:point`]
		   THEN ASM SET_TAC []])
    
let NON_COLL_INFER1, NON_COLL_INFER2, NON_COLL_INFER3 =
  let c1 = SET_RULE `{X,Y,Z} = {X,Z,Y}`
  and c2 = SET_RULE `{X,Y,Z} = {Z,X,Y}`
  in NON_COLL_INFER,
  CONV_RULE (ONCE_DEPTH_CONV (REWR_CONV c1)) NON_COLL_INFER,
  CONV_RULE (ONCE_DEPTH_CONV (REWR_CONV c2)) NON_COLL_INFER
    
let COLLINEAR_INTERSECT =
  prove (`!As Bs Cs B A.
           COLLINEAR As ==> COLLINEAR Bs
           ==> ~COLLINEAR Cs
           ==> Cs SUBSET As UNION Bs
           ==> A IN As ==> B IN As ==> A IN Bs ==> B IN Bs
           ==> A = B`,
         REPEAT GEN_TAC
           THEN REPEAT DISCH_TAC
           THEN SUBGOAL_THEN `~COLLINEAR (As UNION Bs)` MP_TAC
           THENL [MATCH_MP_TAC NON_COL_SUBSET
                    THEN EXISTS_TAC `Cs : point -> bool`
                    THEN CONJ_TAC THEN REPEAT (FIRST_ASSUM ACCEPT_TAC)
                 ;ASM MESON_TAC [COLLINEAR_UNION]]);;

(* What is the relation between Theorem 3 and g22. Are they dual? Can we use the
   Pasch search algorithm to find out? *)

let BETWEEN_COL = prove (`!A B C. between A B C ==> COLLINEAR {A,B,C}`,
                         REPEAT GEN_TAC
                           THEN DISCH_THEN (ASSUME_TAC o MATCH_MP g21)
                           THEN REWRITE_TAC
                           [FORALL_IN_INSERT;NOT_IN_EMPTY;COLLINEAR]
                           THEN ASM_REWRITE_TAC []);;
                         

let SWAP_BETWEEN = prove (`!A B C. between A B C <=> between C B A`,
			  MESON_TAC [g21]);;

let five_eq =
  MESON [] `!P A B C D E. (!X. X = A \/ X = B \/ X = C \/ X = D \/ X = E
      ==> P X a) <=> P A a /\ P B a /\ P C a /\ P D a /\ P E a`;;

let NON_COLL_NEQ =
  prove (`!A B C. ~COLLINEAR {A, B, C} ==>
	   ~(A = B) /\ ~(A = C) /\ ~(B = C)`,
	 REPEAT GEN_TAC THEN
	   CONV_TAC CONTRAPOS_CONV THEN
	   REWRITE_TAC [DE_MORGAN_THM] THEN STRIP_TAC THEN
	   ASM_REWRITE_TAC (COLLINEAR_LESS_THREE ::
			      set_rewrites));;

let COL_NCOL_BOT =
  prove (`COLLINEAR A ==> ~COLLINEAR B ==> ~(B SUBSET A)`,
         MESON_TAC [COLLINEAR_SUBSET]);;

let COL_NCOL_NEQ =
  let lemma =
    prove (`A IN As /\ B IN As
           ==> (?S. S IN As /\ C = S)
           ==> {A,B,C} SUBSET As`,
           SET_TAC []) in
    prove (`COLLINEAR As ==> ~COLLINEAR {A,B,C}
           ==> A IN As /\ B IN As
           ==> !S. S IN As ==> ~(C = S)`,
           MESON_TAC [lemma;COLLINEAR_SUBSET]);;

let pasch_col =
  let weak =
    prove (`!A B C D E. ~COLLINEAR {A, B, C} 
           ==> ~COLLINEAR {A, D, E} 
	   ==> ~COLLINEAR {B, D, E} 
	   ==> ~COLLINEAR {C, D, E} 
           ==> PLANAR {A, B, C, D, E} 
	   ==> between A D B ==>
    	   ?Fa. COLLINEAR {D, E, Fa}
             /\ (between A Fa C \/ between B Fa C)`,
	   REPEAT GEN_TAC 
	     THEN REWRITE_TAC [IMP_CONJ]
	     THEN DISCH_TAC
	     THEN FIRST_ASSUM (ASSUME_TAC o MATCH_MP NON_COLL_NEQ)
	     THEN REPLICATE_TAC 3 DISCH_TAC
	     THEN ASM_REWRITE_TAC
               (COLLINEAR :: three_eq :: set_rewrites)
	     THEN FIRST_ASSUM
               (ASSUME_TAC
                  o CONJUNCT2 o CONJUNCT2
                  o MATCH_MP NON_COLL_NEQ)
	     THEN FIRST_ASSUM (X_CHOOSE_TAC `a : line` o MATCH_MP g11)
	     THEN DISCH_TAC
	     THEN RULE_ASSUM_TAC
	       (REWRITE_RULE ([COLLINEAR; PLANAR_DEF; three_eq
                              ; NOT_EXISTS_THM] @ set_rewrites))
	     THEN REPLICATE_TAC 3
               (FIRST_X_ASSUM (MP_TAC o SPEC `a : line`))
	     THEN ASM_REWRITE_TAC []
	     THEN REPEAT DISCH_TAC
	     THEN FIRST_X_ASSUM (X_CHOOSE_TAC `a' : plane`)
	     THEN RULE_ASSUM_TAC (REWRITE_RULE [five_eq])
	     THEN MP_TAC (SPECL [`D : point`; `E : point`;
                                 `a : line`; `a' : plane`] g16)
	     THEN ASM_REWRITE_TAC []
	     THEN DISCH_TAC
	     THEN MP_TAC
  	       (SPECL [`A : point`; `B : point`; `C: point`;
                       `a : line`; `a' : plane`] g24)
	     THEN ASM_MESON_TAC [])
  in prove (`!A B C D E As.
              between A D B 
            ==> ~COLLINEAR {A, B, C} 
            ==> ~COLLINEAR {A, D, E} 
	    ==> ~COLLINEAR {B, D, E} 
	    ==> ~COLLINEAR {C, D, E}
            ==> PLANAR As
            ==> {A, B, C, D, E} SUBSET As
            ==> ?Fa. COLLINEAR {D, E, Fa}
                      /\ (between A Fa C \/ between B Fa C)`,
            MESON_TAC [weak;PLANAR_SUBSET])
