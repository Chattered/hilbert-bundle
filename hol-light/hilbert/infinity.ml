(* ========================================================================= *)
(* Theorem of infinity using iota.                                           *)
(*                                                                           *)
(*                                   Phil Scott                              *)
(*                                                                           *)
(*               Centre for Intelligent Systems and their Applications       *)
(*                             University of Edinburgh                       *)
(* ========================================================================= *)

(* Repeating the proof in pair.ml *)
let EXISTS_6TUPLED_THM = prove
 (`!P. (?(x,y,z,u,v,w). P x y z u v w) <=> (?x y z u v w. P x y z u v w)`,
  GEN_TAC THEN MATCH_MP_TAC(TAUT `(~p <=> ~q) ==> (p <=> q)`) THEN
  REWRITE_TAC[REWRITE_RULE[ETA_AX] NOT_EXISTS_THM; FORALL_PAIR_THM]);;

let EXISTS_6TUPLE_THM = prove
 (`!P. (?p. P p) <=> (?x y z u v w. P (x, y, z, u, v, w))`,
  GEN_TAC THEN MATCH_MP_TAC(TAUT `(~p <=> ~q) ==> (p <=> q)`) THEN
  REWRITE_TAC[REWRITE_RULE[ETA_AX] NOT_EXISTS_THM; FORALL_PAIR_THM]);;

let FORALL_6TUPLED_THM = prove
  (`!P. (!(x,y,z,a,b,c). P x y z a b c) <=> (!x y z a b c. P x y z a b c)`,
  GEN_TAC THEN GEN_REWRITE_TAC (LAND_CONV o RATOR_CONV) [FORALL_DEF] THEN
  REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM]);;

let LAMBDA_6TUPLE_THM = prove
   (`!t. (\p. t p) = (\(x,y,z,a,b,c). t(x,y,z,a,b,c))`,
  REWRITE_TAC[FORALL_PAIR_THM; FUN_EQ_THM]);;

(* We carve out a type of diagrams that we can prove infinite. *)
let IND = new_type_definition "ind" ("mk_ind","dest_ind")
  (theorem ("?(A, B, C, D, Z, N). " ^
               "~(?a. on_line A a /\ on_line B a /\ on_line Z a)" ^
               "/\ between A B C /\ between C Z D" ^
               "/\ (between A N Z \/ N = Z)") 
     [consider ["A:point";"B:point";"Z:point"] st
         "~(?a. on_line A a /\ on_line B a /\ on_line Z a)" by [g13b] at [0]
     ;obviously by_neqs
       (so consider ["C:point"] st "between A B C" by [g22] at [1])
     ;obviously by_neqs
       (so consider ["D:point"] st "between C Z D" from [0] by [g22])
     ;qed by [EXISTS_6TUPLED_THM] from [0;1]]);;

let exists_ind = prove
  (`!x. ?A B C D Z N. dest_ind x = A,B,C,D,Z,N
    /\ ~(?a. on_line A a /\ on_line B a /\ on_line Z a)
    /\ between A B C /\ between C Z D /\ (between A N Z \/ N = Z)`,
   GEN_TAC THEN SUBGOAL_THEN `?A B C D Z N. dest_ind x = A,B,C,D,Z,N`
     (REPEAT_TCL CHOOSE_THEN ASSUME_TAC)
   THENL [REWRITE_TAC [GSYM EXISTS_6TUPLE_THM] THEN MESON_TAC []; ALL_TAC]
   THEN MAP_EVERY EXISTS_TAC [`A:point`;`B:point`;`C:point`
                             ;`D:point`;`Z:point`;`N:point`]
   THEN ASM_REWRITE_TAC []
   THEN SUBGOAL_THEN `dest_ind (mk_ind (A,B,C,D,Z,N)) = A,B,C,D,Z,N` ASSUME_TAC
   THENL [ASM_MESON_TAC [IND]
         ;POP_ASSUM MP_TAC THEN  REWRITE_TAC [GSYM (CONJUNCT2 IND)]]);;

let dest_ind = prove
  (`!A B C D Z N x. dest_ind x = A,B,C,D,Z,N
    ==> ~(?a. on_line A a /\ on_line B a /\ on_line Z a)
    /\ between A B C /\ between C Z D
    /\ (between A N Z \/ N = Z)`,
   REPEAT GEN_TAC
     THEN DISCH_TAC THEN FIRST_ASSUM (MP_TAC o AP_TERM `mk_ind`)
     THEN DISCH_THEN (MP_TAC o AP_TERM `dest_ind`)
     THEN REWRITE_TAC [IND]
     THEN ASM_REWRITE_TAC []
     THEN MESON_TAC
     [REWRITE_RULE [FORALL_6TUPLED_THM; LAMBDA_6TUPLE_THM] IND]);;

let IOTA_DEF = new_basic_definition
 `(@!) = \P:A->bool. @x. P x /\ !y. P y ==> x = y`;;
parse_as_binder "@!";;

let IOTA_ELIM_AND = prove
  (`!P Q. (?!(x:'a). P x /\ Q x) ==> Q (@!x. P x /\ Q x)`,
   REWRITE_TAC [IOTA_DEF;EXISTS_UNIQUE] THEN MESON_TAC []);;

(* The successor function. *)
let suc_def = new_definition
    `ind_suc n = let (A,B,C,D,Z,N) = dest_ind n in
                 mk_ind (A,B,C,D,Z,@!SN.
                   ?E. (?a. on_line C a /\ on_line E a /\ on_line N a)
		   /\ (?a. on_line A a /\ on_line D a /\ on_line E a)
                   /\ (?a. on_line B a /\ on_line E a /\ on_line SN a)
                   /\ between A SN Z /\ between A SN N)`;;

let (discover_tac : (thm Di.m -> thm Di.m) -> (thm list -> tactic) -> tactic) =
  fun d ttac ((hyps,_) as g) ->
  (ttac
     (Di.to_eager_thms !discovery_depth
        (d (Dim.of_list (map snd hyps)))))
    g;;

let by_cols  b = (Id.inferred b).Id.cols;;
let by_ncols b = (Id.inferred b).Id.ncols;; 

let this = -1;;

(* Successors exist. Could we refactor using inner and outer Pasch? *)

let suc_exists =
  let lemma = theorem
    ("!A B C D N. ~(?a. on_line A a /\ on_line B a /\ on_line N a)" ^
     "   /\ between A B C /\ between C N D" ^
     "   ==> ?N'. (?a. on_line B a /\ on_line D a /\ on_line N' a)" ^
     "   /\ between A N' N")
    [fix ["A:point";"B:point";"C:point";"D:point";"N:point"]
    ;assume "~(?a. on_line A a /\ on_line B a /\ on_line N a)" at [0]
    ;assume "between A B C /\ between C N D" at [1;2]
    ;clearly Id.by_pasch 
      (so consider ["N':point"] st 
         ("(?a. on_line B a /\ on_line D a /\ on_line N' a)" ^
             "/\ (between A N' N \/ between C N' N)")
         from [0;1;2])
    ;obviously (by_eqs o Di.split) qed from [0;1;2] by [g21;g23]] in
  theorem ("!A B C D Z N. ~(?a. on_line A a /\ on_line B a /\ on_line Z a)" ^
           "  /\ between A B C /\ between C Z D /\ (between A N Z \/ N = Z)" ^
           "  ==> ?!SN. ?E. (?a. on_line C a /\ on_line E a /\ on_line N a)" ^ 
           "        /\ (?a. on_line A a /\ on_line D a /\ on_line E a)" ^
           "        /\ (?a. on_line B a /\ on_line E a /\ on_line SN a)" ^
           "        /\ between A SN Z /\ between A SN N")
    [fix ["A:point";"B:point";"C:point";"D:point";"Z:point";"N:point"]
    ;set ("successor SN E <=> " ^
             "(?a. on_line C a /\ on_line E a /\ on_line N a)" ^
             "    /\ (?a. on_line A a /\ on_line D a /\ on_line E a)" ^
             "    /\ (?a. on_line B a /\ on_line E a /\ on_line SN a)" ^
             "    /\ between A SN Z /\ between A SN N")
    ;assume "~(?a. on_line A a /\ on_line B a /\ on_line Z a)" at [0]
    ;assume "between A B C" at [1]
    ;assume "between C Z D" at [2]
    ;assume "N = Z \/ between A N Z"
    ;per qed
      [[suppose "N = Z" at [3]
       ;consider ["SN:point"] st
         "(?a. on_line B a /\ on_line D a /\ on_line SN a) /\ between A SN N"
         from [0;1;2;3] by
         [SPECL [`A:point`;`B:point`;`C:point`;`D:point`;`N:point`] lemma]
         using (fun thms -> MAP_EVERY MP_TAC thms THEN SIMP_TAC []) at [4;5]
       ;obviously by_cols
         (hence "?SN E. successor SN E" by [g11_weak] from [2;3;4] at [6])
       ;have ("!SN' SN'' E' E''. successor SN' E' /\ successor SN'' E''" ^
                 "  ==> SN' = SN'' /\ E' = E''") proof
         [fix ["SN':point";"SN'':point";"E':point";"E'':point"]
         ;assume "successor SN' E' /\ successor SN'' E''" at [7;8]
         ;clearly (by_eqs o Id.conjuncts)
           (hence "E' = E''" from [0;1;2;7;8])
         ;hence "successor SN' E''" at [9] from [7]
         ;clearly (by_eqs o Id.conjuncts) (qed from [0;1;5;8])]
       ;qed from [6]]
      ;[suppose "between A N Z" at [3]
       ;have "?SN E. successor SN E" at [4]
         proof
         [consider ["Fa:point"] st
             ("(?a. on_line C a /\ on_line Fa a /\ on_line N a)" ^
                 "  /\ between A Fa D") at [4;5] proof
             [clearly by_pasch
                 (so consider ["Fa':point"] st
                    ("(?a. on_line C a /\ on_line Fa' a /\ on_line N a) " ^
                     "/\ (between A Fa' D \/ between D Fa' Z)") from [0;1;2])
             ;obviously (by_eqs o Di.split) qed from [0;1;2;3] by [g21;g23]]
         ;have "between C N Fa" at [6] proof
           [clearly by_pasch
               (consider ["SN:point"] st
                  ("(?a. on_line A a /\ on_line SN a /\ on_line Z a)" ^
 	           "/\ (between C SN Fa \/ between D SN Fa)") from [0;1;2;5])
           ;obviously (by_eqs o Di.split) qed from [0;1;2;3;4;5] by [g21;g23]]
         ;clearly by_ncols 
           (have "~(?a. on_line A a /\ on_line B a /\ on_line N a)"
  	      at [7] from [0;3])
         ;so consider ["SN:point"] st
           ("(?a. on_line B a /\ on_line Fa a /\ on_line SN a)" ^
               " /\ between A SN N") by
           [SPECL [`A:point`;`B:point`;`C:point`;`Fa:point`;`N:point`]
               lemma]
           from [1;6]
           using (fun thms -> MAP_EVERY MP_TAC thms THEN SIMP_TAC [])
           at [8;9]
         ;hence "between A SN Z" from [3] by
           [SPECL [`A:point`;`SN:point`;`N:point`;`Z:point`] five2]
         ;take ["SN";"Fa"]
         ;obviously by_cols qed from [4;5;8;9]]
       ;have ("!SN' SN'' E' E''. successor SN' E' /\ successor SN'' E''" ^
              "  ==> SN' = SN'' /\ E' = E''")
         proof
         [fix ["SN':point";"SN'':point";"E':point";"E'':point"]
         ;assume "successor SN' E' /\ successor SN'' E''" at [5;6]
         ;clearly (by_eqs o Di.split) (hence "E' = E''" from [0;1;2;3;5])
         ;hence "successor SN' E''" at [7] from [5]
         ;clearly (by_eqs o Di.split) (qed from [0;1;3;6;7])]
       ;qed from [4]]]];;

let suc_closed = prove
  (`dest_ind (ind_suc x) =
      let A,B,C,D,Z,N = dest_ind x in
      A,B,C,D,Z,@!SN.
        ?E. (?a. on_line C a /\ on_line E a /\ on_line N a)
        /\ (?a. on_line A a /\ on_line D a  /\ on_line E a)
        /\ (?a. on_line B a /\ on_line E a /\ on_line SN a)
        /\ between A SN Z /\ between A SN N`,
      REWRITE_TAC [suc_def] THEN REPEAT LET_TAC
        THEN POP_ASSUM (LABEL_TAC "0" o MATCH_MP dest_ind)
        THEN REWRITE_TAC [GSYM IND] THEN ASM_REWRITE_TAC [] THEN DISJ1_TAC
        THEN REWRITE_TAC [CONJ_ACI]
        THEN ASM_REWRITE_TAC [CONJ_ASSOC;LEFT_EXISTS_AND_THM]
        THEN MATCH_MP_TAC (REWRITE_RULE []
                             (ISPECL [`P:point->bool`;`\x. between A x Z`]
                                IOTA_ELIM_AND))
        THEN MP_TAC (SPECL [`A:point`;`B:point`;`C:point`;`D:point`
                           ;`Z:point`;`N:point`] suc_exists)
        THEN ASM_REWRITE_TAC [] THEN MESON_TAC []);;

let SELECT_CHOOSE =
  prove (`(?(x:'a). P x) ==> ?x. P x /\ x = ((@) P)`,
         DISCH_TAC THEN EXISTS_TAC `((@) P):'a`
           THEN REWRITE_TAC [] THEN ASM_SIMP_TAC [SELECT_AX]);;

let IOTA_CHOOSE =
  prove (`!P. (?!(x:'a). P x) ==> ?!x. P x /\ ((@!) P) = x`,
         REWRITE_TAC [IOTA_DEF] THEN MESON_TAC [SELECT_CHOOSE]);;

let UNIQUE_EXISTS_EXISTS =
  prove (`!P. (?!x. P x) ==> ?x. P x`, MESON_TAC []);;

let ONE_ONE = new_definition
  `ONE_ONE(f:A->B) = !x1 x2. (f x1 = f x2) ==> (x1 = x2)`;;

let ONTO = new_definition
  `ONTO(f:A->B) = !y. ?x. y = f x`;;

let ind_one_one = prove
  (`ONE_ONE ind_suc`,
   REWRITE_TAC [ONE_ONE] THEN REPEAT GEN_TAC THEN DISCH_TAC
     THEN SUBGOAL_THEN `dest_ind x1 = dest_ind x2` ASSUME_TAC THENL
      [POP_ASSUM MP_TAC
          THEN DISCH_THEN (MP_TAC o AP_TERM `dest_ind`)
          THEN REWRITE_TAC [suc_closed]
          THEN REPEAT (LET_TAC THEN POP_ASSUM (ASSUME_TAC o MATCH_MP dest_ind))
          THEN REWRITE_TAC [PAIR_EQ;IMP_CONJ] THEN SIMP_TAC []
          THEN REPLICATE_TAC 5 (DISCH_THEN (fun thm -> REWRITE_ASM_TAC [thm]))
          THEN MP_TAC
          (SPECL [`A:point`;`B:point`;`C:point`;`D:point`;`Z:point`;`N:point`]
             suc_exists)
          THEN MP_TAC
          (SPECL [`A:point`;`B:point`;`C:point`;`D:point`;`Z:point`;`N':point`]
             suc_exists)
          THEN ASM_REWRITE_TAC []
          THEN REPEAT
          (DISCH_THEN (CHOOSE_THEN (MAP_EVERY ASSUME_TAC o CONJUNCTS)
                         o MATCH_MP UNIQUE_EXISTS_EXISTS o MATCH_MP IOTA_CHOOSE)
             THEN FIRST_X_ASSUM CHOOSE_TAC)
          THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN REWRITE_ASM_TAC []
          THEN discover_tac (by_eqs o Di.conjuncts)
          REWRITE_ASM_TAC THEN discover_tac (by_eqs o Di.conjuncts) MESON_TAC
      ;ASM_MESON_TAC [IND]]);;

let ind_not_onto = theorem "~ONTO ind_suc"
  [consider ["A:point";"B:point";"C:point";"D:point";"Z:point"]
     st ("~(?a. on_line A a /\ on_line B a /\ on_line Z a)" ^
            " /\ between A B C /\ between C Z D") at [0;1]
     proof
     [consider ["A:point";"B:point";"Z:point"] st
       "~(?a. on_line A a /\ on_line B a /\ on_line Z a)" by [g13b] at [0]
     ;obviously by_neqs
       (so consider ["C:point"] st "between A B C" by [g22] at [1])
     ;obviously by_neqs qed from [0] by [g22]]
  ;otherwise consider ["x:ind"] st "dest_ind (ind_suc x) = (A,B,C,D,Z,Z)"
     by [REWRITE_RULE []
            (SPEC `(A:point,B:point,C:point,D:point,Z:point,N:point)`
               (CONJUNCT2 IND))]
     at [2] by [ONTO] from [0;1]
  ;consider ["A':point";"B':point";"C':point";"D':point";"Z':point";"N':point"]
     st "dest_ind x = A',B',C',D',Z',N'" at [3] by [exists_ind]
  (* Ugly let-reasoning *)
  ;hence ("A = A' /\ B = B' /\ C = C' /\ D = D' /\ Z = Z'" ^
          "/\ Z = (@!SN. ?E. (?a. on_line C a /\ on_line E a /\ on_line N' a)" ^
          "/\ (?a. on_line A a /\ on_line D a /\ on_line E a)" ^
          "/\ (?a. on_line B a /\ on_line E a /\ on_line SN a)" ^
          "/\ between A SN Z /\ between A SN N')")
     from [2] by [suc_closed;PAIR_EQ] at [4]
     using (MAP_EVERY MP_TAC o map (CONV_RULE (TOP_DEPTH_CONV let_CONV))
              o mutual_rewrite) 
  ;have ("?!SN. ?E. (?a. on_line C' a /\ on_line E a /\ on_line N' a)" ^
          "   /\ (?a. on_line A' a /\ on_line D' a /\ on_line E a)" ^
          "   /\ (?a. on_line B' a /\ on_line E a /\ on_line SN a)" ^
          "   /\ between A' SN Z' /\ between A' SN N'")
     from [3]
     by (map (SPECL [`A':point`;`B':point`;`C':point`
                    ;`D':point`;`Z':point`;`N':point`])
           [dest_ind;suc_exists])
     using (fun thms -> MAP_EVERY MP_TAC thms THEN MESON_TAC [])
  (* Horrible, but IOTA reasoning with our lemma makes things very difficult
     to match here. *)
  ;qed by [g21] from [4]
    using (MAP_EVERY (fun thm -> try MP_TAC (MATCH_MP IOTA_CHOOSE thm)
      with _ -> MP_TAC thm))];;

let INFINITY_AX =
  prove (`?f:ind->ind. ONE_ONE f /\ ~(ONTO f)`,
    EXISTS_TAC `ind_suc` THEN MESON_TAC [ind_one_one;ind_not_onto]);;
