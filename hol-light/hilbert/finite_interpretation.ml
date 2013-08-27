(* ========================================================================= *)
(* Model of Hilbert's axioms as a tetrahedron, and proof that this model is  *)
(* minimal.                                                                  *)
(*                                                                           *)
(*                                   Phil Scott                              *)
(*                                                                           *)
(*               Centre for Intelligent Systems and their Applications       *)
(*                             University of Edinburgh                       *)
(* ========================================================================= *)

let ps     = define_type "fp    = P1 | P2 | P3 | P4";;
let lines  = define_type "fline = L1 | L2 | L3 | L4 | L5 | L6";;

let ind_ps = prove (`!P. (!x. P x) <=> P P1 /\ P P2 /\ P P3 /\ P P4`,
                        MESON_TAC [fst ps]);;
let ind_lines = prove
  (`!P. (!x. P x)
   <=> P L1 /\ P L2 /\ P L3 /\ P L4 /\ P L5 /\ P L6`,
       MESON_TAC [fst lines]);;

let dist_ps = prove_constructors_distinct (snd ps);;
let dist_lines = prove_constructors_distinct (snd lines);;
  
let ex_ps, ex_lines =
  let f ind =
    REWRITE_RULE []
      (AP_TERM `~`
         (REWRITE_RULE [TAUT `~P /\ ~Q <=> ~(P \/ Q)`;FORALL_NOT_THM] ind)) in
  f (SPEC (`\x:fp. ~(P x)`) ind_ps),
  f (SPEC (`\x:fline. ~(P x)`) ind_lines);;

(* The first six clauses define the base of a tetrahedron: P1,P2,P3 joined by L1,L2,L3 *)  
(* The next six clauses define the remaining vertex connected to the
   base. *)

let _,_,on_line = new_inductive_definition
  `on_line' P1 L1 /\ on_line' P2 L1
   /\ on_line' P1 L2 /\ on_line' P3 L2
   /\ on_line' P2 L3 /\ on_line' P3 L3
   /\ on_line' P1 L4 /\ on_line' P4 L4
   /\ on_line' P2 L5 /\ on_line' P4 L5
   /\ on_line' P3 L6 /\ on_line' P4 L6`;;

let _,_,on_plane = new_inductive_definition
  `on_plane' P1 P1 /\ on_plane' P2 P1 /\ on_plane' P3 P1
   /\ on_plane' P1 P2 /\ on_plane' P2 P2 /\ on_plane' P4 P2
   /\ on_plane' P1 P3 /\ on_plane' P3 P3 /\ on_plane' P4 P3
   /\ on_plane' P2 P4 /\ on_plane' P3 P4 /\ on_plane' P4 P4`;;

let ex_ps_tac,ex_lines_tac,ind_ps_tac,ind_lines_tac =
  REWRITE_TAC [ex_ps] THEN REWRITE_TAC [dist_ps],
  REWRITE_TAC [ex_lines] THEN REWRITE_TAC [dist_lines],
  REWRITE_TAC [ind_ps] THEN REWRITE_TAC [dist_ps],
  REWRITE_TAC [ind_lines] THEN REWRITE_TAC [dist_lines];;

let tetra_model =
  prove (`Group1 on_line' on_plane'`,
         REWRITE_TAC [group1;on_line;on_plane]
           THEN REPEAT (DISCH_TAC THEN POP_ASSUM_LIST REWRITE_TAC) 
           THEN REPEAT CONJ_TAC THEN EVERY
           [ex_ps_tac;ind_ps_tac;ex_lines_tac;ind_lines_tac]);;

let line =
  prove (`!A B. ?a. on_line A a /\ on_line B a`,
         REPEAT GEN_TAC THEN ASM_CASES_TAC `A:point = B`
      THEN ASM_MESON_TAC [g11;g13a]);;
    
let ncolneq =
  prove (`!A B C. ~(?a. on_line A a /\ on_line B a /\ on_line C a)
         ==> ~(A = B) /\ ~(A = C) /\ ~(B = C)`,
         MESON_TAC [line]);;           

g `?A B C D a b c d e f a' b' c' d'.
     ~(A = B) /\ ~(A = C) /\ ~(A = D)
  /\ ~(B = C) /\ ~(B = D) 
  /\ ~(C = D)
  /\ ~(a = b) /\ ~(a = c) /\ ~(a = d) /\ ~(a = e) /\ ~(a = f)
p  /\ ~(b = c) /\ ~(b = d) /\ ~(b = e) /\ ~(b = f)
  /\ ~(c = d) /\ ~(c = e) /\ ~(c = f)
  /\ ~(d = e) /\ ~(d = f)
  /\ ~(e = f)
  /\ ~(a' = b') /\ ~(a' = c') /\ ~(a' = d')
  /\ ~(b' = c') /\ ~(b' = d')
  /\ ~(c' = d')
  /\ on_line A a /\ on_line B a
  /\ on_line A b /\ on_line C b
  /\ on_line B c /\ on_line C c
  /\ on_line A d /\ on_line D d
  /\ on_line B e /\ on_line D e
  /\ on_line C f /\ on_line D f
  /\ on_plane A a' /\ on_plane B a' /\ on_plane C a'
  /\ on_plane A b' /\ on_plane B b' /\ on_plane D b'
  /\ on_plane A c' /\ on_plane C c' /\ on_plane D c'
  /\ on_plane B d' /\ on_plane C d' /\ on_plane D d'`;;
e (REPEAT_TCL CHOOSE_THEN (LABEL_TAC "0") (SPEC_ALL plane_three));;
f (so consider ["D:point"] st "~on_plane D a'" at 1 by [g18]);;
f (take ["A:point";"B:point";"C:point";"D:point"]);;
f (have "~(A:point = B) /\ ~(A = C) /\ ~(A = D) /\ ~(B = C) /\ ~(B = D) /\ ~(C = D)" at 2
     from [0;1] by [ncolneq]);;
f (so consider ["a:line";"b:line";"c:line";"d:line";"e:line";"f:line"] st
     ("on_line A a /\ on_line B a /\ on_line A b /\ on_line C b /\ on_line B c /\ on_line C c " ^
      "/\ on_line A d /\ on_line D d /\ on_line B e /\ on_line D e /\ on_line C f /\ on_line D f")
     at 3 from [2] by [g11]);;
f (take ["a:line";"b:line";"c:line";"d:line";"e:line";"f:line"]);;
f (have "!a. ~(on_line A a /\ on_line B a /\ on_line D a)" at 4 from [0;1;2;3] by [g16]);;
e (POP_ASSUM (fun thm -> CHOOSE_THEN (LABEL_TAC "5") (MATCH_MP g14a thm) THEN ASSUME_TAC thm));;
f (have "!a. ~(on_line A a /\ on_line C a /\ on_line D a)" at 6 from [0;1;2;3] by [g16]);;
e (POP_ASSUM (fun thm -> CHOOSE_THEN (LABEL_TAC "7") (MATCH_MP g14a thm) THEN ASSUME_TAC thm));;
f (have "!a. ~(on_line B a /\ on_line C a /\ on_line D a)" at 8 from [0;1;2;3] by [g16]);;
e (POP_ASSUM (fun thm -> CHOOSE_THEN (LABEL_TAC "9") (MATCH_MP g14a thm) THEN ASSUME_TAC thm));;
f (take ["a':plane";"a'':plane";"a''':plane";"a'''':plane"]);;
e (ASM_REWRITE_TAC []);;
e (REPEAT CONJ_TAC THEN (fun tm ->
  if type_of (fst (dest_eq (dest_neg (snd tm)))) = `:line`
  then ASM_MESON_TAC [] tm
  else ALL_TAC tm));;
e (ASM_MESON_TAC []);;
e (REFUTE_THEN ASSUME_TAC);;
f (hence "a':plane=a''" from [0;1;7] by [g15]);;
e (ASM_MESON_TAC []);;
e (REFUTE_THEN ASSUME_TAC);;
f (hence "a':plane=a''" from [0;1;9] by [g15]);;
e (ASM_MESON_TAC []);;
e (REFUTE_THEN ASSUME_TAC);;
f (hence "a':plane=a''" from [0;1;5;7] by [g15]);;
e (ASM_MESON_TAC []);;
e (REFUTE_THEN ASSUME_TAC);;
f (hence "a':plane=a''" from [0;1;5;9] by [g15]);;
e (ASM_MESON_TAC []);;
e (REFUTE_THEN ASSUME_TAC);;
f (hence "a':plane=a''" from [0;1;7;9] by [g15]);;
e (ASM_MESON_TAC []);;
let tetra_smallest = top_thm ();;
