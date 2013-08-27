(* ========================================================================= *)
(* Group II Axioms                                                           *)
(*                                                                           *)
(*                                   Phil Scott                              *)
(*                                                                           *)
(*               Centre for Intelligent Systems and their Applications       *)
(*                             University of Edinburgh                       *)
(* ========================================================================= *)

(* The fourth axiom is rendered with inclusive-or. Exclusion is proved later
   as supplement1. *)

let group2 =
  new_definition
    `Group2 (on_line : point -> line -> bool)
            (on_plane : point -> plane -> bool)
            (between : point -> point -> point -> bool)
    <=> (!A B C. between A B C
                   ==> ~(A = C)
                       /\ (?a. on_line A a /\ on_line B a /\ on_line C a)
		       /\ between C B A)
     /\ (!A C. ~(A = C) ==> ?B. between A C B)
     /\ (!A B C. between A B C ==> ~between A C B)
     /\ (!A B C P a 'a.
           ~(?a. on_line A a /\ on_line B a /\ on_line C a)
	   ==> on_plane A 'a /\ on_plane B 'a /\ on_plane C 'a
	   ==> (!P. on_line P a ==> on_plane P 'a)
	   ==> ~on_line A a /\ ~on_line B a /\ ~on_line C a
	   ==> on_line P a /\ between A P B
	   ==> (?Q. on_line Q a /\ (between A Q C \/ between B Q C)))`;;

new_constant ("between", `:(point -> point -> point -> bool)`);;

let group2_axioms =
  new_axiom `Group2 on_line on_plane between`;;

let [g21;g22;g23;g24] =
    (CONJUNCTS o C MATCH_MP group2_axioms o fst o EQ_IMP_RULE o SPEC_ALL)
       group2;;

(* We strengthen g21 to Hilbert's original rendering. *)
let g21 = prove
  (`between A B C
   ==> ~(A = C) /\ ~(B = C) /\ ~(A = C)
       /\ (?a. on_line A a /\ on_line B a /\ on_line C a) /\
       between C B A`,
     MESON_TAC [g21;g23]);;
