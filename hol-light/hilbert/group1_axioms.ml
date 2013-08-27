(* ========================================================================= *)
(* Group I Axioms                                                            *)
(*                                                                           *)
(*                                   Phil Scott                              *)
(*                                                                           *)
(*               Centre for Intelligent Systems and their Applications       *)
(*                             University of Edinburgh                       *)
(* ========================================================================= *)

(* We don't have unicode, so the convention is the same as for type-variables:
   'a is read as "alpha". *)

let group1 = 
  new_definition
    `Group1 (on_line : 'point -> 'line -> bool)
            (on_plane : 'point -> 'plane -> bool)
    <=> (!A B. ~(A = B) ==> ?a. on_line A a /\ on_line B a)
     /\ (!A B a b. ~(A = B) ==> on_line A a /\ on_line B a /\
	                        on_line A b /\ on_line B b
       	                    ==> a = b)
     /\ (!a. ?A B. ~(A = B) /\ on_line A a /\ on_line B a)
     /\ (?A B C. !a. ~(on_line A a /\ on_line B a /\ on_line C a))
     /\ (!A B C. (!a. ~(on_line A a /\ on_line B a /\ on_line C a))
	                 ==> ?'a. on_plane A 'a /\ on_plane B 'a /\ on_plane C 'a)
     /\ (!'a. ?A. on_plane A 'a)
     /\ (!A B C 'a 'b. (!a. ~(on_line A a /\ on_line B a /\ on_line C a))
  	            ==> on_plane A 'a /\ on_plane B 'a /\ on_plane C 'a
	                /\ on_plane A 'b /\ on_plane B 'b /\ on_plane C 'b
		        ==> 'a = 'b)
     /\ (!A B a 'a P. ~(A = B) ==> on_plane A 'a /\ on_plane B 'a
	                           /\ on_line A a /\ on_line B a
				   ==> on_line P a ==> on_plane P 'a)
     /\ (!A 'a 'b. ~('a = 'b) ==> on_plane A 'a /\ on_plane A 'b
	                      ==> ?B. ~(A = B) /\ on_plane B 'a /\ on_plane B 'b)
     /\ (?A B C D. !'a. ~(on_plane A 'a /\ on_plane B 'a
                            /\ on_plane C 'a /\ on_plane D 'a))`;;

(* A relativised version of enough axioms to prove that all sorts are inhabited. *)
let group1_relative = 
  new_definition
    `Group1_relative (point : 'a -> bool)
                     (line  : 'a -> bool)
                     (plane : 'a -> bool) 
                     (lie : 'a -> 'a -> bool)
    <=> (!A B. point A /\ point B ==> ~(A = B)
         ==> ?a. line a /\ lie A a /\ lie B a)
        /\ (?A B C. point A /\ point B /\ point C
            /\ !a. line a ==> ~(lie A a /\ lie B a /\ lie C a))
        /\ (!A B C. point A /\ point B /\ point C
           ==> (!a. line a ==> ~(lie A a /\ lie B a /\ lie C a))
           ==> ?'a. plane 'a /\ lie A 'a
                    /\ lie B 'a /\ lie C 'a)
        /\ (?A B C D. point A /\ point B /\ point C /\ point D /\
            !'a. plane 'a ==> ~(lie A 'a /\ lie B 'a
                 /\ lie C 'a /\ lie D 'a))`;;

(* Technically, we do not need any primitive types. *)
let inhabited = prove
  (`Group1_relative point line plane lie
   ==> (?A:'a a 'a. point A /\ line a /\ plane 'a)`,
   PURE_REWRITE_TAC [group1_relative]
     THEN DISCH_THEN (MAP_EVERY (fun (l,thm) -> LABEL_TAC l thm)
                        o zip ["1";"2";"3";"4"] o CONJUNCTS)
     THEN REMOVE_THEN "2" (REPEAT_TCL CHOOSE_THEN MP_TAC)
     THEN DISCH_TAC THEN SUBGOAL_THEN `point (A:'a):bool` MP_TAC
     THENL [ASM_REWRITE_TAC []; ALL_TAC]
     THEN REMOVE_THEN "3" (fun thm -> FIRST_ASSUM (CHOOSE_TAC o MATCH_MP
                                                     (REWRITE_RULE
                                                        [CONJ_ACI;IMP_IMP]
                                                        thm)))
     THEN SUBGOAL_THEN `?D:'a. point D /\ ~lie D ('a:'a)` MP_TAC
     THENL [ASM_MESON_TAC []; ALL_TAC] THEN REPEAT DISCH_TAC
     THEN FIRST_ASSUM CHOOSE_TAC THEN SUBGOAL_THEN `~(A:'a=D)` MP_TAC
     THEN ASM_MESON_TAC []);;

new_type ("point",0);;
new_type ("line",0);;
new_type ("plane",0);;
new_constant ("on_line", `:(point -> line -> bool)`);;
new_constant ("on_plane", `:(point -> plane -> bool)`);;

let group1_axioms =  new_axiom `Group1 on_line on_plane`;;
let [g11;g12;g13a;g13b;g14a;g14b;g15;g16;g17;g18] =
  (CONJUNCTS o C MATCH_MP group1_axioms o fst o EQ_IMP_RULE o SPEC_ALL)
    group1

(* REMARKS *)
(* Axioms g11 and g12 establish that two points uniquely determine a
   line.

   The third axiom is rendered in the highly ambiguous prose: "There
   exist at least two points on a line. There exist at least three
   points that do not lie on a line."

   We split the two clauses into g13a and g13b.

   The first axiom could be understood either as:
   1) there is a line and two points which do not lie on it
   or
   2) for every line, there are two points which do not lie on it (the
   two points depending on the chosen line).

   I believe that, on the first rendering, we cannot rule out the
   existence of an indefinite number of lines which contain no points
   or exactly one point, at least not until the completeness axiom.

   The second axiom could be understood either as:
   1) there is a line and three points which do not lie on it
   or
   2) for every line, there are three points which do not lie on it
   (the three points depending on the chosen line)
   or
   3) for every line, there are three points which do not lie
   simultaneously on it (the three points depending on the chosen line)
   4) there are three points such that, for every line, they do not
   lie on it (the three points being independent of the chosen line)

   I believe that, on the first and last renderings, we cannot rule
   out planes whose points are collinear, at least not until the
   completeness axiom. Furthermore, the first rendering here implies
   the previous first rendering. The third rendering gives us three times as
   many extra points as the second. In all, the second is perhaps to
   be preferred. This gives us a consistent interpretation of each clause:

   "There exist at least two points on a line"
   becomes
   "on any line, there are two points that lie simultaneously on it"

   "There exist at least three points that do not lie on a line"
   becomes
   "on any line, there are three points that do not lie simultaneously
   on it"

   The last rendering becomes:
   !a. ?P Q R. ~(P = Q) /\ ~(P = R) /\ ~(Q = R) /\
   ~(on_line P a /\ on_line Q a /\ on_line R a)

   which, given the existence of at least three points, is equivalent to
   !a. ?P. ~on_line P a

   This is the rendering we have used, and we have followed it to
   render the last axiom.

   I am not clear on the real importance of axiom g16. While it is
   required given the rendering of later axioms, I'm not clear why we
   can't omit this, and then later, instead of making assumptions such
   as "point P lies in plane 'a", we can't strengthen the assumption to
   "point P lies on line a and there exists points ~(A = B) that lie
   on both a and 'a."
   Well, there is one answer to this. My proof that every plane
   contains at least three non-collinear points requires it.
*)
