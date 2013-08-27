(* Old proofs, before we learned about the inner and outer Pasch axioms. *)

let three_pasch_match = theorem
  "!A C. ~(A = C) ==> ?D. between A D C"
  [fix ["A:point";"C:point"]
  ;assume "~(A = C)"
  ;so consider ["E:point"]
    st "~(?a. on_line A a /\ on_line C a /\ on_line E a)"
    at [0] by [g12;g13b]
  ;obviously by_neqs
    (consider ["Fa:point"] at [1]
       st "between A E Fa" from [0] by [g22])
  ;obviously by_neqs
    (consider ["G:point"] at [2]
       st "between Fa C G" from [0;1] by [g22])
  ;obviously by_incidence
     (so consider ["D:point"] st
        "(?a. on_line E a /\ on_line G a /\ on_line D a)
         /\ (between A D C \/ between Fa D C)"
        using K (MATCH_MP_TAC (REWRITE_RULE [IMP_IMP] pasch)))
     from [0;1;2]
  ;obviously (by_eqs o Di.split) qed from [0;1;2] by [g21;g23]];;

(* THEOREM THREE *)
let three_pasch =
  theorem ("!A C. ~(A = C) ==> ?D. between A D C")
    [fix ["A:point";"C:point"]
    ;assume "~(A = C)"
    ;so consider ["E:point"]
      st "~(?a. on_line A a /\ on_line C a /\ on_line E a)"
      at [0] by [triangle]
    ;obviously by_neqs
      (consider ["Fa:point"] at [1]
         st "between A E Fa" from [0] by [g22])
    ;obviously by_neqs
      (consider ["G:point"] at [2]
         st "between Fa C G" from [0;1] by [g22])
    ;clearly by_pasch
      (consider ["D:point"] st
         ("(?a. on_line D a /\ on_line E a /\ on_line G a)" ^
             "/\ (between A D C \/ between C D Fa)") by [g21]
         from [0;1;2])
    ;obviously (by_eqs o Di.split) qed from [0;1;2] by [g21;g23]];;

(* An alternative proof of THEOREM FOUR *)

(* h ("!A B C. (?a. on_line A a /\ on_line B a /\ on_line C a) " ^ *)
(*      "==> ~(A = B) /\ ~(A = C) /\ ~(B = C) " ^ *)
(*      "==> ~between A C B /\ ~between B A C ==> between A B C");; *)
(* f (fix ["A:point";"B:point";"C:point"]);; *)
(* f (assume ("(?a. on_line A a /\ on_line B a /\ on_line C a)" ^ *)
(*            "/\ ~(A = B) /\ ~(A = C) /\ ~(B = C)" ^ *)
(*            "/\ ~between A C B /\ ~between B A C") at 0);; *)
(* f (so consider ["D:point"] st "~(?a. on_line A a /\ on_line B a /\ on_line D a)" *)
(*      by [triangle]);; *)
(* f (obviously Id.neqs (consider ["G:point"] st "between B D G" at 1 by [g22]));; *)

(* (\* Interesting that this fails! *\) *)
(* (\* f (consider ["Fa:point"] st "COLLINEAR {B, E, Fa} /\ between C Fa D" by *\) *)
(* (\*      pasch_on' `~COLLINEAR {C, D, G}` (`B:point`,`E:point`));; *\) *)

(* f (consider ["E:point"] st *)
(*      "(?a. on_line A a /\ on_line D a /\ on_line E a) /\ between C E G" *)
(*      at 2);; *)
(*   f (consider ["E:point"] st *)
(*        ("(?a. on_line A a /\ on_line D a /\ on_line E a) " ^ *)
(*           "/\ (between C E G \/ between B E C)") *)
(*        by [pasch_on (`B:point`,`G:point`,`C:point`,`D:point`,`A:point`)] *)
(*        from [1]);; *)
(*   f (obviously one_eq (qed from [0] by [g21;g23]));; *)
(* f (consider ["Fa:point"] st   *)
(*      "(?a. on_line C a /\ on_line D a /\ on_line Fa a) /\ between B Fa E" *)
(*      at 3);; *)
(*   f (consider ["Fa:point"] st *)
(*        ("(?a. on_line C a /\ on_line D a /\ on_line Fa a) " ^ *)
(*           "/\ (between B Fa E \/ between E Fa G)") *)
(*        by [pasch_on (`B:point`,`G:point`,`E:point`,`D:point`,`C:point`)] *)
(*        from [1]);; *)
(*   f (obviously one_eq (qed from [2] by [g21;g23]));; *)
(* f (have "between A D E");; *)
(*   f (consider ["D':point"] st *)
(*        ("(?a. on_line C a /\ on_line D' a /\ on_line Fa a) " ^ *)
(*           "/\ (between A D' B \/ between A D' E)") *)
(*        by [pasch_on (`B:point`,`E:point`,`A:point`,`Fa:point`,`C:point`)] *)
(*        from [3]);; *)
(*   f (obviously two_eqs (qed from [0] by [g21;g23]));; *)
(* f (so consider ["B':point"] st *)
(*      ("(?a. on_line B a /\ on_line B' a /\ on_line D a)" ^ *)
(*         "/\ (between A B' C \/ between C B' E)") *)
(*      by [pasch_on (`A:point`,`E:point`,`C:point`,`D:point`,`B:point`)]);; *)
(* f (obviously two_eqs (qed from [2] by [g21;g23]));; *)

(* We don't need to assume that ABCD are collinear, since this is implied by
the betweeness hypotheses. *) (* THEOREM FIVE --- PART 1 *)
let five1 =
  let lemma = 
    theorem
      ("!A B C D. between A B C /\ between B C D ==> between A C D")
      [fix ["A:point";"B:point";"C:point";"D:point"]
      ;assume "between A B C" at [0]
      ;assume "between B C D" at [1]
      ;consider ["E:point"] st
        "~(?a. on_line A a /\ on_line B a /\ on_line E a)"
        at [2] from [0] by [g21;triangle]
      ;obviously by_neqs
        (so consider ["Fa:point"]
           st "between C E Fa" at [3] from [0] by [g22])
      ;(* This step is needed so we can eliminate the case-split when we
          find H. *)
       consider ["G:point"] st
         ("(?a. on_line B a /\ on_line Fa a /\ on_line G a) /\ between A G E") 
         at [4;5]
         proof
         [clearly by_pasch
             (consider ["G:point"] st
                ("(?a. on_line B a /\ on_line Fa a /\ on_line G a)" ^
                    "/\ (between A G E \/ between C G E)") from [0;2;3])
         ;obviously (by_eqs o Di.split) qed by [g21;g23] from [0;2;3]]
      ;have "between B G Fa" at [6] proof
        [clearly by_pasch
            (consider ["G':point"] st
               ("(?a. on_line A a /\ on_line E a /\ on_line G' a)" ^
                   "/\ (between B G' C \/ between B G' Fa)")
               from [0;2;3])
        ;obviously (by_eqs o Di.split) qed by [g21;g23] from [0;2;4;5]]
      ;consider ["H:point"] st
        ("(?a. on_line C a /\ on_line Fa a /\ on_line H a) /\ between D H G") 
        at [7;8]
        proof
        [clearly by_pasch
            (consider ["H:point"] st
               ("(?a. on_line C a /\ on_line Fa a /\ on_line H a)" ^
                   "/\ (between B H G \/ between D H G)")
               from [0;1;2;3;4;5;6])
        ;obviously (by_eqs o Di.split) qed by [g21;g23] from [2;3;5;6]]
      ;have "~(A = D)" at [9] from [0;1] by [g21;g23]
      ;clearly by_pasch
        (so consider ["C':point"] st
           ("(?a. on_line C' a /\ on_line E a /\ on_line H a)" ^
               "/\ (between A C' D \/ between A C' G)") from [0;1;2;5;8;9])
      ;obviously (by_eqs o Di.split) qed from [0;1;2;3;5;7;8;9] by [g21;g23]]
  in MESON [lemma;g21]
  `!A B C D. between A B C /\ between B C D
      ==> between A B D /\ between A C D`;;
