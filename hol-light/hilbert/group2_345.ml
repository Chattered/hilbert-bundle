(* ========================================================================= *)
(* The first three theorems of Group II                                      *)
(*                                                                           *)
(*                                   Phil Scott                              *)
(*                                                                           *)
(*               Centre for Intelligent Systems and their Applications       *)
(*                             University of Edinburgh                       *)
(* ========================================================================= *)

let BET_SYM  = prove
  (`!A B C. between A B C <=> between C B A`, MESON_TAC [g21]);;
let BET_NEQS = prove
  (`!A B C. between A B C ==> ~(A=B) /\ ~(A=C) /\ ~(B=C)`, MESON_TAC [g21]);;
let BET_REFL1 = prove
  (`!A B. ~between A A B`, MESON_TAC [BET_NEQS]);;
let BET_REFL2 = prove
  (`!A B. ~between A B A`, MESON_TAC [BET_NEQS]);;
let BET_REFL3 = prove
  (`!A B. ~between B A A`, MESON_TAC [BET_NEQS]);;

module Id = Incidence_discovery(Di);;
let by_eqs b = (Id.inferred b).Id.eqs;;
let by_neqs b = (Id.inferred b).Id.neqs;;
let by_ncols b = (Id.inferred b).Id.ncols;;
let by_pasch = Id.by_pasch;;

let inner_pasch = theorem
  "!A B C D X. 
   ~(?a. on_line A a /\ on_line B a /\ on_line C a)
   /\ between A B D /\ between A X C
   ==> ?Y. between D Y X /\ between B Y C"
  [fix ["A:point";"B:point";"C:point";"D:point";"X:point"]
  ;assume "~(?a. on_line A a /\ on_line B a /\ on_line C a)" at [0]
  ;assume "between A B D /\ between A X C" at [1;2]
  ;consider ["Y:point"]
     st "between B Y C /\ ?a. on_line D a /\ on_line X a /\ on_line Y a"
     at [3] proof
     [clearly (by_pasch o Id.conjuncts)
         (so consider ["Y:point"] st
            "(?a. on_line D a /\ on_line Y a /\ on_line X a)
             /\ (between A Y B \/ between B Y C)")
         from [0;1;2]
     ;obviously (by_eqs o Di.split) qed from [0;1;2] by [g23]]
  ;have "between D Y X" proof
    [clearly (by_pasch o Id.conjuncts)
       (so consider ["Y':point"] st
          "(?a. on_line B a /\ on_line C a /\ on_line Y' a)
           /\ (between A Y' X \/ between D Y' X)") from [0;1;2]
    ;obviously (by_eqs o Di.split) qed from [0;2;3] by [g23]]
  ;qed from [3]];;

(* This is Veblen's Axiom VIII from his thesis. *)
let outer_pasch = theorem
  "!A B C D X. 
     ~(?a. on_line A a /\ on_line B a /\ on_line C a)
     /\ between A B D /\ between B X C
     ==> ?Y. between D X Y /\ between A Y C"
  [fix ["A:point";"B:point";"C:point";"D:point";"X:point"]
  ;assume "~(?a. on_line A a /\ on_line B a /\ on_line C a)" at [0]
  ;assume "between A B D /\ between B X C" at [1;2]
  ;consider ["Y:point"] st
     "between A Y C /\ ?a. on_line D a /\ on_line X a /\ on_line Y a"
     at [3] proof
     [obviously by_pasch
         (so consider ["Y:point"] st
            "(?a. on_line D a /\ on_line Y a /\ on_line X a)
             /\ (between A Y B \/ between A Y C)"
            from [0;1;2])
     ;obviously (by_eqs o Di.split) qed from [0;1;2] by [g23]]
  ;have "between D X Y" proof
    [clearly (by_pasch o Di.split)
        (so consider ["Y':point"] st
           "(?a. on_line B a /\ on_line Y' a /\ on_line X a)
            /\ (between A Y' Y \/ between D Y' Y)"
           from [0;1;2])
    ;obviously (by_eqs o Di.split) qed from [0;2;3] by [g23]]
  ;qed from [3]];;

let three = theorem
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
  ;obviously by_ncols
     (qed from [0;1] by [inner_pasch;g21])];;

(* Theorem four using inner and outer pasch. *)
let four = theorem
  ("!A B C a. on_line A a /\ on_line B a /\ on_line C a
    ==> ~(A = B) /\ ~(A = C) /\ ~(B = C)
    ==> between A B C \/ between B A C \/ between A C B")
  [fix ["A:point";"B:point";"C:point";"a:line"]
  ;assume "(?a. on_line A a /\ on_line B a /\ on_line C a)" at [0]
  ;assume "~(A = B)" at [1]
  ;assume "~(A = C)" at [2]
  ;assume "~(B = C)" at [3]
    (* It's pretty cool the way you can use assume like this. *)
  ;assume "~between A C B /\ ~between B A C" at [4]
  ;consider ["D:point"] st "~(?a. on_line A a /\ on_line B a /\ on_line D a)"
    from [1] at [5] by [g12;g13b]
  ;obviously by_neqs
    (so consider ["G:point"] st "between B D G" by [g22] at [6])
  ;consider ["E:point"] st
    ("(?a. on_line A a /\ on_line D a /\ on_line E a) /\ between C E G")
    at [7;8]
    proof
    [clearly by_pasch
        (consider ["E:point"] st
           ("(?a. on_line A a /\ on_line D a /\ on_line E a)" ^
               "/\ (between B E C \/ between C E G)") by [g21]
           from [0;2;3;5;6])
    ;obviously (by_eqs o Di.split) qed from [0;3;4;5] by [g21;g23]]
  ;consider ["Fa:point"] st
    ("(?a. on_line C a /\ on_line D a /\ on_line Fa a) /\ between A Fa G")
    at [9;10]
    proof
    [clearly by_pasch
        (consider ["Fa:point"] st
           ("(?a. on_line C a /\ on_line D a /\ on_line Fa a)" ^
               "/\ (between A Fa B \/ between A Fa G)") by [g21]
           from [0;2;3;5;6])
    ;obviously (by_eqs o Di.split) qed from [0;4;5] by [g21;g23]]
  ;have "between A D E" proof
    [obviously by_ncols
       (so consider ["D':point"] st
          ("between C D' Fa /\ between E D' A")
          using K (MATCH_MP_TAC inner_pasch)
          from [0;2;5;6;8;10] by [BET_SYM])
    ;obviously (by_eqs o Di.split) qed from [0;2;5;7;9] by [g21;g23]]
  ;obviously by_ncols
     (so consider ["B':point"] st
        "between G D B' /\ between C B' A"
        using K (MATCH_MP_TAC outer_pasch))
     from [0;2;5;7;8] by [BET_SYM]
  ;obviously (by_eqs o Di.split) qed from [0;2;5;6] by [BET_SYM]];;

let four = theorem
  ("!A B C a. on_line A a /\ on_line B a /\ on_line C a " ^
      "==> ~(A = B) /\ ~(A = C) /\ ~(B = C) " ^
      "==> between A B C \/ between B A C \/ between A C B")
  [fix ["A:point";"B:point";"C:point";"a:line"]
  ;assume "(?a. on_line A a /\ on_line B a /\ on_line C a)" at [0]
  ;assume "~(A = B)" at [1]
  ;assume "~(A = C)" at [2]
  ;assume "~(B = C)" at [3]
    (* It's pretty cool the way you can use assume like this. *)
  ;assume "~between A C B /\ ~between B A C" at [4]
  ;consider ["D:point"] st "~(?a. on_line A a /\ on_line B a /\ on_line D a)"
    from [1] at [5] by [g12;g13b]
  ;obviously by_neqs
    (so consider ["G:point"] st "between B D G" by [g22] at [6])
  ;consider ["E:point"] st
    ("(?a. on_line A a /\ on_line D a /\ on_line E a) /\ between C E G")
    at [7;8]
    proof
    [clearly by_pasch
        (consider ["E:point"] st
           ("(?a. on_line A a /\ on_line D a /\ on_line E a)" ^
               "/\ (between B E C \/ between C E G)") by [g21]
           from [0;2;3;5;6])
    ;obviously (by_eqs o Di.split) qed from [0;4;5] by [g21;g23]]
  ;consider ["Fa:point"] st
    ("(?a. on_line C a /\ on_line D a /\ on_line Fa a) /\ between A Fa G")
    at [9;10]
    proof
    [clearly by_pasch
        (consider ["Fa:point"] st
           ("(?a. on_line C a /\ on_line D a /\ on_line Fa a)" ^
               "/\ (between A Fa B \/ between A Fa G)") by [g21]
           from [0;2;3;5;6])
    ;obviously (by_eqs o Di.split) qed from [0;4;5] by [g21;g23]]
  ;have "between A D E" at [11] proof
    [clearly by_pasch
        (consider ["D':point"] st
           ("(?a. on_line C a /\ on_line D' a /\ on_line Fa a)" ^
               "/\ (between A D' E \/ between E D' G)")
           from [0;2;5;6;8;10])
    ;obviously (by_eqs o Di.split) qed from [0;5;6;7;8;9;10] by [g21;g23]]
  ;clearly (by_pasch o Di.split)
    (so consider ["B':point"] st
       ("(?a. on_line B a /\ on_line B' a /\ on_line D a)" ^
           "/\ (between A B' C \/ between C B' E)")
       from [0;2;3;5;7;11])
  ;obviously (by_eqs o Di.split) qed from [0;3;5;6;8] by [g21;g23]];;

(* I'd rather use BET_NEQS and BET_SYM explicitly in these arguments, rather
   than g21 --- it's much faster. In fact, g21 should have been split into
   g21a, g21b and g21c. I use g21 here only to match the prose.*)
let five1 =
  let lemma = theorem
    "!A B C D. between A B C /\ between B C D ==> between A C D"
    [fix ["A:point";"B:point";"C:point";"D:point"]
    ;assume "between A B C" at [0]
    ;assume "between B C D" at [1]
    ;consider ["E:point"] st
      "~(?a. on_line A a /\ on_line B a /\ on_line E a)"
      at [2] from [0] by [g12;g13b;g21]
    ;obviously by_neqs
      (so consider ["Fa:point"]
         st "between C E Fa" at [3] from [0] by [g22])
    ;obviously by_ncols
      (so consider ["G:point"]
         st "between A G E /\ between B G Fa"
         at [4;5] from [0;2;3] by [inner_pasch;g21])
    ;obviously by_ncols
      (consider ["H:point"]
         st "between C H Fa /\ between D H G" at [6] from [0;1;2;3;5]
         by [inner_pasch;g21])
    ;have "~(A = D)" at [7] from [0;1] by [g21;g23]
    ;obviously by_ncols
      (so consider ["C':point"]
         st "between E H C' /\ between A C' D" from [0;1;2;4;6;7]
         by [outer_pasch;g21])
    ;obviously (by_eqs o Di.split) qed from [0;1;2;3;6;7]] in
  MESON [lemma;g21]
    `!A B C D. between A B C /\ between B C D
     ==> between A B D /\ between A C D`;;

let five1 =
  let lemma = theorem
    "!A B C D. between A B C /\ between B C D ==> between A C D"
    [fix ["A:point";"B:point";"C:point";"D:point"]
    ;assume "between A B C" at [0]
    ;assume "between B C D" at [1]
    ;consider ["E:point"] st
      "~(?a. on_line A a /\ on_line B a /\ on_line E a)"
      at [2] from [0] by [g21;triangle]
    ;obviously by_neqs
      (so consider ["Fa:point"]
         st "between C E Fa" at [3] from [0] by [g22])
    ;obviously by_ncols
      (so consider ["G:point"]
         st "between A G E /\ between B G Fa"
         at [4;5] from [0;2;3] by [inner_pasch;BET_SYM])
    ;obviously by_ncols
      (consider ["H:point"]
         st "between C H Fa /\ between D H G" at [6] from [0;1;2;3;5]
         by [inner_pasch;BET_SYM])
    ;have "~(A = D)" at [7] from [0;1] by [g21;g23]
    ;obviously by_ncols
      (so consider ["C':point"]
         st "between E H C' /\ between A C' D" from [0;1;2;4;6;7]
         by [outer_pasch;BET_SYM])
    ;obviously (by_eqs o Di.split) qed from [0;1;2;3;6;7]] in
  MESON [lemma;g21]
    `!A B C D. between A B C /\ between B C D
     ==> between A B D /\ between A C D`;;


(* THEOREM 5 -- PART 2. Could we refactor using inner_pasch and outer_pasch? *)
let five2 =
  let lemma = 
    theorem
      "!A B C D. between A B C /\ between A C D ==> between B C D"
      [fix ["A:point";"B:point";"C:point";"D:point"]
      ;assume "between A B C" at [0]
      ;assume "between A C D" at [1]
      ;consider ["G:point"] st
        "~(?a. on_line A a /\ on_line B a /\ on_line G a)"
        at [2] from [0] by [g12;g13b;g21]
      ;obviously by_neqs
        (so consider ["Fa:point"] st "between B G Fa" at [3] by [g22])
      ;have ("~(?P. (?a. on_line C a /\ on_line Fa a /\ on_line P a)" ^
                "/\ between A P G)") at [4] proof
        [otherwise consider ["P:point"] st
            "(?a. on_line C a /\ on_line Fa a /\ on_line P a) /\ between A P G"
            at [4;5]
        ;clearly by_pasch
          (so consider ["Q:point"] st
             ("(?a. on_line C a /\ on_line P a /\ on_line Q a)" ^
                 "/\ (between A Q B \/ between B Q G)") from [0;2])
        ;obviously (by_eqs o Di.split) qed from [0;2;3;4;5] by [g21;g23]]
      ;obviously by_pasch
        (so consider ["H:point"] st
           "(?a. on_line C a /\ on_line Fa a /\ on_line H a) /\ between D H G"
           from [0;1;2;3] at [5;6])
      ;have "~(B = D)" at [7] from [0;1] by [g21;g23]
      ;clearly by_pasch
        (so consider ["C':point"] st
           ("(?a. on_line C' a /\ on_line Fa a /\ on_line H a)" ^
               "/\ (between B C' D \/ between B C' G)") from [0;1;2;3;5;6])
      ;obviously (by_eqs o Di.split) qed from [0;1;2;3;5;6;7] by [g21;g23]]
  in MESON [lemma;five1]
  `!A B C D. between A B C /\ between A C D
     ==> between A B D /\ between B C D`;;
