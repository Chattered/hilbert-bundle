(* ========================================================================= *)
(* Group I Theory                                                            *)
(*                                                                           *)
(*                                   Phil Scott                              *)
(*                                                                           *)
(*               Centre for Intelligent Systems and their Applications       *)
(*                             University of Edinburgh                       *)
(* ========================================================================= *)

(* The following three theorems formalise Hilbert's THEOREM 1. I have not
   formalised the final clause, since I feel that it is identical to I,6 up to
   suitable translations.  *)

module Id = Incidence_discovery(Di);;

let intersect_line = theorem
  ("!a b P Q. on_line P a /\ on_line P b /\ on_line Q a /\ on_line Q b
       ==> a = b \/ P = Q")
  [thus "thesis" by [g12]];;
  
let intersect_plane = theorem
  ("!'a 'b P. ~('a = 'b) /\ on_plane P 'a /\ on_plane P 'b
      ==> ?a. !Q. on_plane Q 'a /\ on_plane Q 'b <=> on_line Q a")
  [fix ["'a:plane";"'b:plane";"P:point"]
  ;assume "~('a = 'b) /\ on_plane P 'a /\ on_plane P 'b" at [1]
  ;so consider ["Q:point"] st "~(P = Q) /\ on_plane Q 'a /\ on_plane Q 'b"
     by [g17] at [2]
  ;so consider ["a:line"] st "on_line P a /\ on_line Q a" at [3] by [g11]
  ;take ["a"]
  ;fix ["R:point"]
  ;have "on_plane R 'a /\ on_plane R 'b ==> on_line R a"
     proof
     [assume "on_plane R 'a /\ on_plane R 'b" at [4]
     ;otherwise assume "~on_line R a" at [5]
     ;hence "!a. ~(on_line P a /\ on_line Q a /\ on_line R a)"
       from [2;3] by [g12]
     ;qed from [1;2;4] by [g15]]
  ;qed from [1;2;3] by [g16]];;

let point_line_plane =
  theorem ("!P a. ~on_line P a ==> 
            ?!'a. on_plane P 'a /\ !Q. on_line Q a ==> on_plane Q 'a")
    [fix ["P:point";"a:line"]
    ;assume "~on_line P a" at [0]
    ;consider ["X:point";"Y:point"] st "~(X = Y) /\ on_line X a  /\ on_line Y a"
      by [g13a] at [1]
    ;hence "!a. ~(on_line P a /\ on_line X a /\ on_line Y a)"
      from [0] by [g12] at [2]
    ;so consider ["'a:plane"] st "on_plane P 'a /\ on_plane X 'a /\ on_plane Y 'a"
      by [g14a] at [3]
    ;unfolding by [EXISTS_UNIQUE]
    ;take ["'a"]
    ;hence "!y. on_plane P y /\ (!Q. on_line Q a ==> on_plane Q y) ==> y = 'a"
      from [1;2] by [g15]
    ;qed from [1;2] from [3] by [g16]];;

let two_line_plane = theorem
  "!P a b. ~(a = b) /\ on_line P a /\ on_line P b
      ==> ?!'a. !P. on_line P a \/ on_line P b ==> on_plane P 'a"
  [fix ["P:point";"a:line";"b:line"]
  ;assume "~(a = b)" at [0]
  ;assume "on_line P a /\ on_line P b" at [1]
  ;so consider ["Q:point"] st "on_line Q a /\ ~(P = Q)"
     by [g13a] from [0;1] at [2]
  ;hence "~on_line Q b" from [0;1] by [g12] at [3]
  ;so consider ["'a:plane"]
     st "on_plane Q 'a /\ !R. on_line R b ==> on_plane R 'a"
     by [point_line_plane] at [4]
  ;unfolding by [EXISTS_UNIQUE]
  ;take ["'a:plane"]
  ;hence "!P. on_line P a \/ on_line P b ==> on_plane P 'a"
     from [1;2] by [g16]
  ;qed from [2;3;4] by [point_line_plane]];;

(* Some additional useful theorems. *)
let plane_three =
  theorem ("!'a. ?A B C. on_plane A 'a /\ on_plane B 'a /\ on_plane C 'a " ^
              "/\ !a. ~(on_line A a /\ on_line B a /\ on_line C a)")
    [fix ["'a:plane"]
    ;consider ["A:point"] at [0] st "on_plane A 'a" by [g14b]
    ;consider ["B:point"] at [1] st "~on_plane B 'a" by [g18]
    ;have "~(A:point = B)" at [2] from [0;1]
    ;so consider ["a:line"] at [3] st "on_line A a /\ on_line B a" by [g11]
    ;consider ["C:point"] at [4] st "~on_line C a" by [g13b]
    ;have "!b. ~(on_line A b /\ on_line B b /\ on_line C b)"
      proof
      [otherwise consider ["b:line"] at [5] st
          "on_line A b /\ on_line B b /\ on_line C b"
      ;hence "a = b" from [2;3] by [g12]
      ;qed from [4;5]]
    ;so consider ["'b:plane"] at [5] st
      "on_plane A 'b /\ on_plane B 'b /\ on_plane C 'b" by [g14a]
    ;consider ["D:point"] at [6] st "on_plane D 'a /\ on_plane D 'b /\ ~(A=D)"
      from [0;1;5] by [g17]
    ;consider ["E:point"] at [7] st "~on_plane E 'b" by [g18]
    ;have "!b. ~(on_line A b /\ on_line B b /\ on_line E b)" at [8]
      proof
      [otherwise consider ["b:line"] at [9] st
          "on_line A b /\ on_line B b /\ on_line E b"
      ;hence "on_plane E 'b" from [2;5] by [g16]
      ;qed from [7]]
    ;so consider ["'c:plane"] at [9] st
      "on_plane A 'c /\ on_plane B 'c /\ on_plane E 'c" by [g14a]
    ;assume "~('a = 'c)" from [8;9]
    ;so consider ["Fa:point"] at [10] st
      "on_plane Fa 'a /\ on_plane Fa 'c /\ ~(A=Fa)" from [0;9] by [g17]
    ;have "!b. ~(on_line A b /\ on_line D b /\ on_line Fa b)"
      proof
      [otherwise consider ["b:line"] at [11] st
          "on_line A b /\ on_line D b /\ on_line Fa b"
      ;hence "on_plane D 'c" at [12] from [0;9;10] by [g16]
      ;have "!c. ~(on_line A c /\ on_line B c /\ on_line D c)"
        proof
        [otherwise consider ["c:line"] at [13] st
            "on_line A c /\ on_line B c /\ on_line D c"
        ;hence "on_plane B 'a" from [0;6] by [g16]
        ;qed from [1]]
      ;hence "'b = 'c" from [5;6;9;12] by [g15]
      ;qed from [7;9]]
    ;qed from [0;6;10]];;

let triangle =
  prove (`!A B. ?C. ~(A = B)
         ==> ~(?a. on_line A a /\ on_line B a /\ on_line C a)`,
         MESON_TAC [g12;g13b]);;

let g11_weak =
  prove (`!A B. ?a. on_line A a /\ on_line B a`, 
         REPEAT GEN_TAC THEN ASM_CASES_TAC `A:point = B`
      THEN ASM_MESON_TAC [g11;g13a]);;

let g14a_weak_lemma =
  theorem "!A B. ?'a. on_plane A 'a /\ on_plane B 'a"
    [fix ["A:point";"B:point"]
    ;per cases
      [[suppose "A = B" at [0]
       ;consider ["a:line";"C:point"] st
         "~(A = C) /\ on_line A a /\ on_line C a" at [0]
         by [g11_weak;g13a] at [1]
       ;so consider ["P:point"] st
         "~(?a. on_line A a /\ on_line C a /\ on_line P a)" by [triangle]
       ;qed from [0;1] by [g14a;g16]]
      ;[suppose "~(A = B)" at [0]
       ;so consider ["P:point"] st
         "~(?a. on_line A a /\ on_line B a /\ on_line P a)" by [triangle]
       ;qed from [0] by [g14a;g16]]]];;

let by_planes b = (Id.inferred b).Id.planes

let g14a_weak =
  theorem "!A B C. ?'a. on_plane A 'a /\ on_plane B 'a /\ on_plane C 'a"
    [fix ["A:point";"B:point";"C:point"]
    ;assume "~(A = B) /\ ~(A = C) /\ ~(B = C)" at [0] by [g14a_weak_lemma]
    ;per cases
      [[suppose "?a. on_line A a /\ on_line B a /\ on_line C a"
       ;obviously by_planes qed]
      ;[suppose "~(?a. on_line A a /\ on_line B a /\ on_line C a)"
       ;obviously by_planes qed]]];;

let plane_triangle = theorem
  "!A B. ~(A = B) /\ on_plane A 'a /\ on_plane B 'a 
         ==> ?C. on_plane C 'a
                 /\ ~(?a. on_line A a /\ on_line B a /\ on_line C a)"
  [fix ["A:point";"B:point"]
  ;assume "~(A = B)" at [0]
  ;assume "on_plane A 'a /\ on_plane B 'a" at [1]
  ;consider ["a:line"] st "on_line A a /\ on_line B a" by [g11_weak] at [2]
  ;so consider ["C:point"] st "on_plane C 'a /\ ~on_line C a"
    by [g12;plane_three] from [0;1]
  ;qed from [0;2] by [g12]];;
