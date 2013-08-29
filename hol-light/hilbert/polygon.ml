(* ========================================================================= *)
(* Theory of polygonal segments and polygons.                                *)
(*                                                                           *)
(*                                   Phil Scott                              *)
(*                                                                           *)
(*               Centre for Intelligent Systems and their Applications       *)
(*                             University of Edinburgh                       *)
(* ========================================================================= *)

step_count := 0;;

let (|>) x f = f x;;

(* Polygonal segments are simply lists of their adjacent vertices.*)
new_type_abbrev("polyseg", `:point list`);;

(* The points of a polygonal segment are the vertices and all points in
   between adjacent vertices. .*)
let on_polyseg = new_definition
  `on_polyseg p P
   <=> MEM P p \/ ?x y. MEM (x,y) (ADJACENT p) /\ between x P y`;;

let on_polyseg_CONS2 = prove
  (`!P Q Ps X. on_polyseg (CONS P (CONS Q Ps)) X <=>
       P = X \/ on_polyseg (CONS Q Ps) X \/ between P X Q`,
   REWRITE_TAC [on_polyseg;MEM;PAIR_EQ;ADJACENT_CONS]
     THEN MESON_TAC []);;

let on_polyseg_CONS2' = prove
  (`!P Q Ps. on_polyseg (CONS P (CONS Q Ps)) R
            <=> on_polyseg [P;Q] R \/ on_polyseg (CONS Q Ps) R`,
   REWRITE_TAC [on_polyseg;ADJACENT_CONS;MEM
               ;ADJACENT;ZIP;BUTLAST;TAIL;NOT_CONS_NIL;MEM]
     THEN MESON_TAC []);;

let on_polyseg_CONS = prove
  (`on_polyseg Qs P ==> on_polyseg (CONS Q Qs) P`,
   ASM_CASES_TAC `Qs = []:point list`
      THENL [ASM_REWRITE_TAC
                [on_polyseg;MEM;ADJACENT;TAIL;BUTLAST
                ;ZIP;NOT_IN_EMPTY]
            ;MP_TAC (ISPECL [`Qs:point list`] list_CASES)
              THEN ASM_REWRITE_TAC []
              THEN DISCH_THEN
              (REPEAT_TCL CHOOSE_THEN
                 (fun thm -> SIMP_TAC [on_polyseg_CONS2;thm]))]);;

let on_polyseg_APPEND = prove
  (`!Ps Qs P. ~(Ps = []) /\ ~(Qs = [])
    ==> (on_polyseg (APPEND Ps Qs) P
         <=> on_polyseg Ps P \/ on_polyseg Qs P
             \/ between (LAST Ps) P (HD Qs))`,
   ASM_SIMP_TAC [on_polyseg;ADJACENT_APPEND;MEM_APPEND;MEM;PAIR_EQ]
     THEN MESON_TAC []);;

let on_polyseg_nil = prove
  (`!P. ~(on_polyseg [] P)`,
   REWRITE_TAC
  [on_polyseg;MEM;ADJACENT;ZIP;BUTLAST;TAIL]);;

let on_polyseg_sing = prove
  (`!P Q. on_polyseg [P] Q <=> P = Q`,
   REWRITE_TAC
  [on_polyseg;MEM;ADJACENT;ZIP;BUTLAST;TAIL
  ;NOT_CONS_NIL;EQ_SYM_EQ]);;

let on_polyseg_pair = prove
  (`!P Q R. on_polyseg [P;Q] R <=> P = R \/ Q = R \/ between P R Q`,
  REWRITE_TAC
  [on_polyseg;MEM;ADJACENT;ZIP;BUTLAST;TAIL
  ;NOT_CONS_NIL;EQ_SYM_EQ;NOT_IN_EMPTY;DISJ_ACI;PAIR_EQ]
    THEN MESON_TAC []);;

let on_polyseg_dup = prove
  (`!P Ps. on_polyseg (CONS P (CONS P Ps)) = on_polyseg (CONS P Ps)`,
   ONCE_REWRITE_TAC [GSYM (REWRITE_CONV [APPEND] `APPEND [P] (CONS Q Ps)`)]
     THEN SIMP_TAC [on_polyseg_APPEND;NOT_CONS_NIL;FUN_EQ_THM]
     THEN REWRITE_TAC [on_polyseg_sing;LAST;NOT_CONS_NIL;HD]
     THEN MESON_TAC [BET_NEQS;on_polyseg;MEM]);;

(* Two points are segment connected with respect to a figure and plane when
   they can be joined by a polygonal segment that does not meet the
   figure. Without the planes parameter, we cannot obtain transitivity, since
   it would be possible to have two planar polygonal segments whose union is
   non-planar. *)
let seg_connected = new_definition
  `seg_connected 'a figure P Q <=>
    ?path. ~(path = [])
           /\ (!P. MEM P path ==> on_plane P 'a)
           /\ HD path = P
           /\ LAST path = Q
           /\ DISJOINT (on_polyseg path) figure`;;

(* This is an equivalence relation. Virtually all of the reasoning here is
   based on properties of lists. *)
let seg_connected_refl = prove
  (`!'a figure P. on_plane P 'a /\ ~(figure P)
        ==> seg_connected 'a figure P P`,
   REPEAT STRIP_TAC THEN REWRITE_TAC [seg_connected;DISJOINT_IMP;IN]
     THEN EXISTS_TAC `[P:point]`
     THEN REWRITE_TAC
     [LENGTH;HD;LAST;on_polyseg;ADJACENT;ZIP;NOT_CONS_NIL;BUTLAST 
     ;TAIL;NOT_IN_EMPTY;FORALL_PAIRED_THM;MEM]
     THEN ASM_MESON_TAC []);;

let on_polyseg_REVERSE =
  prove (`!ps. on_polyseg (REVERSE ps) = on_polyseg ps`,
         REWRITE_TAC [on_polyseg;ADJACENT;BUTLAST_REVERSE
                     ;TAIL_REVERSE;EXTENSION;IN]
           THEN SIMP_TAC [GSYM ZIP_REVERSE;LENGTH_TAIL;BUTLAST_LENGTH]
           THEN REWRITE_TAC [MEM_REVERSE]
           THEN GEN_TAC
           THEN SUBGOAL_THEN `LENGTH (TAIL ps:point list)
                              = LENGTH (BUTLAST ps)`
                (ASSUME_TAC o MATCH_MP ZIP_SWAP)
           THENL [REWRITE_TAC [LENGTH_TAIL;BUTLAST_LENGTH]
                 ;ONCE_ASM_REWRITE_TAC []
                   THEN REWRITE_TAC [MEM_MAP;EXISTS_PAIR_THM;PAIR_EQ]
                   THEN MESON_TAC [BET_SYM]]);;

let seg_connected_sym =
  let lemma = prove
    (`!'a figure P Q.
        seg_connected 'a figure P Q ==> seg_connected 'a figure Q P`,
     REWRITE_TAC [seg_connected;DISJOINT_IMP;IN] 
       THEN REPEAT STRIP_TAC THEN EXISTS_TAC `REVERSE (path : point list)`
       THEN ASM_SIMP_TAC [REVERSE_EQ_NIL;HD_REVERSE;LAST_REVERSE
                         ;MEM_REVERSE;on_polyseg_REVERSE]) in
  prove
    (`!'a figure P Q.
        seg_connected 'a figure P Q <=> seg_connected 'a figure Q P`,
     MESON_TAC [lemma]);;

let seg_connected_trans = prove
  (`!'a figure P Q R.
      seg_connected 'a figure P Q /\ seg_connected 'a figure Q R
     ==> seg_connected 'a figure P R`,
   REWRITE_TAC [seg_connected;DISJOINT_IMP;IN]
     THEN REWRITE_TAC [on_polyseg;MEM]
     THEN REPEAT STRIP_TAC 
     THEN EXISTS_TAC `APPEND (path : polyseg) path'` THEN REPEAT CONJ_TAC
     THEN ASM_SIMP_TAC [APPEND_EQ_NIL;HD_APPEND;LAST_APPEND]
     THEN ASM_SIMP_TAC [ADJACENT_APPEND;MEM_APPEND;MEM;PAIR_EQ]
     THEN ASM_MESON_TAC [g21]);;

(* We define the interior of a triangle as the intersection of three
   half-planes. *)
let in_triangle = new_definition
  `in_triangle (A,B,C) P <=>
  ?hp hp' hp''. on_line A (line_of_half_plane hp)
             /\ on_line B (line_of_half_plane hp)
             /\ on_line A (line_of_half_plane hp')
             /\ on_line C (line_of_half_plane hp')
             /\ on_line B (line_of_half_plane hp'')
             /\ on_line C (line_of_half_plane hp'')
             /\ on_half_plane hp C
             /\ on_half_plane hp' B
             /\ on_half_plane hp'' A
             /\ on_half_plane hp P
             /\ on_half_plane hp' P
             /\ on_half_plane hp'' P`;;

(* The definition of half-planes forces the three points to be
   non-collinear. *)
let in_triangle_ncol = prove
  (`!A B C P. in_triangle (A,B,C) P ==>
      ~(?a. on_line A a /\ on_line B a /\ on_line C a)`,
   MESON_TAC [half_plane_not_on_line;g12;in_triangle]);;

(* The boundary of a triangle. *)
let on_triangle_def = new_definition
  `on_triangle (A,B,C) P <=> on_polyseg [A;B;C;A] P`;;

(* Unfolded definition of on_triangle. *)
let on_triangle = prove
  (`on_triangle (A,B,C) P <=>
      P = A \/ P = B \/ P = C
      \/ between A P B \/ between A P C \/ between B P C`,
   REWRITE_TAC [on_triangle_def;on_polyseg;NOT_CONS_NIL;ADJACENT
               ;MEM;ZIP;BUTLAST;TAIL;PAIR_EQ]
     THEN MESON_TAC [BET_SYM]);;

(* Convenient abbreviation for points outside the triangle. *)
let out_triangle = new_definition
  `out_triangle (A,B,C) P <=> ~in_triangle (A,B,C) P /\ ~on_triangle (A,B,C) P`;;

(* Complete rewrites for on in and out_triangle. *)
let tri_syms =
  let on_in = 
    [`on_triangle (A,B,C) P <=> on_triangle (A,C,B) P`
    ;`on_triangle (A,B,C) P <=> on_triangle (B,A,C) P`
    ;`in_triangle (A,B,C) P <=> in_triangle (A,C,B) P`
    ;`in_triangle (A,B,C) P <=> in_triangle (B,A,C) P`]
      |> map (MESON [BET_SYM;on_triangle;in_triangle])
  in (on_in
      @ ([`out_triangle (A,B,C) P <=> out_triangle (A,C,B) P`
         ;`out_triangle (A,B,C) P <=> out_triangle (B,A,C) P`]
            |> map (MESON (out_triangle::on_in)))
         |> end_itlist CONJ);;

(* In triangle ABC, there is a unique half-plane on the line AB containing
   C. *)
let unique_half_plane = prove
  (`!A B C. ~(?a. on_line A a /\ on_line B a /\ on_line C a)
      ==> ?!hp. on_line A (line_of_half_plane hp)
                /\ on_line B (line_of_half_plane hp)
                /\ on_half_plane hp C`,
   REPEAT GEN_TAC THEN DISCH_TAC
     THEN FIRST_ASSUM (CHOOSE_TAC o MATCH_MP
                         (REWRITE_RULE [GSYM NOT_EXISTS_THM] g14a))
     THEN discover_tac by_neqs (MAP_EVERY (CHOOSE_TAC o MATCH_MP g11))
     THEN SUBGOAL_THEN `!P. on_line P a ==> on_plane P 'a` ASSUME_TAC
     THENL [MATCH_MP_TAC
               (REWRITE_RULE [IMP_IMP;RIGHT_FORALL_IMP_THM] g16)
            THEN EXISTS_TAC `A:point` THEN EXISTS_TAC `B:point`
            THEN discover_tac by_neqs ASM_REWRITE_TAC
           ;ALL_TAC]
     THEN FIRST_ASSUM (REPEAT_TCL CHOOSE_THEN MP_TAC
                         o MATCH_MP half_plane_cover)
     THEN REWRITE_TAC [IMP_CONJ] THEN REPLICATE_TAC 3 DISCH_TAC
     THEN DISCH_THEN (MP_TAC o SPEC `C:point`) THEN DISCH_TAC
     THEN FULL_REWRITE_TAC [] THEN discover_tac by_neqs
       (fun thms -> ASM_MESON_TAC (on_half_plane_disjoint :: g12 :: thms)));;

(* The segment of two interior points of a triangle ABC does not meet the line
   AB. Used as a lemma for in_triangle_simple_connected. *)
let in_triangle_half_plane = theorem
  ("!A B C P Q a. in_triangle (A,B,C) P /\ in_triangle (A,B,C) Q
    /\ on_line A a /\ on_line B a 
    ==> ~(?R. on_line R a /\ between P R Q)")
  [fix ["A:point";"B:point";"C:point";"P:point";"Q:point";"a:line"]
  ;assume "~(?a. on_line A a /\ on_line B a /\ on_line C a)
           /\ in_triangle (A,B,C) P /\ in_triangle (A,B,C) Q
           /\ on_line A a /\ on_line B a" at [0;1;2;3;4] by [in_triangle_ncol]
  ;so consider ["hp:half_plane"] st
     "on_line A (line_of_half_plane hp)
      /\ on_line B (line_of_half_plane hp)
      /\ on_half_plane hp P
      /\ on_half_plane hp Q
      /\ on_half_plane hp C" from [1;2] by [in_triangle] at [5;6;7;8;9] 
     using (K (FIRST_ASSUM (MP_TAC o MATCH_MP unique_half_plane)))
  ;consider ["'a:plane"] st "on_plane A 'a /\ on_plane B 'a /\ on_plane C 'a"
     at [10;11;12] by [g14a] from [0]
  ;obviously by_neqs
     (assume "a = line_of_half_plane hp" at [13] from [0;3;4;5;6]) by [g12]
  ;obviously by_neqs
     (have "(!R. on_line R (line_of_half_plane hp) ==> on_plane R 'a)"
        from [0;3;4;10;11;13] by [g16])
  ;qed from [7;8;9;12] by [on_half_plane_not_bet;half_plane_on_plane]];;

(* The interior, exterior and boundary of a triangle are distinct. *)
let in_triangle_not_on_triangle = prove
  (`!A B C P. in_triangle (A,B,C) P ==> ~on_triangle (A,B,C) P`,
   REWRITE_TAC [in_triangle;on_triangle]
     THEN MESON_TAC [half_plane_not_on_line;g21;g12]);;

(* Any two interior points of a triangle are connected by a single segment
   (by definition of outside). *)
let in_triangle_single_connected = theorem
  "!A B C P Q. 
     in_triangle (A,B,C) P /\ in_triangle (A,B,C) Q
     ==> ~(?R. on_triangle (A,B,C) R /\ between P R Q)"
  [fix ["A:point";"B:point";"C:point";"P:point";"Q:point"]
  ;assume "~(?a. on_line A a /\ on_line B a /\ on_line C a)"
      at [0] by [in_triangle_ncol]
  ;assume "in_triangle (A,B,C) P" at [1]
  ;assume "in_triangle (A,B,C) Q" at [2]
  ;have "in_triangle (B,C,A) P /\ in_triangle (B,C,A) Q"
    from [1;2] by [in_triangle] at [3]
  ;have "in_triangle (A,C,B) P /\ in_triangle (A,C,B) Q"
    from [1;2] by [in_triangle]
  ;qed from [0;1;2;3] by [on_triangle;in_triangle_half_plane
                         ;g11_weak;g21]];;

(* Effectively says that a ray emerging from the line of a half-plane lies
   entirely in a half-plane, but unfolded in terms of betweenness. *)
let bet_on_half_plane = theorem
  "!hp P Q R. on_line P (line_of_half_plane hp)
      /\ on_half_plane hp Q
      /\ (between P Q R \/ between P R Q) ==> on_half_plane hp R"
  [fix ["hp:half_plane";"P:point";"Q:point";"R:point"]
  ;assume "on_line P (line_of_half_plane hp)" at [0]
  ;consider ["P':point"] st "~(P = P') /\ on_line P' (line_of_half_plane hp)"
    at [1] by [g13a]
  ;assume "on_half_plane hp Q" at [2]
  ;hence "~on_line Q (line_of_half_plane hp)"
    at [3] by [half_plane_not_on_line]
  ;assume "between P Q R \/ between P R Q" at [4]
  ;have "!X. ~(on_line X (line_of_half_plane hp)
               /\ between Q X R)" at [5] proof
    [fix ["X:point"]
    ;assume "on_line X (line_of_half_plane hp) /\ between Q X R"
    ;obviously (by_eqs o Di.split) qed from [0;1;3;4] by [BET_SYM;g23]]
  ;consider ["'a:plane"]
     st "on_plane Q 'a
         /\ !R. on_line R (line_of_half_plane hp) ==> on_plane R 'a"
     at [6;7] by [point_line_plane] from [3]
  ;hence "!R. on_half_plane hp R ==> on_plane R 'a"
     at [8] by [half_plane_on_plane] from [2;6;7]
  ;have "on_plane R 'a" at [9] from [0;4;5;6;7] by [g16;g21]
  ;obviously (by_ncols o Di.split)
    (have "~on_line R (line_of_half_plane hp)" from [0;1;3;4])
  ;qed by [on_half_plane_not_bet] from [2;5;8;9]];;      

(* The segment of two points in a half-plane lies in that half plane. *)
let bet_on_half_plane2 = theorem
  "!P Q R hp. on_half_plane hp P /\ on_half_plane hp R /\ between P Q R 
              ==> on_half_plane hp Q"
  [fix ["P:point";"Q:point";"R:point";"hp:half_plane"]
  ;assume "on_half_plane hp P /\ on_half_plane hp R" at [0;1]
  ;assume "between P Q R" at [2]
  ;have "~on_line P (line_of_half_plane hp)
         /\ ~on_line R (line_of_half_plane hp)"
    by [half_plane_not_on_line] from [0;1] at [3;4]
  ;so consider ["'a:plane"] st
    "on_plane P 'a /\ !X. on_line X (line_of_half_plane hp) ==> on_plane X 'a"
    by [point_line_plane] from [3] at [5;6]
  ;hence "!Q. on_half_plane hp Q ==> on_plane Q 'a" by [half_plane_on_plane]
    from [0;5;6] at [7]
  ;consider ["a:line"] st "on_line P a /\ on_line Q a /\ on_line R a" by [g21]
    from [2] at [8]
  ;hence "on_plane Q 'a /\ ~on_line Q (line_of_half_plane hp)" by
    [on_half_plane_not_bet;g16;BET_NEQS] from [0;1;2;7]
  ;so assume "?R. on_line R (line_of_half_plane hp) /\ between P R Q"
    from [0;7] by [on_half_plane_not_bet] using SIMP_TAC
  ;so consider ["S:point"] st
    "on_line S (line_of_half_plane hp) /\ between P S Q" at [9]
  ;hence "between P S R" using ORDER_TAC `{P:point,Q,R,S}` from [2;8]
  ;qed from [0;1;7;9] by [on_half_plane_not_bet]];;

(* Similar to inner_pasch, but cuts through an interior point rather than the
   side AC. *)
let tri_cut1 = theorem
  "!A B C P Q. in_triangle (A,B,C) P /\ between A B Q
     ==> ?X. between P X Q /\ between B X C"
  [fix ["A:point";"B:point";"C:point";"P:point";"Q:point"]
  ;assume "~(?a. on_line A a /\ on_line B a /\ on_line C a)"
     at [0] by [in_triangle_ncol]
  ;so consider ["'a:plane"]
    st "on_plane A 'a /\ on_plane B 'a /\ on_plane C 'a" at [1;2;3] by [g14a]
  ;assume "in_triangle (A,B,C) P"
  ;so consider ["hp:half_plane";"hq:half_plane";"hr:half_plane"]
     st ("on_line A (line_of_half_plane hp)
          /\ on_line B (line_of_half_plane hp)
          /\ on_line A (line_of_half_plane hq)
          /\ on_line C (line_of_half_plane hq)
          /\ on_line B (line_of_half_plane hr)            
          /\ on_line C (line_of_half_plane hr)
          /\ on_half_plane hp C
          /\ on_half_plane hq B
          /\ on_half_plane hr A
          /\ on_half_plane hp P
          /\ on_half_plane hq P
          /\ on_half_plane hr P")
     at [4;5;6;7;8;9;10;11;12;13;14;15] by [in_triangle]
  ;assume "between A B Q" at [16]
  ;obviously by_neqs
     (have "!X. on_half_plane hp X ==> on_plane X 'a"
        from [0;1;2;3;4;5;10] by [half_plane_on_plane;g16] at [17])
  ;obviously by_neqs
     (have "!X. on_half_plane hq X ==> on_plane X 'a"
        from [0;1;2;3;6;7;11] by [half_plane_on_plane;g16] at [18])
  ;obviously by_neqs
     (have "!X. on_half_plane hr X ==> on_plane X 'a"
        from [0;1;2;3;8;9;12] by [half_plane_on_plane;g16] at [19])
  ;obviously by_ncols
     (hence "on_plane Q 'a /\ ~on_line Q (line_of_half_plane hr)
             /\ ~on_half_plane hr Q"
        at [20;21;22] from [0;1;2;8;9;12;16] by [on_half_plane_not_bet;g16;g21])
  ;consider ["X:point"]
     st "on_line X (line_of_half_plane hr) /\ between P X Q"
     at [23] from [15;19;20;21;22] by [on_half_plane_not_bet]
  ;have "on_line Q (line_of_half_plane hp)" from [4;5;16] by [g21;g12]
  ;hence "on_half_plane hp X" by [bet_on_half_plane;BET_SYM] from [13;23] at [24]
  ;hence "~between C B X" at [25] from [5;10;17] by [on_half_plane_not_bet]
  ;have "on_half_plane hq Q" from [6;11;16] by [bet_on_half_plane]
  ;hence "on_half_plane hq X" from [14;23] by [bet_on_half_plane2]
  ;hence "~between B C X /\ ~(B = X) /\ ~(C = X)" from [5;7;11;18;24]
    by [on_half_plane_not_bet;half_plane_not_on_line]
  ;obviously by_neqs
       (qed from [0;8;9;23;25] by [four])];;

(* If a segment starts inside the triangle and does not cross the triangle
   boundary, then it ends inside the triangle. *)
let in_triangle_simple_closed =
  let lemma = MESON [tri_cut1;on_triangle]
    `!'a A B C P Q. in_triangle (A,B,C) P /\ between A B Q
       ==> (?R. between P R Q /\ on_triangle (A,B,C) R)` in
  let lemma = theorem
    "!'a A B C P Q hp. on_plane A 'a /\ on_plane B 'a /\ on_plane C 'a
       /\ on_line A (line_of_half_plane hp)
       /\ on_line B (line_of_half_plane hp)
       /\ on_half_plane hp C
       /\ in_triangle (A,B,C) P
       /\ on_plane Q 'a 
       /\ ~(on_triangle (A,B,C) Q)
       /\ ~(?R. on_triangle (A,B,C) R /\ between P R Q)
       ==> on_half_plane hp Q"
    [fix ["'a:plane";"A:point";"B:point";"C:point"
         ;"P:point";"Q:point";"hp:half_plane"]
    ;assume "~(?a. on_line A a /\ on_line B a /\ on_line C a)"
      at [0] by [in_triangle_ncol]
    ;assume "on_plane A 'a /\ on_plane B 'a /\ on_plane C 'a" at [1]
    ;assume ("on_line A (line_of_half_plane hp)" ^
             "/\ on_line B (line_of_half_plane hp)") at [2;3]
    ;assume "on_half_plane hp C" at [4]
    ;assume ("in_triangle (A,B,C) P" ^
             "/\ on_plane Q 'a" ^
             "/\ ~on_triangle (A,B,C) Q" ^
             "/\ ~(?R. on_triangle (A,B,C) R /\ between P R Q)") at [5;6;7;8]
    ;obviously by_neqs
      (have "!P. on_line P (line_of_half_plane hp) ==> on_plane P 'a"
         at [9] from [0;1;2;3] by [g16])
    ;consider ["hp':half_plane"] st
       "on_line A (line_of_half_plane hp')
        /\ on_line B (line_of_half_plane hp')
        /\ on_half_plane hp' C
        /\ on_half_plane hp' P" by [in_triangle] from [5]
    ;hence "on_half_plane hp P" at [10] by [unique_half_plane] from [0;2;3;4]
    ;hence "on_plane P 'a" at [11] from [1;4;9] by [half_plane_on_plane]
    ;have "~(?R. on_line R (line_of_half_plane hp) /\ between P R Q)"
       at [12] proof
       [otherwise consider ["R:point"] st
           "on_line R (line_of_half_plane hp) /\ between P R Q" at [12]
       ;per cases
         [[suppose "between A B R"
          ;so consider ["S:point"] st "between P S R /\ on_triangle (A,B,C) S" 
            using (K (MATCH_MP_TAC lemma)) at [13] from [0;5]
          ;hence "between P S Q" using ORDER_TAC `{P:point,Q,R,S}` from [12]
          ;qed from [8;13]]
         ;[suppose "between B A R"
          ;so consider ["S:point"] st "between P S R /\ on_triangle (B,A,C) S"
            by [in_triangle] using (K (MATCH_MP_TAC lemma))
            at [13] from [0;1;5]
          ;hence "between P S Q" using ORDER_TAC `{P:point,Q,R,S}` from [12]
          ;qed by [on_triangle;BET_SYM] from [8;13]]]
         by [on_triangle;four;g11_weak] from [0;2;3;8;12]]
    ;have "~(on_line Q (line_of_half_plane hp))" at [13] proof
      [otherwise assume "on_line Q (line_of_half_plane hp)" at [13]
      ;per cases
        [[suppose "between A B Q"
         ;so consider ["S:point"] st "between P S Q /\ on_triangle (A,B,C) S"
           using (K (MATCH_MP_TAC lemma)) from [0;1;5]
         ;qed from [8]]
        ;[suppose "between B A Q"
         ;so consider ["S:point"] st "between P S Q /\ on_triangle (B,A,C) S"
           using (K (MATCH_MP_TAC lemma)) at [14] from [0;1;5] by [in_triangle]
         ;qed by [on_triangle;BET_SYM] from [8]]]
        by [on_triangle;four;g11_weak] from [0;2;3;7;13]]
    ;have "!P. on_half_plane hp P ==> on_plane P 'a"
      from [9;10;11] by [half_plane_on_plane]
    ;qed from [6;10;12;13] by [on_half_plane_not_bet]] in
  prove
    (`!A B C P Q.
        on_plane A 'a /\ on_plane B 'a /\ on_plane C 'a
        /\ ~(?R. on_triangle (A,B,C) R /\ between P R Q)
        /\ on_plane Q 'a /\ ~on_triangle (A,B,C) Q
        ==> in_triangle (A,B,C) P
        ==> in_triangle (A,B,C) Q`,
     REPEAT GEN_TAC THEN DISCH_TAC THEN ASSUME_ANT
     THEN REWRITE_TAC [in_triangle]
     THEN DISCH_THEN (MAP_EVERY_TCL X_CHOOSE_THEN
                        [`hp:half_plane`;`hq:half_plane`;`hr:half_plane`]
                        ASSUME_TAC)
     THEN MAP_EVERY EXISTS_TAC
       [`hp:half_plane`;`hq:half_plane`;`hr:half_plane`]
     THEN ASM_REWRITE_TAC [] THEN CONJ_TAC
     THENL
       [MATCH_MP_TAC lemma THEN MAP_EVERY EXISTS_TAC
           [`'a:plane`;`A:point`;`B:point`;`C:point`;`P:point`]
           THEN ASM_REWRITE_TAC []
       ;ALL_TAC]
     THEN CONJ_TAC
     THENL [MATCH_MP_TAC lemma
               THEN MAP_EVERY EXISTS_TAC
               [`'a:plane`;`A:point`;`C:point`;`B:point`;`P:point`]
               THEN ASM_REWRITE_TAC []
               THEN ASM_MESON_TAC [in_triangle;on_triangle;BET_SYM]
           ;ALL_TAC]
     THEN MATCH_MP_TAC lemma THEN MAP_EVERY EXISTS_TAC
       [`'a:plane`;`B:point`;`C:point`;`A:point`;`P:point`]
     THEN ASM_REWRITE_TAC []
     THEN ASM_MESON_TAC [in_triangle;on_triangle;BET_SYM]);;

let with_subst x = Dim.plus (Di.subst x x) x;;
let by_incidence b = (Id.inferred b).Id.all;;

(* The segment between distinct sides of a triangle lies inside the
   triangle. *)
let in_triangle1 = theorem
  "!A B C X Y P.
     ~(?a. on_line A a /\ on_line B a /\ on_line C a)
     /\ between A X B /\ between A Y C /\ between X P Y
     ==> in_triangle (A,B,C) P"
  [fix ["A:point";"B:point";"C:point";"X:point";"Y:point";"P:point"]
  ;assume "~(?a. on_line A a /\ on_line B a /\ on_line C a)" at [0]
  ;assume "between A X B /\ between A Y C /\ between X P Y" at [1;2;3]
  ;consider ["hp:half_plane"]
     st "on_line A (line_of_half_plane hp)
         /\ on_line B (line_of_half_plane hp)
         /\ on_half_plane hp C" from [0] at [4;5;6] by [unique_half_plane]
  ;consider ["hq:half_plane"]
     st "on_line A (line_of_half_plane hq)
         /\ on_line C (line_of_half_plane hq)
         /\ on_half_plane hq B" from [0] at [7;8;9] by [unique_half_plane]
  ;so consider ["hr:half_plane"]
     st "on_line B (line_of_half_plane hr)
         /\ on_line C (line_of_half_plane hr)
         /\ on_half_plane hr A" from [0] at [10;11;12] by [unique_half_plane]
  ;have "on_half_plane hq X /\ on_half_plane hr X"
     at [13;14] from [1;7;9;10;12] by [bet_on_half_plane;BET_SYM]
  ;have "on_half_plane hp Y /\ on_half_plane hr Y"
     at [15;16] from [2;4;6;11;12] by [bet_on_half_plane;BET_SYM]
  ;have "on_line X (line_of_half_plane hp)
         /\ on_line Y (line_of_half_plane hq)"
    at [17;18] from [1;2;4;5;7;8] by [g12;g21]
  ;have "on_half_plane hp P /\ on_half_plane hq P /\ on_half_plane hr P"
     from [3;13;14;15;16;17;18] by [bet_on_half_plane2;bet_on_half_plane;BET_SYM]
  ;qed from [4;5;6;7;8;9;10;11;12] by [in_triangle]];;

(* The segment between a vertex and opposite side lies inside the triangle. *)
let in_triangle2 = theorem
  "!A B C X P.
     ~(?a. on_line A a /\ on_line B a /\ on_line C a)
     /\ between A X B /\ between C P X
     ==> in_triangle (A,B,C) P"
  [fix ["A:point";"B:point";"C:point";"X:point";"P:point"]
  ;assume "~(?a. on_line A a /\ on_line B a /\ on_line C a)" at [0]
  ;assume "between A X B /\ between C P X" at [1;2]
  ;consider ["hp:half_plane"]
     st "on_line A (line_of_half_plane hp) /\ on_line B (line_of_half_plane hp)
         /\ on_half_plane hp C" from [0] at [3;4;5] by [unique_half_plane]
  ;consider ["hq:half_plane"]
     st "on_line A (line_of_half_plane hq) /\ on_line C (line_of_half_plane hq)
         /\ on_half_plane hq B" from [0] at [6;7;8] by [unique_half_plane]
  ;so consider ["hr:half_plane"]
     st "on_line B (line_of_half_plane hr) /\ on_line C (line_of_half_plane hr)
         /\ on_half_plane hr A" from [0] at [9;10;11] by [unique_half_plane] 
  ;have "on_half_plane hq X /\ on_half_plane hr X"
     at [13;14] from [1;6;8;9;11] by [bet_on_half_plane;BET_SYM]
  ;have "on_line X (line_of_half_plane hp)" from [1;3;4] by [g12;g21]
  ;hence "on_half_plane hp P /\ on_half_plane hq P /\ on_half_plane hr P"
     from [2;5;7;10;13;14] by [bet_on_half_plane2;bet_on_half_plane;BET_SYM]
  ;qed from [3;4;5;6;7;8;9;10;11] by [in_triangle]];;

(* Add inferred incidence facts based on in_triangle. *)
let add_in_triangle =
  let in_triangle_ncols =
    let in_triangle_ncol2 = prove
      (`!A B C P. in_triangle (A,B,C) P
       ==> ~(?a. on_line A a /\ on_line B a /\ on_line P a)`,
       REWRITE_TAC [in_triangle]
         THEN MESON_TAC [g12;half_plane_not_on_line]) in
    let lemma = prove
      (`!A B C P. in_triangle (A,B,C) P
       ==> ~(?a. on_line A a /\ on_line B a /\ on_line P a)`,
       REWRITE_TAC [in_triangle]
         THEN MESON_TAC [g12;half_plane_not_on_line]) in
    let in_tri = ASSUME `in_triangle (A,B,C) P` in
    let syms = prove
      (`in_triangle (A,B,C) P
       ==> in_triangle (A,C,B) P /\ in_triangle (B,C,A) P`,
       MESON_TAC [in_triangle]) in
    UNDISCH syms 
    |> CONJUNCTS |> map (MATCH_MP in_triangle_ncol2)
    |> end_itlist CONJ
    |> CONJ (MATCH_MP in_triangle_ncol in_tri)
    |> CONJ (MATCH_MP lemma in_tri)
    |> REWRITE_RULE [CONJ_ACI]
    |> DISCH_ALL |> GEN_ALL in
  let in_triangle_on_plane = prove
  (`!A B C P. 
      on_plane A 'a /\ on_plane B 'a /\ on_plane C 'a
      /\ in_triangle (A,B,C) P
      ==> on_plane P 'a`,
   REPEAT GEN_TAC THEN DISCH_TAC
     THEN SUBGOAL_THEN `~(A:point=B)` ASSUME_TAC
     THENL [ASM_MESON_TAC [g11_weak;in_triangle_ncol]
           ;ASM_MESON_TAC [half_plane_on_plane;g16;in_triangle]]) in
  let all_on_plane = prove
    (`!A B C P. in_triangle (A,B,C) P
        ==> (?'a. on_plane A 'a /\ on_plane B 'a /\ on_plane C 'a
                  /\ on_plane P 'a)`,
     MESON_TAC [g14a_weak;in_triangle_on_plane]) in
  fun b ->
    [Id.unique (Di.rewrite [CONJ_ACI] (Di.rule1 all_on_plane b))
    ;Di.conjuncts (Di.rule1 in_triangle_ncols b)
    ;b] |> Id.Di_m.msum |> Di.rewrite [CONJ_ACI] |> Id.unique;;

(* A segment from inside the triangle to a side lies inside the triangle. *)
let on_triangle_bet_in_triangle =
  let lemma = theorem
    "!A B C P.
        (between A P B \/ A = P) /\ in_triangle (A,B,C) Q
        /\ between P R Q ==> in_triangle (A,B,C) R"
    [fix ["A:point";"B:point";"C:point";"P:point"]
    ;assume "in_triangle (A,B,C) Q" at [0]
    ;so consider ["hp:half_plane"]
      st "on_line A (line_of_half_plane hp)
           /\ on_line B (line_of_half_plane hp)
           /\ on_half_plane hp C
           /\ on_half_plane hp Q"
       by [in_triangle] at [1;2;3;4]
    ;consider ["hq:half_plane"]
       st "on_line A (line_of_half_plane hq)
           /\ on_line C (line_of_half_plane hq)
           /\ on_half_plane hq B
           /\ on_half_plane hq Q"
       from [0] by [in_triangle] at [5;6;7;8]
    ;consider ["hr:half_plane"]
      st "on_line B (line_of_half_plane hr)
           /\ on_line C (line_of_half_plane hr)
           /\ on_half_plane hr A
           /\ on_half_plane hr Q"
       from [0] by [in_triangle] at [9;10;11;12]
    ;assume "between P R Q" at [13]
    ;per cases
      [[suppose "between A P B" at [14]
       ;hence "on_half_plane hp R"
         from [1;2;4;13] by [g21;g12;bet_on_half_plane] at [15]
       ;have "on_half_plane hq P /\ on_half_plane hr P"
         from [5;7;9;11;14] by [bet_on_half_plane;BET_SYM]
       ;hence "on_half_plane hq R /\ on_half_plane hr R"
         from [8;12;13] by [bet_on_half_plane2]
       ;qed from [1;2;3;5;6;7;9;10;11;15] by [in_triangle]]
      ;[suppose "~between A P B" at [14]
       ;so assume "A = P" at [15]
       ;hence "on_half_plane hp R /\ on_half_plane hq R"
         at [16] from [1;4;5;8;13] by [bet_on_half_plane]
       ;have "on_half_plane hr R"
         from [11;12;13;15] by [bet_on_half_plane2]
       ;qed from [1;2;3;5;6;7;9;10;11;15;16] by [in_triangle]]]] in
  prove
    (`!A B C P Q R.
        on_triangle (A,B,C) P ==> in_triangle (A,B,C) Q /\ between P R Q
        ==> in_triangle (A,B,C) R`,
     REPEAT GEN_TAC THEN REWRITE_TAC [on_triangle]
       THEN STRIP_TAC
       THEN (REWRITE_RULE [TAUT `(P \/ Q ==> X) <=> (P ==> X) /\ (Q ==> X)`
                          ;IMP_CONJ;FORALL_AND_THM] lemma
                |> ONCE_REWRITE_RULE [EQ_SYM_EQ] |> CONJUNCTS
                |> MAP_EVERY (fun thm -> TRY (FIRST_MATCH MP_TAC thm)))
       THEN ASM_MESON_TAC [tri_syms]);;

(* If a segment starts inside the triangle and crosses an edge or vertex, then
   it ends outside the triangle. *)
let on_triangle_bet_out_triangle =
  let lemma = theorem
    "!A B C P.
          (between A P B \/ A = P) /\ in_triangle (A,B,C) Q
          /\ between Q P R ==> out_triangle (A,B,C) R"
    [fix ["A:point";"B:point";"C:point";"P:point"]
    ;assume "(between A P B \/ A = P) /\ in_triangle (A,B,C) Q
             /\ between Q P R" at [0;1;2] 
    ;so consider ["hp:half_plane"]
       st "on_line A (line_of_half_plane hp)
           /\ on_line B (line_of_half_plane hp)
           /\ on_half_plane hp C /\ on_half_plane hp Q"
       from [1] by [in_triangle] at [3;4;5;6]
    ;obviously (by_planes o add_in_triangle)
       (consider ["'a:plane"]
          st "on_plane A 'a /\ on_plane B 'a /\ on_plane C 'a" from [1])
    ;obviously (by_neqs o add_in_triangle)
       (hence "!P. on_half_plane hp P ==> on_plane P 'a"
          from [1;3;4;5] by [g16;half_plane_on_plane] at [7])
    ;obviously (by_neqs o add_in_triangle)
       (hence "on_line P (line_of_half_plane hp)"
          from [0;3;4] by [g12;g21])
    ;hence "~on_half_plane hp R"
       from [2;6;7] by [on_half_plane_not_bet;BET_SYM] at [8]
    ;obviously (by_incidence o with_subst o add_in_triangle o Di.split)
       (hence "~on_line R (line_of_half_plane hp)" from [0;1;2;3;4] at [9])
    ;have "~between A R C /\ ~between B R C" from [3;4;5;8] by
      [bet_on_half_plane] at [10]
    ;unfolding from [this] by [out_triangle;on_triangle]
    ;obviously (by_ncols o add_in_triangle)
       (have "~(?a. on_line A a /\ on_line B a /\ on_line C a)" from [1])
    ;hence "~in_triangle (A,B,C) R" by
      [in_triangle;in_triangle_ncol]
      using K (FIRST_ASSUM (MP_TAC o MATCH_MP unique_half_plane))
      from [1;3;4;5;8]
    ;qed from [3;4;5;8;9] by [g12;g21]] in
  prove
    (`!A B C P Q R.
        on_triangle (A,B,C) P ==> in_triangle (A,B,C) Q /\ between Q P R
        ==> out_triangle (A,B,C) R`,
     REPEAT GEN_TAC THEN REWRITE_TAC [on_triangle]
       THEN STRIP_TAC
       THEN (REWRITE_RULE [TAUT `(P \/ Q ==> X) <=> (P ==> X) /\ (Q ==> X)`
                          ;IMP_CONJ;FORALL_AND_THM] lemma
                |> ONCE_REWRITE_RULE [EQ_SYM_EQ] |> CONJUNCTS
                |> MAP_EVERY (fun thm -> TRY (FIRST_MATCH MP_TAC thm)))
       THEN ASM_MESON_TAC [tri_syms]);;

(* A lemma used to prove tri_cut3. If we prove the equivalence between Veblen's
   and our current definition of a triangle's interior, then this lemma should
   be easily derivable from tri_cut3. *)
let tri_cut2 = theorem
  "!A B C D E X.
     ~(?a. on_line A a /\ on_line B a /\ on_line C a)
     /\ between A D B /\ between A E C /\ between D X E
     ==> ?Y a. on_line A a /\ on_line X a /\ on_line Y a 
               /\ between B Y C"
  [fix ["A:point";"B:point";"C:point";"D:point";"E:point"
       ;"X:point"]
  ;assume ("~(?a. on_line A a /\ on_line B a /\ on_line C a)
            /\ between A D B /\ between A E C 
            /\ between D X E")
   at [0;1;2;3]
  ;consider ["Y:point"]
     st "(?a. on_line A a /\ on_line Y a /\ on_line X a)
          /\ between C Y D" at [4;5] proof
     [clearly by_pasch
         (consider ["Y:point"]
            st "(?a. on_line A a /\ on_line Y a /\ on_line X a)
                /\ (between C Y D \/ between C Y E)"
            from [0;1;2;3])
     ;obviously (by_eqs o Di.split)
       (qed from [0;1;2;3] by [BET_SYM;g23])]
  ;clearly by_pasch
     (consider ["Z:point"]
        st "(?a. on_line A a /\ on_line Z a /\ on_line Y a)
            /\ (between B Z C \/ between B Z D)"
        at [6;7] from [0;1;5])
  ;obviously (by_eqs o Di.split)
     (have "between B Z C" from [0;1;5;6;7] by [BET_SYM;g23])
  ;obviously by_cols qed from [0;1;4;5;6]];;

(* Drop a line from a vertex through an interior point of a triangle to the
   opposite side. *)
let tri_cut3 =
  let lemma = theorem
    "!A B C P a.
       in_triangle (A,B,C) P
       /\ between A X B
       /\ on_line C a /\ on_line P a /\ on_line X a
       ==> ?X. between B X C /\ between A P X"
    [fix ["A:point";"B:point";"C:point";"P:point";"a:line"]
    ;assume "in_triangle (A,B,C) P" at [0]
    ;hence "~(?a. on_line A a /\ on_line B a /\ on_line C a)"
      at [1] by [in_triangle_ncol]
    ;assume "between A X B" at [2]
    ;assume "on_line C a /\ on_line P a /\ on_line X a" at [3]
    ;consider ["hp:half_plane"]
       st ("on_line A (line_of_half_plane hp)" ^
           "/\ on_line B (line_of_half_plane hp)" ^
           "/\ on_half_plane hp C" ^
           "/\ on_half_plane hp P") at [4;5;6;7]
       from [0] by [in_triangle]
    ;consider ["hq:half_plane"]
       st ("on_line A (line_of_half_plane hq)" ^
           "/\ on_line C (line_of_half_plane hq)" ^
           "/\ on_half_plane hq B" ^
           "/\ on_half_plane hq P") at [8;9;10;11]
       from [0] by [in_triangle]
    ;obviously (by_planes o add_in_triangle)
       (consider ["'a:plane"]
          st "on_plane A 'a /\ on_plane B 'a /\ on_plane C 'a
              /\ on_plane P 'a /\ on_plane X 'a" from [0;2] at [12])
    ;have "on_line X (line_of_half_plane hp)"
       at [13] from [2;4;5] by [g12;g21]
    ;obviously by_neqs
       (have "!P. on_half_plane hp P ==> on_plane P 'a"
          at [14] from [1;4;5;6;12] by [g16;half_plane_on_plane])
    ;obviously by_neqs
       (have "!P. on_half_plane hq P ==> on_plane P 'a"
          at [15] from [1;8;9;10;12] by [g16;half_plane_on_plane])
    ;have "on_half_plane hq X" from [2;8;10] by [bet_on_half_plane]
    ;hence "~between P C X /\ ~between C X P"
       from [6;7;9;11;13;14;15] by [BET_SYM;on_half_plane_not_bet]
    ;obviously (by_neqs o add_in_triangle)
       (hence "between C P X" at [16] from [0;2;3] by [four;BET_SYM])
    ;consider ["Y:point"]
       st "(?a. on_line A a /\ on_line Y a /\ on_line P a)
            /\ between B Y C" at [17;18] proof
       [clearly (by_pasch o add_in_triangle)
         (so consider ["Y:point"]
            st "(?a. on_line A a /\ on_line Y a /\ on_line P a)
                /\ (between B Y C \/ between B Y X)"
            from [0;2;3;16])
       ;obviously (by_eqs o Di.split o add_in_triangle)
         qed from [0;2] by [BET_SYM;g23]]
    ;have "between A P Y" proof
      [clearly (by_pasch o add_in_triangle)
          (consider ["Z:point"]
             st "(?a. on_line Z a /\ on_line P a /\ on_line X a)
                 /\ (between A Z Y \/ between B Z Y)"
             from [0;2;16;17;18])
      ;obviously (by_eqs o Di.split o add_in_triangle)
         qed from [0;3;16;17;18] by [BET_SYM;g23]]
    ;qed from [18]] in
  theorem
    "!A B C P. in_triangle (A,B,C) P
             ==> ?X. between B X C /\ between A P X"
    [fix ["A:point";"B:point";"C:point";"P:point"]
    ;assume "in_triangle (A,B,C) P" at [0]
    ;hence "~(?a. on_line A a /\ on_line B a /\ on_line C a)"
       at [1] by [in_triangle_ncol]
    ;so consider ["X:point"] st "between A X B" at [2]
       by [in_triangle_ncol;three;g11_weak]
    ;so assume "~(?a. on_line C a /\ on_line P a /\ on_line X a)"
       by [lemma] from [0;1] at [3]
    ;clearly (by_pasch o add_in_triangle)
       (consider ["Y:point"]
          st "(?a. on_line Y a /\ on_line P a /\ on_line X a)
                /\ (between A Y C \/ between B Y C)"
          at [4;5] from [0;2;3])
    ;hence "~between P X Y /\ ~between P Y X"
      by [on_triangle_bet_in_triangle;on_triangle;
          in_triangle_not_on_triangle;BET_SYM]
      from [0;2]
    ;obviously (by_neqs o add_in_triangle o Di.split)
       (hence "between X P Y"
          at [6] from [0;2;3;4;5] by [four])
    ;per cases
      [[suppose "between B Y C" at [7]
       ;clearly (by_pasch o add_in_triangle)
         (so consider ["Z:point"]
            st "(?a. on_line A a /\ on_line Z a /\ on_line P a)
                 /\ (between B Z X \/ between B Z Y)"
            at [8] from [0;2;4;6])
       ;obviously (by_eqs o add_in_triangle o Di.split)
           (hence "between B Z Y"
              at [9] from [0;2] by [BET_SYM;g23])
       ;hence "between B Z C"
         at [10] from [7] using ORDER_TAC `{B:point,C,Y,Z}`
       ;hence "~between A Z P /\ ~between P A Z"
         by [on_triangle_bet_in_triangle;on_triangle;
             in_triangle_not_on_triangle;BET_SYM]
         from [0]
       ;obviously (by_neqs o add_in_triangle)
         (qed from [0;8;10] by [four])]
      ;[suppose "between A Y C" at [7]
       ;so consider ["Z:point";"a:line"]
         st "on_line A a /\ on_line P a /\ on_line Z a
             /\ between B Z C"
         at [8] from [0;2;6;7] by [in_triangle_ncol]
         using K (MATCH_MP_TAC tri_cut2)
       ;hence "~between P A Z /\ ~between A Z P"
         from [0] by [on_triangle_bet_in_triangle;on_triangle;
                      in_triangle_not_on_triangle;BET_SYM]
       ;obviously (by_neqs o add_in_triangle o Di.conjuncts)
         (qed from [0;8] by [BET_SYM;four])]]
      from [5]];;

(* Similar to in_triangle1, but considers the extension of XY outside the
   triangle. *)
let out_triangle1 = theorem
  "!A B C X Y P.
         ~(?a. on_line A a /\ on_line B a /\ on_line C a)
         /\ between A X B
         /\ between A Y C
         /\ between X Y P
         ==> out_triangle (A,B,C) P"
  [fix ["A:point";"B:point";"C:point";"X:point";"Y:point";"P:point"];
   assume "~(?a. on_line A a /\ on_line B a /\ on_line C a)" at [0];
   assume "between A X B" at [1];
   assume "between A Y C" at [2];
   assume "between X Y P" at [3];
   so consider ["Z:point"] st "between X Z Y" at [4] by [three;BET_NEQS];
   hence "in_triangle (A,B,C) Z" at [5] by [in_triangle1] from [0;1;2;4];
   have "between Z Y P" from [3;4] using ORDER_TAC `{P:point,X,Y,Z}`;
   qed from [1;2;5] by [on_triangle;on_triangle_bet_out_triangle]];;

(* The next block of definitions and lemmas are needed to prove
   intersect_polyseg_closed. *)

(* A crossing against triangle (A,B,C) is the number of times that the segment
   PQ moves us from inside the triangle to outside (or vice-versa) by
   intersecting the edge AB. This is not a local property, so we carry around
   "was_inside" as context. *)

let crossing = new_definition
  `crossing (A,B,C) was_inside P Q =
    if between A P B /\ between A Q B then 0
    else if (?R. between P R Q /\ between A R B) then 1
    else if between A P B
            /\ ((?R. between P R Q /\ in_triangle (A,B,C) R)
                <=> ~was_inside) then 1
    else 0`;;

(* Update the context. *)
let new_was_inside = new_definition 
  `new_was_inside (A,B,C) was_inside P Q =
    if on_triangle (A,B,C) Q then
      if ?R. between P R Q /\ in_triangle (A,B,C) R then T
      else if on_triangle (A,B,C) P then was_inside
      else F
    else in_triangle (A,B,C) Q`;;

(* Should have used this. *)
g `new_was_inside (A,B,C) was_inside P Q <=>
    in_triangle (A,B,C) Q
    \/ (on_triangle (A,B,C) Q /\ 
          ((?R. between P R Q /\ in_triangle (A,B,C) R)
              \/ on_triangle (A,B,C) P /\ was_inside))`;;
e (REWRITE_TAC [new_was_inside] THEN EQ_TAC THEN REPEAT COND_CASES_TAC
     THEN FULL_REWRITE_TAC []
     THEN ASM_MESON_TAC [in_triangle_not_on_triangle]);;

(* This is provable. *)
(* |- new_was_inside (A,B,C) was_inside P Q <=> *)
(*    (if on_triangle (A,B,C) Q *)
(*     then (?R. between P R Q /\ in_triangle (A,B,C) R) \/ *)
(*          on_triangle (A,B,C) P /\ was_inside *)
(*     else in_triangle (A,B,C) Q) *)

(* A crossing is 0 or 1. *)
let crossing_lt_2 = prove
  (`!A B C X P Q. crossing (A,B,C) X P Q < 2`,
   REWRITE_TAC [crossing] THEN ARITH_TAC);;

let unfold_crossing_tac =
  REWRITE_TAC [crossing]
    THEN CONV_TAC (TOP_SWEEP_CONV (REWR_CONV COND_RAND))
    THEN CONV_TAC (TOP_SWEEP_CONV (REWR_CONV COND_RATOR))
    THEN REWRITE_TAC [ARITH_RULE `~(1=0)`;tri_syms];;

(* The sum of crossings against all sides of the triangle is less than or
   equal to 2. *)
let crossing_sum_le_2 =
  let lemma = theorem
    "~(?a. on_line A a /\ on_line B a /\ on_line C a)
     /\ crossing (A,B,C) X P Q = 1
     /\ crossing (A,C,B) X P Q = 1
     ==> crossing (B,C,A) X P Q = 0"
    [assume "~(?a. on_line A a /\ on_line B a /\ on_line C a)" at [0]
    ;tactics [unfold_crossing_tac]
    ;assume "between A P B \/ ?R. between P R Q /\ between A R B"
    ;so consider ["R:point"]
      st "between A R B 
           /\ ?a. on_line P a /\ on_line Q a /\ on_line R a"
      by [g11_weak;g21] at [1]
    ;assume "between A P C \/ ?R. between P R Q /\ between A R C"
    ;so consider ["S:point"]
       st "between A S C
           /\ ?a. on_line P a /\ on_line Q a /\ on_line S a"
       by [g11_weak;g21] at [2]
    ;assume "~(P=Q)" by [BET_NEQS]
    ;obviously (by_cols o Di.conjuncts) (hence "~between B P C" from [0;1;2])
       by [supplement1] at [3]
    ;have "~(?R. between P R Q /\ between B R C)" proof
       [otherwise assume "?R. between P R Q /\ between B R C"
       ;so consider ["U:point"] st "between P U Q /\ between B U C"
       ;obviously (by_cols o Di.conjuncts) qed from [0;1;2]
         by [supplement1]]
    ;qed from [3]] in
  prove (`!A B C X P Q. ~(?a. on_line A a /\ on_line B a /\ on_line C a)
          ==> crossing (A,B,C) X P Q
              + crossing (A,C,B) X P Q
              + crossing (B,C,A) X P Q <= 2`,
         REPEAT GEN_TAC THEN DISCH_TAC
           THEN MATCH_MP_TAC (ARITH_RULE
          `x < 2 /\ y < 2 /\ z < 2 /\ (x = 1 /\ y = 1 ==> z = 0)
             ==> x + y + z <= 2`)
           THEN ASM_MESON_TAC [crossing_lt_2;lemma]);;

let crossing_sym = prove
  (`!A B C was_inside P Q.
      crossing (B,A,C) was_inside P Q = crossing (A,B,C) was_inside P Q`,
   REWRITE_TAC [crossing;BET_SYM;tri_syms]);;

(* Crossings of a segment PQ which does not intersect a vertex sum to 1
   precisely when we move from inside to outside or vice-versa. We have to
   factor the context into this theorem. *)
let cross_1_not_on =
  let part1 = theorem
    "!'a A B C was_inside P Q.
         crossing (A,B,C) was_inside P Q = 1
         ==> crossing (A,C,B) was_inside P Q = 0
         ==> crossing (B,C,A) was_inside P Q = 0
         ==> on_plane A 'a /\ on_plane B 'a /\ on_plane C 'a
             /\ on_plane P 'a /\ on_plane Q 'a
             /\ ~(?a. on_line A a /\ on_line B a /\ on_line C a)
             /\ ~on_polyseg [P;Q] A /\ ~on_polyseg [P;Q] B /\ ~on_polyseg [P;Q] C
             /\ ~on_triangle (A,B,C) Q
             ==> (in_triangle (A,B,C) P \/ on_triangle (A,B,C) P /\ was_inside
                  <=> ~(in_triangle (A,B,C) Q))"
    [fix ["'a:plane";"A:point";"B:point";"C:point"
         ;"was_inside:bool";"P:point";"Q:point"]
    ;assume "on_plane A 'a /\ on_plane B 'a /\ on_plane C 'a
             /\ on_plane P 'a /\ on_plane Q 'a" at [0]
    ;assume "~(?a. on_line A a /\ on_line B a /\ on_line C a)" at [1]
    ;assume "~on_polyseg [P; Q] A /\ ~on_polyseg [P; Q] B
             /\ ~on_polyseg [P; Q] C" at [2]
    ;tactics [unfold_crossing_tac]
    ;per cases
      [[suppose "?R. between P R Q /\ between A R B"
       ;so consider ["R:point"] st "between P R Q /\ between A R B" at [3]
       ;per cases 
         [[suppose "in_triangle (A,B,C) P" at [4]
          ;hence "out_triangle (A,B,C) Q" from [3]
            by [on_triangle;on_triangle_bet_out_triangle]
          ;qed by [out_triangle] from [4] using K (DISCH_THEN (K ALL_TAC))]
         ;[suppose "out_triangle (A,B,C) P" at [4]
          ;per cases
            [[suppose "?a. on_line C a /\ on_line P a /\ on_line R a" at [5]
             ;have "~between C P R" at [6] from [1;3;4]
               by [in_triangle2;out_triangle]
             ;obviously (by_neqs o Id.conjuncts)
               (have "~(C = R)" at [7] from [1;3])
             ;have "~(C = P) /\ ~(C = Q) /\ ~between P C Q"
               from [2] by [on_polyseg_pair;on_triangle]
             ;hence "between R Q C" from [3;5;6;7]
               using ORDER_TAC `{C:point,P,Q,R}`
             ;hence "in_triangle (A,B,C) Q"
               from [1;3] by [in_triangle2;BET_SYM]
             ;qed from [4] by [out_triangle]
               using K (DISCH_THEN (K ALL_TAC))]
            ;[suppose "~(?a. on_line C a /\ on_line P a /\ on_line R a)"
                 at [5]
             ;have "~(?a. on_line A a /\ on_line P a /\ on_line Q a)"
               at [6] proof
               [otherwise
                   assume "?a. on_line A a /\ on_line P a /\ on_line Q a"
                   at [6]
               ;have "~(A=P) /\ ~(A=Q) /\ ~(B=P) /\ ~(B=Q)
                      /\ ~between P A Q /\ ~between P B Q
                      /\ ~(between A P B)"
                 from [2;4] by [on_triangle;on_polyseg_pair;out_triangle]
             ;qed from [3;6] using ORDER_TAC `{A:point,B,P,Q,R}`]
             ;have "~(?a. on_line B a /\ on_line P a /\ on_line Q a)" at [7]
               proof
               [otherwise
                   assume "?a. on_line B a /\ on_line P a /\ on_line Q a"
                   at [6]
               ;have "~(A=P) /\ ~(A=Q) /\ ~(B=P) /\ ~(B=Q)
                      /\ ~between P A Q /\ ~between P B Q
                      /\ ~(between A P B)"
                 from [2;4] by [on_triangle;on_polyseg_pair;out_triangle]
               ;qed from [3;6] using ORDER_TAC `{A:point,B,P,Q,R}`]
             ;clearly (by_pasch o Di.conjuncts)
               (so consider ["S:point"] st
                  "(?a. on_line S a /\ on_line P a /\ on_line R a)
                   /\ (between A S C \/ between B S C)"
                  from [0;1;3;5] at [8;9])
             ;have "~between A P C /\ ~between B P C"
               from [4] by [out_triangle;on_triangle]
             ;so assume "~(?R. between P R Q /\ between A R C)
                         /\ ~(?R. between P R Q /\ between B R C)"
             ;hence "~between P S Q" at [10] from [9]
             ;assume "~on_triangle (A,B,C) Q"
             ;hence "~(P = S) /\ ~(Q = S)" 
               from [4;9] by [out_triangle;on_triangle] at [11]
             ;have "~between R P S" proof
               [otherwise assume "between R P S"
               ;hence "in_triangle (A,B,C) P" from [1;3;9]
                 by [in_triangle1;BET_SYM;tri_syms]
               ;qed by [out_triangle] from [4]]
             ;hence "between R Q S" from [3;8;9;10;11]
               using ORDER_TAC `{P:point,R,Q,S}`
             ;hence "in_triangle (A,B,C) Q" by [in_triangle1;BET_SYM;tri_syms]
               from [1;3;9]
             ;qed from [4] by [out_triangle]
               using K (DISCH_THEN (K ALL_TAC))]]]
         ;[suppose "on_triangle (A,B,C) P" at [4]
          ;per cases 
            [[suppose "between A P B" at [5]
             ;have "~between P A Q /\ ~between P B Q /\ ~(A = Q) /\ ~(B = Q)"
               from [2] by [on_polyseg_pair;on_triangle;BET_SYM]
             ;hence "between A Q B" using ORDER_TAC `{A:point,B,P,Q,R}`
               from [3;5]
             ;qed by [on_triangle]]
            ;[suppose "between A P C \/ between B P C" at [5]
             ;hence "out_triangle (A,B,C) Q"
               by [out_triangle1;BET_SYM;tri_syms]
               at [6] from [1;3;5]
             ;hence "~between A Q C /\ ~between B Q C"
               at [7] by [on_triangle;out_triangle]
             ;have "?R. between P R Q /\ in_triangle (A,B,C) R" proof
               [consider ["X:point"] st "between P X R" at [8]
                   from [3] by [BET_NEQS;three]
               ;hence "between P X Q" using ORDER_TAC `{P:point,Q,R,X}`
                 at [9] from [3]
               ;hence "in_triangle (A,B,C) X" by [in_triangle1] from [1;3;5;8]
                 by [tri_syms;BET_SYM;in_triangle1]
               ;qed from [9]]
             ;so assume "was_inside" from [5;7]
             ;qed from [4;6] by [out_triangle]
               using K (DISCH_THEN (K ALL_TAC))]]
            by [on_triangle;on_polyseg_pair] from [2;4]]]
         by [out_triangle]]
      ;[suppose "~(?R. between P R Q /\ between A R B)" at [3]
       ;so assume "between A P B" at [4]
       ;per cases
         [[suppose "?R. between P R Q /\ in_triangle (A,B,C) R"
          ;so consider ["R:point"]
            st "between P R Q /\ in_triangle (A,B,C) R" at [5]
          ;have "~between A P C /\ ~between B P C" at [6] proof
            [otherwise assume "between A P C \/ between B P C"
            ;obviously (by_cols o Di.split) (qed from [1;4])]
          ;so assume "~(?R. between P R Q /\ between A R C)
                  /\ ~(?R. between P R Q /\ between B R C)" at [7]
          ;assume "~between A Q B" at [8]
          ;assume "~on_triangle (A,B,C) Q"
          ;have "in_triangle (A,B,C) Q" proof
            [otherwise assume "out_triangle (A,B,C) Q"
                from [this] by [out_triangle]
            ;so consider ["S:point"] st
              "between R S Q /\ on_triangle (A,B,C) S"
              at [9;10] from [0;5]
              by [in_triangle_simple_closed;out_triangle]
            ;have "between P S Q" at [11] from [5;9] using
              ORDER_TAC `{P:point,Q,R,S}`
            ;have "~between A S B" proof
              [otherwise assume "between A S B" at [12] by [on_polyseg_pair]
              ;have "~between P A Q /\ ~between P B Q" from [2]
                by [on_polyseg_pair;on_triangle]
              ;hence "A = Q \/ B = Q" from [4;8;11;12]
                using ORDER_TAC `{A:point,B,P,Q}`
              ;qed by [on_triangle;on_polyseg_pair] from [2]]
            ;hence "between A S C \/ between B S C"
              by [on_triangle;on_polyseg_pair;BET_SYM] from [2;10;11]
            ;qed from [7;11]]
          ;unfolding from [this;3;6]
          ;qed from [4;5] by [on_triangle;in_triangle_not_on_triangle]]
         ;[suppose "~(?R. between P R Q /\ in_triangle (A,B,C) R)" at [5]
          ;otherwise assume "in_triangle (A,B,C) Q" at [6]
            from [this;3;4] by [on_triangle]
          ;so consider ["R:point"] st "between P R Q"
            from [4;5] by [on_triangle;in_triangle_not_on_triangle;three]
          ;qed from [4;5;6]
            by [on_triangle_bet_in_triangle;on_triangle]]]]]] in
  let lemma1 = theorem
    "!'a A B C was_inside P Q.
       between A P B 
       ==> on_plane A 'a /\ on_plane B 'a /\ on_plane C 'a
           /\ on_plane P 'a /\ on_plane Q 'a
           /\ ~on_polyseg [P;Q] A /\ ~on_polyseg [P;Q] B /\ ~on_polyseg [P;Q] C 
           /\ crossing (A,B,C) was_inside P Q = 0
           /\ crossing (A,C,B) was_inside P Q = 0
           /\ crossing (B,C,A) was_inside P Q = 0
           /\ ~on_triangle (A,B,C) Q
           ==> (in_triangle (A,B,C) P \/ on_triangle (A,B,C) P /\ was_inside
                <=> in_triangle (A,B,C) Q)"
    [fix ["'a:plane";"A:point";"B:point";"C:point";"was_inside:bool"
         ;"P:point";"Q:point"]
    ;assume "on_plane A 'a /\ on_plane B 'a /\ on_plane C 'a
             /\ on_plane P 'a /\ on_plane Q 'a" at [0]
    ;assume "~on_polyseg [P; Q] A /\ ~on_polyseg [P; Q] B \
             /\ ~on_polyseg [P; Q] C" at [2]
    ;tactics [unfold_crossing_tac]
    ;assume "between A P B" at [3]
    ;assume "~on_triangle (A,B,C) Q" at [4]
    ;hence "~between A Q B /\ ~between A Q C /\ ~between B Q C"
      by [on_triangle] at [5]
    ;so assume "~(?R. between P R Q
                 /\ (between A R B \/ between A R C \/ between B R C))"
    ;hence "~(?R. between P R Q /\ on_triangle (A,B,C) R)"
      at [6] from [2] by [on_polyseg_pair;on_triangle]
    ;per cases
      [[suppose "?R. between P R Q /\ in_triangle (A,B,C) R" at [7]
       ;so consider ["R:point"] st "between P R Q /\ in_triangle (A,B,C) R"
         at [8]
       ;have "~(?S. between R S Q /\ on_triangle (A,B,C) S)" proof
         [otherwise assume "?S. between R S Q /\ on_triangle (A,B,C) S"
         ;so consider ["S:point"] st "between R S Q /\ on_triangle (A,B,C) S"
           at [9]
         ;hence "between P S Q" from [8] using ORDER_TAC `{P:point,Q,R,S}`
         ;qed from [6;9]]
       ;hence "in_triangle (A,B,C) Q" from [0;4;8]
         by [in_triangle_simple_closed]
       ;qed from [3;5;7] by [on_triangle]]
      ;[suppose "~(?R. between P R Q /\ in_triangle (A,B,C) R)" at [7]
       ;hence "~in_triangle (A,B,C) Q" from [3]
         by [on_triangle_bet_in_triangle;on_triangle;three
            ;in_triangle_not_on_triangle]
       ;qed from [3;5;7] by [in_triangle_not_on_triangle;on_triangle]]]] in
  let part2 = theorem
    "!'a A B C was_inside P Q.
     crossing (A,B,C) was_inside P Q = 0
     ==> crossing (A,C,B) was_inside P Q = 0
     ==> crossing (B,C,A) was_inside P Q = 0\
     ==> on_plane A 'a /\ on_plane B 'a /\ on_plane C 'a
         /\ on_plane P 'a /\ on_plane Q 'a
         /\ ~(?a. on_line A a /\ on_line B a /\ on_line C a)
         /\ ~on_polyseg [P;Q] A /\ ~on_polyseg [P;Q] B /\ ~on_polyseg [P;Q] C
         /\ ~on_triangle (A,B,C) Q
         ==> (in_triangle (A,B,C) P \/ on_triangle (A,B,C) P /\ was_inside
              <=> in_triangle (A,B,C) Q)"
    [fix ["'a:plane";"A:point";"B:point";"C:point"
         ;"was_inside:bool";"P:point";"Q:point"]
    ;assume "on_plane A 'a /\ on_plane B 'a /\ on_plane C 'a
             /\ on_plane P 'a /\ on_plane Q 'a" at [0]
    ;assume "~(?a. on_line A a /\ on_line B a /\ on_line C a)" at [1]
    ;assume "~on_polyseg [P; Q] A /\ ~on_polyseg [P; Q] B
             /\ ~on_polyseg [P; Q] C" at [2]
    ;assume "~on_triangle (A,B,C) Q" at [3]
    ;per cases
      [[suppose "between A P B"
       ;qed from [0;1;2;3] by [lemma1]]
      ;[suppose "between A P C"
       ;tactics [POP_ASSUM (ASSUME_TAC o SPECL [`'a:plane`;`B:point`]
                              o MATCH_MP lemma1)]
       ;qed from [0;1;2;3] using (MESON_TAC o mutual_rewrite)
         by [tri_syms;crossing_sym]]
      ;[suppose "between B P C"
       ;tactics [POP_ASSUM (ASSUME_TAC o SPECL [`'a:plane`;`A:point`]
                              o MATCH_MP lemma1)]
       ;qed from [0;1;2;3] using (MESON_TAC o mutual_rewrite)
         by [tri_syms;crossing_sym]]
      ;[suppose "~on_triangle (A,B,C) P" at [4]
       ;tactics [unfold_crossing_tac]
       ;have "~between A Q B /\ ~between A Q C /\ ~between B Q C"
         from [3] by [on_triangle]
       ;so assume "~(?R. between P R Q
                   /\ (between A R B \/ between A R C \/ between B R C))"
       ;hence "~(?R. between P R Q /\ on_triangle (A,B,C) R)"
         at [5] from [2] by [on_polyseg_pair;on_triangle]
       ;hence "in_triangle (A,B,C) P <=> in_triangle (A,B,C) Q"
         from [0;3;4] by [in_triangle_simple_closed;BET_SYM]
       ;qed from [4] using K (DISCH_THEN (K ALL_TAC))]]
      from [2] by [on_polyseg_pair;on_triangle]] in
  let lemma2 = theorem
    "!A B C was_inside P Q.
       (?R. between P R Q /\ between A R C)
       ==> ~(?a. on_line A a /\ on_line B a /\ on_line C a)
           /\ crossing (A,B,C) was_inside P Q = 0
           /\ crossing (A,C,B) was_inside P Q = 1
           /\ crossing (B,C,A) was_inside P Q = 1
           ==> (in_triangle (A,B,C) P \/ on_triangle (A,B,C) P /\ was_inside
                <=> in_triangle (A,B,C) Q)"
    [fix ["A:point";"B:point";"C:point";"was_inside:bool";"P:point";"Q:point"]
    ;assume "~(?a. on_line A a /\ on_line B a /\ on_line C a)" at [0]
    ;tactics [unfold_crossing_tac]
    ;assume "?R. between P R Q /\ between A R C"
    ;so consider ["R:point"] st "between P R Q /\ between A R C" at [1]
    ;per cases
      [[suppose "?S. between P S Q /\ between B S C"
       ;so consider ["S:point"] st "between P S Q /\ between B S C" at [2]
       ;obviously (by_neqs o Di.conjuncts)
         (so consider ["U:point"] st "between R U S"
            at [3] from [0;1] by [three])
       ;hence "(between U R P /\ between U S Q) \
               \/ (between U S P /\ between U R Q)"
         at [4] using ORDER_TAC `{P:point,Q,R,S,U}` from [1;2]
       ;have "in_triangle (A,B,C) U"
         from [0;1;2;3] by [in_triangle1;tri_syms;BET_SYM]
       ;hence "out_triangle (A,B,C) P /\ out_triangle (A,B,C) Q"
         from [1;2;4] by [on_triangle_bet_out_triangle;on_triangle]
       ;qed by [out_triangle]]
      ;[suppose "~(?S. between P S Q /\ between B S C)" at [2]
       ;so assume "between B P C" at [3]
       ;hence "out_triangle (A,B,C) Q" at [4] from [0;1]
         by [out_triangle1;tri_syms;BET_SYM]
       ;have "?S. between P S Q /\ in_triangle (A,B,C) S" proof
         [consider ["S:point"] st "between P S R" at [5] from [1]
             by [BET_NEQS;three]
         ;hence "in_triangle (A,B,C) S" at [6] from [0;1;3]
           by [in_triangle1;tri_syms;BET_SYM]
         ;have "between P S Q" from [1;5] using ORDER_TAC `{P:point,Q,R,S}`
         ;qed from [6]]
       ;qed from [2;3;4]
         by [on_triangle;out_triangle;in_triangle_not_on_triangle]]]] in
  let part3 = theorem
    "!'a A B C was_inside P Q.
       crossing (A,B,C) was_inside P Q = 0
       ==> crossing (A,C,B) was_inside P Q = 1
       ==> crossing (B,C,A) was_inside P Q = 1
       ==> on_plane A 'a /\ on_plane B 'a /\ on_plane C 'a
           /\ on_plane P 'a /\ on_plane Q 'a
           /\ ~(?a. on_line A a /\ on_line B a /\ on_line C a)
           /\ ~on_polyseg [P;Q] A /\ ~on_polyseg [P;Q] B /\ ~on_polyseg [P;Q] C
           /\ ~on_triangle (A,B,C) Q
           ==> (in_triangle (A,B,C) P \/ on_triangle (A,B,C) P /\ was_inside
                <=> in_triangle (A,B,C) Q)"
    [fix ["'a:plane";"A:point";"B:point";"C:point"
         ;"was_inside:bool";"P:point";"Q:point"]
    ;assume "on_plane A 'a /\ on_plane B 'a /\ on_plane C 'a
             /\ on_plane P 'a /\ on_plane Q 'a" at [0]
    ;assume "~(?a. on_line A a /\ on_line B a /\ on_line C a)" at [1]
    ;assume "~on_polyseg [P; Q] A /\ ~on_polyseg [P; Q] B
             /\ ~on_polyseg [P; Q] C" at [2]
    ;assume "~on_triangle (A,B,C) Q" at [3]
    ;per cases
      [[suppose "(?R. between P R Q /\ between A R C)" at [4]
       ;assume "crossing (A,B,C) was_inside P Q = 0
                /\ crossing (A,C,B) was_inside P Q = 1
                /\ crossing (B,C,A) was_inside P Q = 1" at [5]
       ;tactics [USE_THEN "4" (MATCH_MP_TAC o MATCH_MP lemma2)]
       ;qed from [1;5]]
      ;[suppose "(?R. between P R Q /\ between B R C)" at [4]
       ;assume "crossing (A,B,C) was_inside P Q = 0
                /\ crossing (A,C,B) was_inside P Q = 1
                /\ crossing (B,C,A) was_inside P Q = 1" at [5]
       ;tactics [USE_THEN "4"
                    (MATCH_MP_TAC
                       o REWRITE_RULE [crossing_sym;tri_syms;BET_SYM]
                       o SPECL [`A:point`] o MATCH_MP lemma2)]
       ;qed from [1;5]]
      ;[suppose "~(?R. between P R Q /\ between A R C)
                 /\ ~(?R. between P R Q /\ between B R C)" at [4]
       ;tactics [unfold_crossing_tac]
       ;have "~(between A P C /\ between B P C)" proof
         [otherwise assume "between A P C /\ between B P C"
         ;obviously (by_cols o Di.split) (qed from [1])]
       ;qed from [4]]]] in
  let crossing_lt_2' =
    REWRITE_RULE [ONE;TWO;LT] crossing_lt_2
      |> REWRITE_RULE [GSYM ONE] in
  prove
    (`!'a A B C was_inside P Q.
       on_plane A 'a /\ on_plane B 'a /\ on_plane C 'a
       /\ on_plane P 'a /\ on_plane Q 'a
       /\ ~(?a. on_line A a /\ on_line B a /\ on_line C a)
       /\ ~on_polyseg [P;Q] A /\ ~on_polyseg [P;Q] B /\ ~on_polyseg [P;Q] C
       /\ ~on_triangle (A,B,C) Q
       ==> (crossing (A,B,C) was_inside P Q
            + crossing (A,C,B) was_inside P Q
            + crossing (B,C,A) was_inside P Q = 1
            <=> (in_triangle (A,B,C) P \/ on_triangle (A,B,C) P /\ was_inside
                <=> ~in_triangle (A,B,C) Q))`,
     REWRITE_TAC [IMP_CONJ] THEN REPEAT GEN_TAC THEN REPEAT DISCH_TAC
       THEN DISJ_CASES_TAC
       (SPECL
          [`A:point`;`B:point`;`C:point`;`was_inside:bool`;`P:point`;`Q:point`]
          crossing_lt_2')
       THEN DISJ_CASES_TAC
       (SPECL
          [`A:point`;`C:point`;`B:point`;`was_inside:bool`;`P:point`;`Q:point`]
          crossing_lt_2')
       THEN DISJ_CASES_TAC
       (SPECL
          [`B:point`;`C:point`;`A:point`;`was_inside:bool`;`P:point`;`Q:point`]
          crossing_lt_2')
       THEN ASM_REWRITE_TAC []
       THEN TRY (FIRST_X_MATCH 
                   ((FIRST_X_MATCH
                       ((FIRST_X_MATCH
                           (ASSUME_TAC o REWRITE_RULE
                              [crossing_sym])) o REWRITE_RULE
                           [crossing_sym]))
                       o REWRITE_RULE [crossing_sym]) part1)
       THEN TRY (FIRST_X_MATCH 
                   ((FIRST_X_MATCH
                       ((FIRST_X_MATCH
                           (ASSUME_TAC o REWRITE_RULE
                              [crossing_sym])) o REWRITE_RULE
                           [crossing_sym]))
                       o REWRITE_RULE [crossing_sym]) part2)
       THEN TRY (FIRST_X_MATCH 
                   ((FIRST_X_MATCH
                       ((FIRST_X_MATCH
                           (ASSUME_TAC o REWRITE_RULE
                              [crossing_sym])) o REWRITE_RULE
                           [crossing_sym]))
                       o REWRITE_RULE [crossing_sym]) part3)
       THEN FULL_REWRITE_TAC [tri_syms;crossing_sym]
       THEN REWRITE_TAC [ADD_0;ONE;ADD;SUC_INJ;NOT_SUC]
       THEN MP_TAC
       (SPECL
          [`A:point`;`B:point`;`C:point`;`was_inside:bool`;`P:point`;`Q:point`]
          crossing_sum_le_2)
       THEN ASM_REWRITE_TAC [ONE;TWO;LE;ADD;SUC_INJ;NOT_SUC]
       THEN ASM_MESON_TAC []);;

(* We now deal with the case that Q lies on the triangle. The following lemmas
   assume that Q lies between A and B. *)
let same_side_same_side = prove
  (`!A B P Q. between A P B /\ between A Q B
              ==> !R. between P R Q ==> between A R B`,
   REPEAT STRIP_TAC THEN ASSUM_LIST (ORDER_TAC `{A:point,B,P,Q,R}`));;

let opposite_sides = prove
  (`!A B P C. between A P B
    ==> ~(?a. on_line A a /\ on_line B a /\ on_line C a)
    ==> ~between A P C /\ ~between B P C`,
   REPEAT STRIP_TAC THEN discover_tac by_cols ASM_MESON_TAC);;

let opposite_sides_inside = prove
  (`!A B P Q C. between A Q B
   ==> between A P C
   ==> ~(?a. on_line A a /\ on_line B a /\ on_line C a)
   ==> ?R. between P R Q /\ in_triangle (A,B,C) R`,
   REPEAT STRIP_TAC
     THEN SUBGOAL_THEN `~(P:point=Q)`
     (fun thm -> ASM_MESON_TAC [thm;three;in_triangle1;BET_SYM])
     THEN discover_tac by_neqs ASM_MESON_TAC);;

let side_crossing_0 = theorem
  "!A B C P Q was_inside.
         ~on_polyseg [P;Q] A /\ ~on_polyseg [P;Q] B
         /\ between A Q B ==> crossing (A,B,C) was_inside P Q = 0"
  [fix ["A:point";"B:point";"C:point";"P:point";"Q:point";"was_inside:bool"]
  ;assume "between A Q B" at [0]
  ;tactics [unfold_crossing_tac]
  ;so assume "~between A P B" at [1]
  ;so assume "?R. between P R Q /\ between A R B"
  ;so consider ["R:point"] st "between P R Q /\ between A R B" at [2]
  ;unfolding by [on_polyseg_pair]
  ;qed using ORDER_TAC `{A:point,B,P,Q}`from [0;1]];;

let side_crossing_le_1 = theorem
  "!A B C P Q was_inside.
      ~(?a. on_line A a /\ on_line B a /\ on_line C a)
      /\ between A Q B ==>
         ~(crossing (A,C,B) was_inside P Q = 1
           /\ crossing (B,C,A) was_inside P Q = 1)"
  [tactics [unfold_crossing_tac]
  ;fix ["A:point";"B:point";"C:point";"P:point";"Q:point";"was_inside:bool"]
  ;assume "~(?a. on_line A a /\ on_line B a /\ on_line C a)" at [0]
  ;assume "between A Q B" at [1]
  ;have "~((?R. between P R Q /\ between A R C)
           /\ ?S. between P S Q /\ between B S C)" at [2] proof
    [otherwise consider ["R:point";"S:point"] st
       "between P R Q /\ between A R C /\ between P S Q /\ between B S C"
    ;obviously (by_cols o Di.conjuncts) (qed from [0;1] by [supplement1])]
  ;assume "(?R. between P R Q /\ between A R C)
           \/ ?R. between P R Q /\ between B R C"
    by [opposite_sides;BET_SYM] from [0;2]
  ;per cases
    [[suppose "?R. between P R Q /\ between A R C" at [3]
     ;so consider ["R:point"] st
       "between P R Q /\ between A R C" at [4]
     ;hence "~between B P C" at [5] proof
       [otherwise assume "between B P C"
       ;obviously (by_cols o Di.conjuncts)
         (qed by [supplement1;g21] from [0;1;4])]
     ;qed from [2;4]]
    ;[suppose "?R. between P R Q /\ between B R C" at [3]
     ;so consider ["R:point"] st
       "between P R Q /\ between B R C" at [4]
     ;hence "~between A P C" at [5] proof
       [otherwise assume "between A P C"
       ;obviously (by_cols o Di.conjuncts)
         (qed by [supplement1;g21] from [0;1;4])]
     ;qed from [2;4]]]
    from [this]];;
  
let same_side_no_crossing = prove
  (`!A B P C. between A P B /\ between A Q B
    /\ ~(?a. on_line A a /\ on_line B a /\ on_line C a)
    ==> crossing (A,B,C) was_inside P Q = 0
        /\ crossing (A,C,B) was_inside P Q = 0
        /\ crossing (B,C,A) was_inside P Q = 0`,
   REWRITE_TAC [crossing;on_polyseg_pair;on_triangle;DE_MORGAN_THM]
     THEN unfold_crossing_tac
     THEN REPEAT GEN_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC []
     THEN CONJ_TAC
     THEN ASM_MESON_TAC [same_side_same_side;opposite_sides]);;

let same_side_preserve = prove
  (`!A B P C. between A P B /\ between A Q B
   ==> new_was_inside (A,B,C) was_inside P Q = was_inside`,
   REWRITE_TAC [new_was_inside]
     THEN MESON_TAC [same_side_same_side
                    ;in_triangle_not_on_triangle;on_triangle]);;

let opposite_sides_now_inside = prove
  (`!A B C P Q. between A Q B /\ between A P C
    /\ ~(?a. on_line A a /\ on_line B a /\ on_line C a)
    ==> new_was_inside (A,B,C) was_inside P Q `,
   REWRITE_TAC [new_was_inside]
     THEN MESON_TAC [opposite_sides_inside;on_triangle]);;

let opposite_sides_no_crossing = prove
  (`!A B C P Q.
     ~(?a. on_line A a /\ on_line B a /\ on_line C a)
     /\ between A Q B /\ between A P C
   ==> crossing (B,C,A) was_inside P Q = 0`,
   REWRITE_TAC [crossing;on_polyseg_pair;on_triangle;DE_MORGAN_THM]
     THEN unfold_crossing_tac
     THEN MESON_TAC [in_triangle1;in_triangle_not_on_triangle
                    ;on_triangle;opposite_sides;BET_SYM]);;

let opposite_sides_was_inside = prove
  (`!A B C P Q. between A Q B /\ between A P C
    /\ ~(?a. on_line A a /\ on_line B a /\ on_line C a)
    ==> (was_inside <=> crossing (A,C,B) was_inside P Q = 0)`,
   REWRITE_TAC [crossing;on_polyseg_pair;on_triangle;DE_MORGAN_THM]
     THEN unfold_crossing_tac
     THEN MESON_TAC [in_triangle1;in_triangle_not_on_triangle
                    ;on_triangle;opposite_sides_inside;opposite_sides]);;

let in_side_no_crossing = prove
  (`!A B P C. in_triangle (A,B,C) P /\ between A Q B
    ==> crossing (A,C,B) was_inside P Q = 0
        /\ crossing (B,C,A) was_inside P Q = 0`,
   REWRITE_TAC [crossing;on_polyseg_pair;on_triangle;DE_MORGAN_THM]
     THEN unfold_crossing_tac
     THEN REPEAT GEN_TAC THEN DISCH_TAC
     THEN SUBGOAL_THEN `~(P:point = Q)` (CHOOSE_TAC o MATCH_MP three)
     THENL [ASM_MESON_TAC [in_triangle_not_on_triangle;on_triangle]
           ;ALL_TAC]
     THEN SUBGOAL_THEN `~(?R. between P R Q /\ on_triangle (A,B,C) R)`
     ASSUME_TAC
     THENL [ASM_MESON_TAC
               [BET_SYM;on_triangle;on_triangle_bet_in_triangle
               ;in_triangle_not_on_triangle]
           ;ALL_TAC]
     THEN REPEAT CONJ_TAC
     THEN ASM_MESON_TAC [in_triangle_not_on_triangle;on_triangle]);;

let in_side_now_inside = prove
  (`!A B P C. in_triangle (A,B,C) P /\ between A Q B
   ==> new_was_inside (A,B,C) was_inside P Q`,
     REWRITE_TAC [new_was_inside]
       THEN REPEAT STRIP_TAC
       THEN SUBGOAL_THEN `~(P:point = Q)` (CHOOSE_TAC o MATCH_MP three)
       THENL [ASM_MESON_TAC [on_triangle;in_triangle_not_on_triangle]
             ;ASM_MESON_TAC
               [on_triangle_bet_in_triangle;on_triangle;BET_SYM]]);;

let out_side_now_inside = theorem
  "!A B C P Q.
    ~(?a. on_line A a /\ on_line B a /\ on_line C a)
    /\ out_triangle (A,B,C) P /\ between A Q B
    ==> (crossing (A,C,B) was_inside P Q = 1
         ==> new_was_inside (A,B,C) was_inside P Q)"
  [fix ["A:point";"B:point";"C:point";"P:point";"Q:point"]
  ;tactics [REWRITE_TAC [crossing;on_polyseg_pair;on_triangle]
               THEN unfold_crossing_tac
               THEN REWRITE_TAC [new_was_inside]]
  ;assume "?R. between P R Q /\ between A R C" by [on_triangle;out_triangle]
  ;so consider ["R:point"] st "between P R Q /\ between A R C" at [0]
  ;assume "between A Q B /\ ~(?a. on_line A a /\ on_line B a /\ on_line C a)"
     at [1]
  ;so consider ["S:point"] st "between Q S R" from [0] by [three;BET_NEQS]
    at [2]
  ;hence "in_triangle (A,B,C) S" from [0;1] by [in_triangle1] at [3]
  ;hence "between P S Q" from [0;2] using ORDER_TAC `{P:point,R,Q,S}`
  ;qed from [1;3] by [on_triangle]];;

let out_side_now_outside = theorem
  "!A B C P Q.
    ~on_polyseg [P;Q] C
   /\ out_triangle (A,B,C) P /\ between A Q B
    ==> (crossing (A,C,B) was_inside P Q = 0
         /\ crossing (B,C,A) was_inside P Q = 0
         ==> ~new_was_inside (A,B,C) was_inside P Q)"
  [fix ["A:point";"B:point";"C:point";"P:point";"Q:point"]
  ;tactics [REWRITE_TAC [crossing;on_polyseg_pair;on_triangle]
               THEN unfold_crossing_tac
               THEN REWRITE_TAC [new_was_inside]]
  ;assume "out_triangle (A,B,C) P" at [0]
  ;assume "between A Q B" at [1]
  ;hence "~between A P C /\ ~between B P C" from [0] by
    [out_triangle;on_triangle]
  ;unfolding from [this]
  ;assume "?R. between P R Q /\ in_triangle (A,B,C) R"
     from [0;1] by [on_triangle;out_triangle]
  ;so consider ["R:point"] st "between P R Q /\ in_triangle (A,B,C) R"
     at [2]
  ;assume "~between P C Q /\ ~(P = C) /\ ~(Q = C)" at [3] from [0;1]
    by [out_triangle;on_triangle]
  ;have "~(?a. on_line C a /\ on_line P a /\ on_line Q a)" proof
    [otherwise assume "?a. on_line C a /\ on_line P a /\ on_line Q a"
    ;hence "between C P R \/ between C Q R" from [2;3]
       using ORDER_TAC `{C:point,P,Q,R}`
    ;qed by [on_triangle_bet_in_triangle;on_triangle
            ;out_triangle;in_triangle_not_on_triangle] from [0;1;2]]
  ;clearly (by_pasch o add_in_triangle o Di.conjuncts)
     (so consider ["S:point"] st
        "(?a. on_line S a /\ on_line P a /\ on_line Q a)
         /\ (between A S C \/ between B S C)"
        from [1;2] at [4])
  ;have "~in_triangle (A,B,C) P /\ ~in_triangle (B,A,C) P" from [0]
     by [out_triangle;tri_syms]
  ;obviously (by_ncols o add_in_triangle o Id.conjuncts) 
       (hence "~between Q P S" at [5] from [0;1;2;4]
          by [in_triangle1;BET_SYM])
  ;have "~between R Q S" by [on_triangle_bet_out_triangle;on_triangle;out_triangle]
     from [1;2;4] at [6]
  ;obviously (by_ncols o add_in_triangle o Di.conjuncts)
     (have "~(P = S) /\ ~(Q = S)"
        from [0;1;2;4]
        by [out_triangle;on_triangle;opposite_sides;BET_SYM])
  ;hence "between P S Q" from [2;4;5;6] using ORDER_TAC `{P:point,Q,R,S}`
  ;qed from [4]];;

let new_was_inside_syms = prove (`new_was_inside (A,B,C) was_inside P Q =
    new_was_inside (B,A,C) was_inside P Q /\ new_was_inside (A,B,C) was_inside
      P Q = new_was_inside (A,C,B) was_inside P Q`, REWRITE_TAC
        [new_was_inside;tri_syms]);;

(* Combining these lemmas tell us generally what happens when Q is between A and B. *)
let cross_1_same_side_lemma =
  let side_crossing_le_1 =
    CONV_RULE (ONCE_DEPTH_CONV CONTRAPOS_CONV THENC REWRITE_CONV [IMP_CONJ])
      side_crossing_le_1 in
  let crossing_lt_2' =
    REWRITE_RULE [ONE;TWO;LT] crossing_lt_2
      |> REWRITE_RULE [GSYM ONE] in
  prove
  (`!A B C.
     between A Q B
     ==> (in_triangle (A,B,C) P ==> was_inside)
     /\ (out_triangle (A,B,C) P ==> ~was_inside)
     /\ ~(?a. on_line A a /\ on_line B a /\ on_line C a)
     /\ ~on_polyseg [P;Q] A /\ ~on_polyseg [P;Q] B /\ ~on_polyseg [P;Q] C
     ==> (crossing (A,B,C) was_inside P Q
          + crossing (A,C,B) was_inside P Q
          + crossing (B,C,A) was_inside P Q = 1
          <=> was_inside = ~new_was_inside (A,B,C) was_inside P Q)`,
   REPEAT STRIP_TAC THEN ASM_SIMP_TAC [side_crossing_0;ADD]
     THEN DISJ_CASES_TAC
     (SPECL
        [`A:point`;`C:point`;`B:point`;`was_inside:bool`;`P:point`;`Q:point`]
        crossing_lt_2')
     THEN DISJ_CASES_TAC
     (SPECL
        [`B:point`;`C:point`;`A:point`;`was_inside:bool`;`P:point`;`Q:point`]
        crossing_lt_2')
     THEN ASM_REWRITE_TAC [ADD_0;ONE;ADD;SUC_INJ;NOT_SUC]
     THEN TRY (FIRST_X_MATCH (FIRST_X_MATCH ASSUME_TAC) side_crossing_le_1
                 THEN FULL_SIMP_TAC [CONJ_ACI;BET_SYM]
                 THEN FIRST_ASSUM CONTR_TAC)
     THEN MP_TAC (MESON [out_triangle]
                    `in_triangle (A,B,C) P \/ out_triangle (A,B,C) P
                     \/ on_triangle (A,B,C) P`)
     THEN REWRITE_ASM_TAC [on_polyseg_pair;DE_MORGAN_THM]
     THEN ASM_REWRITE_TAC [on_triangle]
     THEN POP_ASSUM (fun thm -> POP_ASSUM
       (fun thm' -> STRIP_TAC THEN MP_TAC thm THEN MP_TAC thm'))
     THEN ASM_SIMP_TAC
     [in_side_no_crossing;in_side_now_inside
     ;side_crossing_0;same_side_no_crossing
     ;opposite_sides_no_crossing;opposite_sides_now_inside
     ;same_side_preserve;out_side_now_inside
     ;REWRITE_RULE [on_polyseg_pair] out_side_now_outside]
     THEN REWRITE_TAC [TAUT `~(P <=> ~P)`;ADD;ONE;ADD_0;NOT_SUC]
     THEN MP_TAC (SPECL [`B:point`;`A:point`;`C:point`] out_side_now_inside)
     THEN MP_TAC (SPECL [`B:point`;`A:point`;`C:point`]
                    opposite_sides_now_inside)
     THEN MP_TAC (SPECL [`B:point`;`A:point`;`C:point`]
                    opposite_sides_was_inside)
     THEN MP_TAC (SPECL [`B:point`;`A:point`;`C:point`]
                    opposite_sides_no_crossing)
     THEN REWRITE_TAC [ONE;BET_SYM;tri_syms;new_was_inside_syms]
     THEN ASM_SIMP_TAC [opposite_sides_now_inside
                       ;BET_SYM;tri_syms;new_was_inside_syms]
     THEN ASM_MESON_TAC [NOT_SUC;opposite_sides_was_inside]);;

let cross_1_same_side = prove
  (`!A B C P Q.
      on_triangle (A,B,C) Q
      ==> (in_triangle (A,B,C) P ==> was_inside)
          /\ (out_triangle (A,B,C) P ==> ~was_inside)
          /\ ~(?a. on_line A a /\ on_line B a /\ on_line C a)
          /\ ~on_polyseg [P; Q] A
          /\ ~on_polyseg [P; Q] B
          /\ ~on_polyseg [P; Q] C
          ==> (crossing (A,B,C) was_inside P Q
               + crossing (A,C,B) was_inside P Q
               + crossing (B,C,A) was_inside P Q = 1
               <=> (was_inside =
                      ~new_was_inside (A,B,C) was_inside P Q))`,
   REPEAT GEN_TAC THEN REWRITE_TAC [on_triangle]
     THEN STRIP_TAC THEN
     (POP_ASSUM (MP_TAC o MATCH_MP cross_1_same_side_lemma)
        ORELSE REWRITE_TAC [on_polyseg_pair] THEN ASM_SIMP_TAC [])
     THENL [DISCH_THEN (MP_TAC o SPECL [`B:point`])
           ;DISCH_THEN (MP_TAC o SPECL [`A:point`])]
     THEN SIMP_TAC [ARITH_RULE `x + y + z = y + x + z /\ x + y + z = x + z + y`
                   ;tri_syms;CONJ_ACI;crossing_sym;new_was_inside_syms]);;

let not_on_new_was_inside = prove
  (`!A B C P Q. ~on_triangle (A,B,C) Q
   ==> (in_triangle (A,B,C) Q <=> new_was_inside (A,B,C) was_inside P Q)`,
   SIMP_TAC [new_was_inside]);;

let was_inside_imp = prove
  (`!A B C P Q was_inside.
      ~on_triangle (A,B,C) P ==> (in_triangle (A,B,C) P <=> was_inside)
      <=> ((in_triangle (A,B,C) P ==> was_inside)
           /\ (out_triangle (A,B,C) P ==> ~was_inside))`,
   REWRITE_TAC [out_triangle] THEN MESON_TAC [in_triangle_not_on_triangle]);;

(* If PQ does not intersect a vertex, then the number of crossings sum to 1
   precisely when was_inside changes truth value. When P does not lie on the
   triangle, we get to assume that was_inside tracks whether P is inside or
   outside. See not_on_new_was_inside to explain why this assumption is
   justified. *)
let cross_1 =
  prove
  (`!A B C P Q.
      on_plane A 'a
      /\ on_plane B 'a
      /\ on_plane C 'a
      /\ on_plane P 'a
      /\ on_plane Q 'a
      /\ ~(?a. on_line A a /\ on_line B a /\ on_line C a)
      /\ ~on_polyseg [P; Q] A
      /\ ~on_polyseg [P; Q] B
      /\ ~on_polyseg [P; Q] C
      /\ (~on_triangle (A,B,C) P ==> (in_triangle (A,B,C) P <=> was_inside))
      ==> (crossing (A,B,C) was_inside P Q
           + crossing (A,C,B) was_inside P Q
           + crossing (B,C,A) was_inside P Q = 1
           <=> (was_inside =
                  ~new_was_inside (A,B,C) was_inside P Q))`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `on_triangle (A,B,C) Q`
    THEN ASM_SIMP_TAC [cross_1_same_side;was_inside_imp]
    THEN MP_TAC (SPECL
                   [`'a:plane`;`A:point`;`B:point`;`C:point`;`was_inside:bool`
                   ;`P:point`;`Q:point`]
                   cross_1_not_on)
    THEN REWRITE_TAC [out_triangle]
    THEN ASM_SIMP_TAC [not_on_new_was_inside]
    THEN ASM_MESON_TAC []);; 

(* A segment which starts on an edge, moves into the same half-plane as the
   opposite vertex, and ends up outside the triangle must cross the polygonal
   segment [A;B;C]. *)
let tri_cut_half_plane = theorem
  "!A B C P Q hp. 
     between A P B
     /\ on_line A (line_of_half_plane hp)
     /\ on_line B (line_of_half_plane hp)
     /\ on_half_plane hp C
     /\ on_half_plane hp Q
     /\ out_triangle (A,B,C) Q
     ==> ?X. between P X Q /\ (between A X C \/ between B X C \/ X = C)"
  [fix ["A:point";"B:point";"C:point";"P:point";"Q:point";"hp:half_plane"]
  ;assume "between A P B" at [0]
  ;assume "on_line A (line_of_half_plane hp)
           /\ on_line B (line_of_half_plane hp)
           /\ on_half_plane hp C" at [1]
  ;assume "out_triangle (A,B,C) Q" at [2]
  ;assume "on_half_plane hp Q" at [3]
  ;have "~(?a. on_line A a /\ on_line B a /\ on_line Q a)"
     from [0;1;3] by [BET_NEQS;half_plane_not_on_line;g12]
     at [4]
  ;have "~(?a. on_line A a /\ on_line B a /\ on_line C a)"
     from [0;1] by [half_plane_not_on_line;g12;BET_NEQS]
     at [5]
  ;consider ["'a:plane"]
     st "on_plane A 'a /\ on_plane B 'a /\ on_plane C 'a /\ on_plane Q 'a"
     at [6] proof
     [so consider ["'a:plane"] st "on_plane A 'a /\ on_plane B 'a /\ on_plane C 'a"
         at [6] by [g14a]
     ;hence "!X. on_line X (line_of_half_plane hp) ==> on_plane X 'a"
       from [0;1] by [BET_NEQS;g16]
     ;hence "!X. on_half_plane hp X ==> on_plane X 'a"
       from [1;6] by [half_plane_on_plane]
     ;qed from [3;6]]
  ;obviously by_neqs
     (consider ["R:point"] st "between C R P" at [7] from [0;5] by [three])
  ;hence "in_triangle (A,B,C) R" at [8] from [0;5] by [in_triangle2]
  ;obviously by_planes
     (so consider ["S:point"] st "on_triangle (A,B,C) S /\ between R S Q"
        at [9] from [0;2;6;7] by [out_triangle;in_triangle_simple_closed])
  ;hence "between A S C \/ between B S C \/ S = C" at [10] proof
    [have "on_half_plane hp R" by [in_triangle]
       using K (USE_THEN "5" (MP_TAC o MATCH_MP unique_half_plane))
       from [1;8]
    ;hence "on_half_plane hp S" at [10] from [3;9] by [bet_on_half_plane2]
    ;hence "~between A S B" from [1] by [g12;g21;half_plane_not_on_line]
    ;qed from [1;9;10] by [half_plane_not_on_line;on_triangle]]
  ;per cases
    [[suppose "?a. on_line P a /\ on_line Q a /\ on_line R a"
     ;take ["C:point"]
     ;obviously (by_cols o Di.split)
       (hence "C = S /\ between R C Q" from [0;5;7;9;10])
     ;qed from [7;9] using ORDER_TAC `{C,P:point,Q,R,S}`]
    ;[suppose "~(?a. on_line P a /\ on_line Q a /\ on_line R a)" at [11]
     ;consider ["S':point"] st
       "(?a. on_line C a /\ on_line S' a /\ on_line S a) 
             /\ between P S' Q" at [12] proof
       [obviously (by_pasch o Di.conjuncts)
           (so consider ["S':point"] st
              "(?a. on_line C a /\ on_line S' a /\ on_line S a) 
                    /\ (between P S' R \/ between P S' Q)"
              at [12] from [7;9])
       ;so assume "between P S' R" at [13]
       ;hence "in_triangle (A,B,C) S'"
         from [0;8] by [on_triangle_bet_in_triangle;on_triangle]
       ;obviously (by_eqs o Di.conjuncts)
         (qed by [on_triangle;in_triangle_not_on_triangle]
            from [7;9;11;12;13])]
     ;have "on_half_plane hp S'"
       at [13] from [0;1;3;12] by [g21;g12;bet_on_half_plane]
     ;obviously by_neqs
       (have "(!X. on_half_plane hp X ==> on_plane X 'a)"
          from [0;1;6] by [half_plane_on_plane;g16])
     ;hence "~between C A S'/\ ~between C B S'"
       at [14] from [1;12;13] by [on_half_plane_not_bet]
     ;obviously (by_neqs o Di.conjuncts)
       (have "~(A = S') /\ ~(B = S') /\ ~(C = S)"
          from [1;7;9;10;11;12;13] by [half_plane_not_on_line] at [15])
     ;obviously (by_incidence o Di.split)
       (hence "(?a. on_line A a /\ on_line C a /\ on_line S' a)
                \/ (?a. on_line B a /\ on_line C a /\ on_line S' a)"
          at [16] by [g11_weak] from [10;12])
     ;obviously (by_neqs o Di.conjuncts)
       (hence "between A C S' \/ between A S' C 
               \/ between B C S' \/ between B S' C"
          from [5;7;11;12;14;15] by [four])
     ;so assume "between A C S' \/ between B C S'"
       from [5;12]
     ;so consider ["S'':point"] st
       "between P S'' S' /\ (between A S'' C \/ between B S'' C)"
       from [0;5] by [inner_pasch;BET_SYM] at [17]
     ;hence "between P S'' Q" using ORDER_TAC `{P:point,Q,S',S''}`
       from [12]
     ;qed from [17]]]];;

(* As a corollary, we prove that Q is in the same half plane as C exactly when
   there is a point inside the triangle between P and Q. *)
let tri_cut_on_half_plane = theorem
 "!A B C P Q hp. 
     between A P B
     /\ on_line A (line_of_half_plane hp)
     /\ on_line B (line_of_half_plane hp)
     /\ on_half_plane hp C
     ==> (on_half_plane hp Q <=> ?X. between P X Q /\ in_triangle (A,B,C) X)"
 [fix ["A:point";"B:point";"C:point";"P:point";"Q:point";"hp:half_plane"]
 ;assume "between A P B" at [0]
 ;assume "on_line A (line_of_half_plane hp)
          /\ on_line B (line_of_half_plane hp)
          /\ on_half_plane hp C" at [1]
 ;hence "~(?a. on_line A a /\ on_line B a /\ on_line C a)"  (* Refactor *)
   from [0] by [g12;g21;half_plane_not_on_line] at [2]
 ;have "on_half_plane hp Q ==> ?X. between P X Q /\ in_triangle (A,B,C) X" 
   at [3] proof 
   [assume "on_half_plane hp Q" at [3]
   ;per cases
     [[suppose "in_triangle (A,B,C) Q" at [4]
      ;have "~(P=Q)" from [0;1;3] by [g12;g21;half_plane_not_on_line]
      ;so consider ["R:point"] st "between P R Q" by [three]
      ;qed from [0;4] by [on_triangle_bet_in_triangle;on_triangle]]
     ;[suppose "~in_triangle (A,B,C) Q" at [4]
      ;so consider ["R:point"]
        st "(between P R Q \/ R = Q)
             /\ (C = R \/ between A R C \/ between B R C)" at [5]
        proof
        [per cases
            [[suppose "on_triangle (A,B,C) Q" at [5]
             ;have "~(A = Q) /\ ~(B = Q) /\ ~between A Q B"
               from [1;3] by [g12;g21;half_plane_not_on_line]
             ;qed from [5] by [on_triangle]]
            ;[suppose "~on_triangle (A,B,C) Q"
             ;hence "out_triangle (A,B,C) Q" from [4] by [out_triangle]
             ;qed from [0;1;3;4] by [tri_cut_half_plane]]]]
      ;hence "~(P = R)" from [0;1;3] by [g12;g21;half_plane_not_on_line]
      ;so consider ["S:point"]
        st "between P S R" at [6] by [three]
      ;obviously (by_cols o Di.split)
        (have "?a. on_line P a /\ on_line Q a /\ on_line R a /\ on_line S a"
           from [5;6])
      ;hence "between P S Q" at [7] from [5;6]
        using ORDER_TAC `{P:point,Q,R,S}`
      ;have "in_triangle (A,B,C) S \/ in_triangle (B,A,C) S"
        from [0;2;4;5;6] by [in_triangle1;in_triangle2;BET_SYM]
      ;qed from [7] by [tri_syms]]]]
 ;have "(?X. between P X Q /\ in_triangle (A,B,C) X) ==> on_half_plane hp Q"
   proof 
   [assume "?X. between P X Q /\ in_triangle (A,B,C) X" at [3]
   ;so consider ["X:point"] st
     "between P X Q /\ in_triangle (A,B,C) X" at [4]
   ;hence "on_half_plane hp X" 
     using K (USE_THEN "2" (MP_TAC o MATCH_MP unique_half_plane))
     from [1] by [in_triangle]
   ;qed from [0;1;4] by [g12;g21;bet_on_half_plane]]
 ;qed from [3]];;
  
(* When we consider changing the B vertex of a triangle, we assume that PQ
   does not intersect the extended part. This means that PQ intersects AB' in
   precisely the points that it intersects AB. The disjunctive assumption may
   appear odd, since it is redundant and one of the disjuncts is weaker than
   necessary. However, we want this hypothesis to propagate through into later
   lemmas where it would be difficult to infer manually. *)
let cross_change_side_lemma = theorem
  "!A B B' P Q X.
   (between A B B' \/ between A B' B \/ ~(A = B) /\ B = B')
   /\ ~(?X. on_polyseg [B;B'] X /\ on_polyseg [P;Q] X)
   /\ on_polyseg [P;Q] X 
   ==> (between A X B <=> between A X B')"
  [fix ["A:point";"B:point";"B':point";"P:point";"Q:point";"X:point"]
  ;assume "between A B B' \/ between A B' B \/ ~(A = B) /\ B = B'" at [0]
  ;assume "~(?X. on_polyseg [B;B'] X /\ on_polyseg [P;Q] X)" at [1]
  ;assume "P = X \/ Q = X \/ between P X Q" by [on_polyseg_pair] at [2]
  ;hence "~(X = B) /\ ~(X = B') /\ ~between B X B'"
    at [3] from [1] by [on_polyseg_pair]
  ;assume "between A X B \/ between A X B'" at [4]
  ;obviously (by_cols o Di.split)
    (hence "?a. on_line A a /\ on_line B a /\ on_line B' a /\ on_line X a")
    from [0] at [5] 
  ;per cases
    [[suppose "between A X B" at [6]
     ;hence "between A X B'" from [0;3;5]
       using ORDER_TAC `{A:point,B,B',X}`
     ;qed from [6]]
    ;[suppose "between A X B'" at [6]
     ;hence "between A X B" from [0;3;5]
       using ORDER_TAC `{A:point,B,B',X}`
     ;qed from [6]]]
    from [4]];;

let cross_change_lemma1 = theorem
  "!P Q A B B' C C'.
   (between A B B' \/ between A B' B \/ ~(A = B) /\ B = B')
   /\ ~(?X. on_polyseg [B;B'] X /\ on_polyseg [P;Q] X)
   /\ on_line A (line_of_half_plane hp) /\ on_line B (line_of_half_plane hp)
   /\ on_half_plane hp C /\ on_half_plane hp C'
   ==> (between A P B /\ (?R. between P R Q /\ in_triangle (A,B,C) R)
        <=> between A P B' /\ ?R. between P R Q /\ in_triangle (A,B',C') R)"
  [fix ["P:point";"Q:point";"A:point"
       ;"B:point";"B':point";"C:point";"C':point"]
  ;assume "between A B B' \/ between A B' B \/ ~(A = B) /\ B = B'" at [0]
  ;assume "~(?X. on_polyseg [B;B'] X /\ on_polyseg [P;Q] X)" at [1]
  ;assume "on_line A (line_of_half_plane hp) /\ on_line B (line_of_half_plane hp)
           /\ on_half_plane hp C /\ on_half_plane hp C'" at [2]
  ;have "!X. on_polyseg [P; Q] X
               ==> (between A X B <=> between A X B')"
      at [3] from [0;1] by [cross_change_side_lemma]
  ;have "~(?a. on_line A a /\ on_line B a /\ on_line C a)" at [4] from [0;2]
    by [g12;g21;half_plane_not_on_line]
  ;have "!X. in_triangle (A,B,C) X ==> on_half_plane hp X"
    using K (USE_THEN "4" (MP_TAC o MATCH_MP unique_half_plane))
    at [5] by [in_triangle] from [2]
  ;have "~(?a. on_line A a /\ on_line B' a /\ on_line C' a)" at [6] from [0;2]
    by [g12;g21;half_plane_not_on_line]
  ;have "on_line B' (line_of_half_plane hp)"
    at [7] from [0;2] by [g12;g21]
  ;hence "!X. in_triangle (A,B',C') X ==> on_half_plane hp X"
    using K (USE_THEN "6" (MP_TAC o MATCH_MP unique_half_plane))
    by [g12;g21;in_triangle] from [0;2]
  ;qed from [2;3;5;7] 
      by [tri_cut_on_half_plane;five2;on_polyseg_pair]];;

let cross_change_eq = prove
  (`!P Q A B B' C C' was_inside was_inside'.
      (between A B B' \/ between A B' B \/ ~(A = B) /\ B = B')
      /\ ~(?X. on_polyseg [B;B'] X /\ on_polyseg [P;Q] X)
      /\ on_line A (line_of_half_plane hp) /\ on_line B (line_of_half_plane hp)
      /\ on_half_plane hp C /\ on_half_plane hp C'
      ==> (between A P B ==> was_inside = was_inside')
      ==> crossing (A,B,C) was_inside P Q = crossing (A,B',C') was_inside' P Q`,
   REPEAT GEN_TAC THEN ASSUME_ANT
     THEN DISCH_THEN (MP_TAC o MATCH_MP cross_change_lemma1)
     THEN MP_TAC (GEN `X:point` (SPEC_ALL cross_change_side_lemma))
     THEN ASM_REWRITE_TAC [on_polyseg_pair]
     THEN unfold_crossing_tac THEN POP_ASSUM (K ALL_TAC)
     THEN REPEAT STRIP_TAC THEN REPEAT COND_CASES_TAC
     THEN ASM_MESON_TAC []);;

(* We generally assume that vertices are not intersected by PQ, but this is
   stronger than necessary for moving the vertex of a triangle, and would
   require that we discharge an annoying assumption in the proof of the main
   theorem. So in order to get cross_change_new_was_inside through, we need the
   following lemma. *)
let vertex_side_inside = prove
  (`!A B C P. 
      ~(?a. on_line A a /\ on_line B a /\ on_line C a)
       /\ between A P B
       ==> ?Q. between C Q P /\ in_triangle (A,B,C) Q`,
   REPEAT STRIP_TAC
     THEN SUBGOAL_THEN `~(C:point = P)`
           (fun thm -> ASM_MESON_TAC [three;in_triangle2;thm])
     THEN discover_tac by_neqs REWRITE_TAC);;

let cross_change_new_was_inside = theorem
  "!P Q A B B' C C'.
      (between A B B' \/ between A B' B \/ ~(A = B) /\ B = B')
      /\ ~(?X. on_polyseg [B;B'] X /\ on_polyseg [P;Q] X)
      /\ ~on_polyseg [P;Q] A
      /\ on_line A (line_of_half_plane hp) /\ on_line B (line_of_half_plane hp)
      /\ on_half_plane hp C /\ on_half_plane hp C'
      /\ ~between A P B /\ between A Q B
      ==> new_was_inside (A,B,C) was_inside P Q 
          = new_was_inside (A,B',C') was_inside' P Q"
  [fix ["P:point";"Q:point";"A:point"
       ;"B:point";"B':point";"C:point";"C':point"]
  ;assume "(between A B B' \/ between A B' B \/ ~(A = B) /\ B = B')
           /\ ~(?X. on_polyseg [B; B'] X /\ on_polyseg [P; Q] X)" at [0]
  ;hence "!X. on_polyseg [P;Q] X ==> (between A X B <=> between A X B')"
     at [1] by [cross_change_side_lemma]
  ;assume "on_line A (line_of_half_plane hp)
           /\ on_line B (line_of_half_plane hp)" at [2]
  ;assume "on_half_plane hp C /\ on_half_plane hp C'" at [3]
  ;assume "between A Q B /\ between A Q B'" from [1]
     by [on_polyseg_pair] at [4]
  ;hence "(?R. between P R Q /\ in_triangle (A,B,C) R)
          <=> ?R. between P R Q /\ in_triangle (A,B',C') R" at [5] proof
     [hence "between A Q B /\ (?R. between Q R P /\ in_triangle (A,B,C) R)
          <=> between A Q B' /\ (?R. between Q R P /\ in_triangle (A,B',C') R)"
         from [0;2;3] using K (MATCH_MP_TAC cross_change_lemma1)
         by [on_polyseg_pair;BET_SYM];
      qed from [4] by [BET_SYM]]
  ;assume "~on_polyseg [P;Q] A /\ ~on_polyseg [P;Q] B"
    at [6] from [0] by [on_polyseg_pair]
  ;have "~(?a. on_line A a /\ on_line B a /\ on_line C a)"
     from [0;2;3] by [g12;BET_NEQS;half_plane_not_on_line]
  ;hence "on_triangle (A,B,C) P /\ ~(?R. between P R Q /\ in_triangle (A,B',C') R)
          ==> between A P B" at [7]
     using (K (REWRITE_TAC [on_triangle])
              THEN' MESON_TAC o map (REWRITE_RULE [on_polyseg_pair]))
     by [REWRITE_RULE [BET_SYM;tri_syms]
            (SPECL [`B:point`;`A:point`] opposite_sides_inside)
        ;opposite_sides_inside;vertex_side_inside]
     from [4;5;6]
  ;assume "~on_polyseg [P;Q] B'" from [0] by [on_polyseg_pair] at [8]
  ;have "~(?a. on_line A a /\ on_line B' a /\ on_line C' a)"
     from [0;2;3] by [g12;g21;half_plane_not_on_line]
  ;hence "on_triangle (A,B',C') P /\ ~(?R. between P R Q /\ in_triangle (A,B,C) R)
          ==> between A P B" at [9]
     using (K (REWRITE_TAC [on_triangle])
              THEN' MESON_TAC o map (REWRITE_RULE [on_polyseg_pair]))
     by [REWRITE_RULE [BET_SYM;tri_syms]
            (SPECL [`B':point`;`A':point`;`P:point`;`Q:point`;`C':point`]
               opposite_sides_inside)
        ;opposite_sides_inside;vertex_side_inside]
     from [1;4;5;6;8]
  ;assume "~between A P B"
  ;qed from [1;4;5;7;9] using (MESON_TAC o map (REWRITE_RULE [on_polyseg_pair]))
      by [on_triangle;new_was_inside]];;

let on_side_on_line = theorem
  "!P Q A B. ~on_polyseg [P;Q] A /\ ~on_polyseg [P;Q] B
             /\ between A Q B
             /\ (?a. on_line A a /\ on_line B a /\ on_line P a)
             ==> between A P B"
  [fix ["P:point";"Q:point";"A:point";"B:point"]
  ;assume "~(P = A) /\ ~(P = B) /\ ~(Q = A) /\ ~(Q = B)
           /\ ~between P A Q /\ ~between P B Q" at [0]
     by [on_polyseg_pair]
  ;assume "between A Q B" at [1]
  ;assume "?a. on_line A a /\ on_line B a /\ on_line P a"
  ;qed using ORDER_TAC `{A:point,B,P,Q}` from [0;1]];;

(* P and Q should probably be switched throughout here, since that's how the
   theorem is applied. *)
let cross_change_lemma2 = theorem
  "!P Q A B B' C C'.
    ~(?a. on_line A a /\ on_line B' a /\ on_line C' a)
    /\ on_plane A 'a /\ on_plane B 'a /\ on_plane C 'a /\ on_plane C' 'a
    /\ on_plane Q 'a /\ ~on_polyseg [P;Q] A
    /\ on_line A (line_of_half_plane hp) /\ on_line B (line_of_half_plane hp)
    /\ on_half_plane hp C /\ ~on_half_plane hp C'
    /\ ~(?X. on_polyseg [B;B'] X /\ on_polyseg [P;Q] X)
    /\ (between A B B' \/ between A B' B \/ ~(A = B) /\ B = B')
    ==> ~between A Q B
    ==> (between A P B /\ (?R. between P R Q /\ in_triangle (A,B,C) R)
         <=> between A P B'
             /\ ~(?R. between P R Q /\ in_triangle (A,B',C') R))"
  [fix ["P:point";"Q:point";"A:point"
       ;"B:point";"B':point";"C:point";"C':point"]
  ;assume "on_plane A 'a /\ on_plane B 'a /\ on_plane C 'a /\ on_plane C' 'a
           /\ on_plane Q 'a"
     at [0]
  ;assume "between A B B' \/ between A B' B \/ ~(A = B) /\ B = B'" at [1]
  ;assume "~(?X. on_polyseg [B;B'] X /\ on_polyseg [P;Q] X)" at [2]
  ;assume "on_line A (line_of_half_plane hp) /\ on_line B (line_of_half_plane hp)
           /\ on_half_plane hp C /\ ~on_half_plane hp C'" at [3]
  ;assume "~(?a. on_line A a /\ on_line B' a /\ on_line C' a)" at [4]
  ;so consider ["hp':half_plane"]
     st "on_line A (line_of_half_plane hp')
           /\ on_line B' (line_of_half_plane hp')
           /\ on_half_plane hp' C'"
     at [5] from [4] by [unique_half_plane]
  ;hence "line_of_half_plane hp = line_of_half_plane hp'"
     by [g12;g21] from [1;3] at [6]
  ;have "between A P B /\ (?R. between P R Q /\ in_triangle (A,B,C) R)
         ==> between A P B' /\ ~(?S. between P S Q /\ in_triangle (A,B',C') S)"
     at [7] proof
     [assume "between A P B" at [7]
     ;hence "between A P B'" by [cross_change_side_lemma;on_polyseg_pair]
       from [1;2]
     ;assume "?R. between P R Q /\ in_triangle (A,B,C) R"
     ;so consider ["R:point"] st "between P R Q /\ in_triangle (A,B,C) R"
       at [8]
     ;otherwise assume "?S. between P S Q /\ in_triangle (A,B',C') S"
     ;so consider ["S:point"] st "between P S Q /\ in_triangle (A,B',C') S"
       at [9]
     ;have "~(?a. on_line A a /\ on_line B a /\ on_line C a)"
       from [1;3] by [g12;BET_NEQS;half_plane_not_on_line] at [10]
     ;hence "on_half_plane hp R" by [in_triangle]
       at [11] from [3;8]
       using K (USE_THEN "10" (MP_TAC o MATCH_MP unique_half_plane))
     ;have "on_line P (line_of_half_plane hp)"
       at [12] from [3;7] by [g21;g12]
     ;hence "on_half_plane hp Q /\ on_half_plane hp S"
       by [bet_on_half_plane] at [13] from [8;9;11]
     ;obviously by_cols
       (have "on_line P (line_of_half_plane hp')"
          from [1;5;7] by [g12;g21])
     ;hence "~on_half_plane hp' S"
       from [3;5;6;13] by [on_half_plane_disjoint]
     ;hence "~in_triangle (A,B',C') S" by [in_triangle] from [5]
       using K (USE_THEN "4" (MP_TAC o MATCH_MP unique_half_plane))
     ;qed from [9]]
  ;assume "~on_polyseg [P; Q] A /\ ~on_polyseg [P; Q] B"
    from [2] by [on_polyseg_pair] at [8]
  ;assume "~between A Q B" at [9]
  ;have "between A P B' /\ ~(?S. between P S Q /\ in_triangle (A,B',C') S)
         ==> between A P B /\ ?R. between P R Q /\ in_triangle (A,B,C) R"
    proof
    [assume "between A P B'" at [10]
    ;hence "between A P B" at [11] by [cross_change_side_lemma;on_polyseg_pair]
       from [1;2]
    ;hence "~on_line Q (line_of_half_plane hp)" from [3;8;9;11]
      by [on_side_on_line;on_polyseg_pair;BET_SYM] at [12]
    ;assume "~(?S. between P S Q /\ in_triangle (A,B',C') S)" at [13]
    ;hence "~on_half_plane hp' Q" by [tri_cut_on_half_plane]
       from [5;6;10] at [14]
    ;have "on_half_plane hp Q" proof
      [have "!X. on_line X (line_of_half_plane hp) ==> on_plane X 'a"
         from [0;1;3] by [g16;BET_NEQS] at [15]
      ;have "~(hp = hp')" from [3;5]
      ;qed by [half_plane_on_plane] from [0;3;5;6;12;14;15]
        using K (MP_TAC (SPECL [`hp:half_plane`;`hp':half_plane`;`Q:point`] 
                           half_plane_cover2))]
    ;qed by [tri_cut_on_half_plane] from [3;11]]
  ;qed from [7]];;

(* Exactly the same proof for cross_change_eq but based on
   cross_change_lemma2. *)
let cross_change_eq2 = prove
  (`!P Q A B B' C C' was_inside was_inside'.
      ~(?a. on_line A a /\ on_line B' a /\ on_line C' a)
      /\ on_plane A 'a /\ on_plane B 'a /\ on_plane C 'a /\ on_plane C' 'a
      /\ on_plane Q 'a /\ ~on_polyseg [P;Q] A
      /\ on_line A (line_of_half_plane hp) /\ on_line B (line_of_half_plane hp)
      /\ on_half_plane hp C /\ ~on_half_plane hp C'
      /\ ~(?X. on_polyseg [B;B'] X /\ on_polyseg [P;Q] X)
      /\ (between A B B' \/ between A B' B \/ ~(A = B) /\ B = B')
      ==> (between A P B ==> was_inside = ~was_inside')
      ==> crossing (A,B,C) was_inside P Q
          = crossing (A,B',C') was_inside' P Q`,
   REPEAT GEN_TAC THEN ASSUME_ANT
     THEN DISCH_THEN (MP_TAC o MATCH_MP cross_change_lemma2)
     THEN MP_TAC (GEN `X:point` (SPEC_ALL cross_change_side_lemma))
     THEN ASM_REWRITE_TAC [on_polyseg_pair]
     THEN unfold_crossing_tac THEN POP_ASSUM (K ALL_TAC)
     THEN REPEAT STRIP_TAC THEN REPEAT COND_CASES_TAC
     THEN ASM_MESON_TAC []);;

(* There's a *lot* of overlap here with cross_change_new_was_inside. Step 7 and
   step 9 of the earlier proof are steps 10 and the penultimate step of this
   proof, and are the key steps. They are also both derived from
   cross_change_lemma and cross_change_lemma2 respectively. *)
let cross_change_new_was_inside2 = theorem
  "!P Q A B B' C C'.
      ~(?a. on_line A a /\ on_line B' a /\ on_line C' a)
      /\ on_plane A 'a /\ on_plane B 'a /\ on_plane C 'a /\ on_plane C' 'a
      /\ on_plane P 'a
      /\ (between A B B' \/ between A B' B \/ ~(A = B) /\ B = B')
      /\ ~(?X. on_polyseg [B;B'] X /\ on_polyseg [P;Q] X)
      /\ ~on_polyseg [P;Q] A
      /\ on_line A (line_of_half_plane hp) /\ on_line B (line_of_half_plane hp)
      /\ on_half_plane hp C /\ ~on_half_plane hp C'
      /\ ~between A P B /\ between A Q B
      ==> new_was_inside (A,B,C) was_inside P Q 
          = ~new_was_inside (A,B',C') was_inside' P Q"
  [fix ["P:point";"Q:point";"A:point"
       ;"B:point";"B':point";"C:point";"C':point"]
  ;assume "(between A B B' \/ between A B' B \/ ~(A = B) /\ B = B')
           /\ ~(?X. on_polyseg [B; B'] X /\ on_polyseg [P; Q] X)" at [0]
  ;hence "!X. on_polyseg [P;Q] X ==> (between A X B <=> between A X B')"
     at [1] by [cross_change_side_lemma]
  ;assume "on_line A (line_of_half_plane hp)
           /\ on_line B (line_of_half_plane hp)" at [2]
  ;assume "on_half_plane hp C /\ ~on_half_plane hp C'" at [3]
  ;assume "between A Q B /\ between A Q B'" from [1]
     by [on_polyseg_pair] at [4]
  ;assume "on_plane A 'a /\ on_plane B 'a /\ on_plane C 'a /\ on_plane C' 'a
           /\ on_plane P 'a"
    at [5]
  ;assume "~(?a. on_line A a /\ on_line B' a /\ on_line C' a)" at [6]
  ;assume "~on_polyseg [P;Q] A /\ ~on_polyseg [P;Q] B /\ ~on_polyseg [P;Q] B'"
    from [0] by [on_polyseg_pair] at [7]
  ;assume "~between A P B" at [8]
  ;hence "((?R. between P R Q /\ in_triangle (A,B,C) R)
          <=> ~(?R. between P R Q /\ in_triangle (A,B',C') R))"
    at [9] proof
     [hence "(between A Q B /\ (?R. between Q R P /\ in_triangle (A,B,C) R)
              <=> between A Q B'
                  /\ ~(?R. between Q R P /\ in_triangle (A,B',C') R))"
         from [0;2;3;4;5;6;7] using K (MATCH_MP_TAC (REWRITE_RULE [IMP_IMP]
                                                       cross_change_lemma2))
         by [on_polyseg_pair;BET_SYM];
      qed from [4] by [BET_SYM]]
  ;hence "on_triangle (A,B',C') P /\ (?R. between P R Q /\ in_triangle (A,B,C) R)
          ==> between A P B" at [10]
    using (K (REWRITE_TAC [on_triangle])
             THEN' MESON_TAC o map (REWRITE_RULE [on_polyseg_pair]))
    by [REWRITE_RULE [BET_SYM;tri_syms]
           (SPECL [`B:point`;`A:point`] opposite_sides_inside)
       ;opposite_sides_inside;vertex_side_inside]
    from [1;4;6;7]
  ;have "~(?a. on_line A a /\ on_line B a /\ on_line C a)"
     from [0;2;3] by [g12;BET_NEQS;half_plane_not_on_line]
  ;hence "on_triangle (A,B,C) P /\ (?R. between P R Q /\ in_triangle (A,B',C') R)
          ==> between A P B"
    using (K (REWRITE_TAC [on_triangle])
             THEN' MESON_TAC o map (REWRITE_RULE [on_polyseg_pair]))
    by [REWRITE_RULE [BET_SYM;tri_syms]
           (SPECL [`B:point`;`A:point`] opposite_sides_inside)
       ;opposite_sides_inside;vertex_side_inside]
    from [1;4;6;7;9]
  ;qed from [1;4;8;9;10] using (MESON_TAC o map (REWRITE_RULE [on_polyseg_pair]))
      by [on_triangle;new_was_inside]];;

(* The total number of crossings at side AB. *)
let polyseg_crossings = define
  `polyseg_crossings (A,B,C) was_inside [] = 0
   /\ polyseg_crossings (A,B,C) was_inside (CONS seg Ps)
        = crossing (A,B,C) was_inside (FST seg) (SND seg)
          + polyseg_crossings (A,B,C)
              (new_was_inside (A,B,C) was_inside (FST seg) (SND seg)) Ps`;;

(* The final context. *)
let polyseg_new_was_inside = define
  `polyseg_new_was_inside (A,B,C) was_inside [] = was_inside
   /\ polyseg_new_was_inside (A,B,C) was_inside (CONS seg Ps)
        = polyseg_new_was_inside (A,B,C)
            (new_was_inside (A,B,C) was_inside (FST seg) (SND seg))
            Ps`;;

let le_2_even = prove
  (`!n. n <= 2 ==> (EVEN n <=> ~(n = 1))`,
   CONV_TAC (REDEPTH_CONV num_CONV) THEN REWRITE_TAC [LE] THEN REPEAT STRIP_TAC
     THEN ASM_REWRITE_TAC [EVEN;SUC_INJ;NOT_SUC]);;

(* Assuming that was_inside is consistent with whether the first element of Ps
   is inside the triangle, an even number of crossings occurs exactly when the
   final value of was_inside is the same as it began. *)
let polyseg_crossings_even_change = prove
  (`!Ps was_inside.
      on_plane A 'a /\ on_plane B 'a /\ on_plane C 'a
      /\ (!X. MEM X Ps ==> on_plane X 'a)
      /\ ~on_polyseg Ps A /\ ~on_polyseg Ps B /\ ~on_polyseg Ps C
      /\ ~(?a. on_line A a /\ on_line B a /\ on_line C a)
      ==> (~on_triangle (A,B,C) (HD Ps)
         ==> (in_triangle (A,B,C) (HD Ps) <=> was_inside))
      ==> (EVEN (polyseg_crossings (A,B,C) was_inside (ADJACENT Ps)
                 + polyseg_crossings (A,C,B) was_inside (ADJACENT Ps)
                 + polyseg_crossings (B,C,A) was_inside (ADJACENT Ps))
        <=> was_inside
            <=> polyseg_new_was_inside (A,B,C) was_inside (ADJACENT Ps))`,
   LIST_INDUCT_TAC2 THEN REWRITE_TAC
     [ADJACENT_CLAUSES;polyseg_crossings;polyseg_new_was_inside;ADD_CLAUSES;EVEN]
     THEN POP_ASSUM MP_TAC
     THEN ONCE_REWRITE_TAC [on_polyseg_CONS2']
     THEN REWRITE_TAC [DE_MORGAN_THM;GSYM IN_SET_OF_LIST
                      ;set_of_list;FORALL_IN_INSERT;HD]
     THEN REWRITE_TAC [IN_SET_OF_LIST] THEN DISCH_TAC
     THEN ONCE_REWRITE_TAC [ARITH_RULE `(a + x) + (b + y) + (c + z)
                                        = (a + b + c) + x + y + z`]
     THEN ONCE_REWRITE_TAC [EVEN_ADD]
     THEN SIMP_TAC [crossing_sum_le_2;le_2_even] THEN REPEAT STRIP_TAC
     THEN MP_TAC cross_1 THEN ASM_SIMP_TAC []
     THEN DISCH_THEN (K ALL_TAC) THEN REWRITE_TAC [new_was_inside_syms]
     THEN MP_TAC (SPECL [`A:point`;`B:point`;`C:point`;`x:point`;`y:point`]
                    not_on_new_was_inside)
     THEN ASM_SIMP_TAC [] THEN MESON_TAC []);;

let not_on_polyseg_new_was_inside = prove
  (`!segs A B C P Q was_inside. ~on_triangle (A,B,C) Q
     ==> (in_triangle (A,B,C) Q
          <=> polyseg_new_was_inside (A,B,C) was_inside (APPEND segs [P,Q]))`,
   LIST_INDUCT_TAC
     THEN ASM_REWRITE_TAC [polyseg_new_was_inside;APPEND
                          ;not_on_new_was_inside;APPEND]);;

let not_on_polyseg_new_was_inside2 = prove
  (`!Ps A B C P Q was_inside.
     ~(Ps = []) /\ ~on_triangle (A,B,C) P
     ==> (polyseg_new_was_inside (A,B,C) was_inside
            (ADJACENT (APPEND Ps [P])) <=> in_triangle (A,B,C) P)`,
   LIST_INDUCT_TAC2 THEN TRY (POP_ASSUM MP_TAC)
     THEN ASM_SIMP_TAC
     [polyseg_new_was_inside;ADJACENT_CLAUSES;APPEND;GSYM not_on_new_was_inside
     ;NOT_CONS_NIL;HD]);;

(* Key result: if Ps is a closed polygonal segment, then the number of
   crossings is even (for an appropriate choice of was_inside). *)
let polyseg_crossings_even =
  (* We assume that was_inside is fixed under polyseg_new_was_inside. An
     appropriate fixpoint is just polyseg_new_was_inside for an arbitrary
     initial was_inside. *)
  let lemma = prove
    (`!was_inside 'a P Ps.
        Qs = CONS P (APPEND Ps [P])
        ==> was_inside = polyseg_new_was_inside (A,B,C)
                         was_inside (ADJACENT Qs)
        ==> on_plane A 'a /\ on_plane B 'a /\ on_plane C 'a
            /\ (!X. MEM X Qs ==> on_plane X 'a)
            /\ ~on_polyseg Qs A /\ ~on_polyseg Qs B /\ ~on_polyseg Qs C
            /\ ~(?a. on_line A a /\ on_line B a /\ on_line C a)
            ==> EVEN (polyseg_crossings (A,B,C) was_inside (ADJACENT Qs)
                      + polyseg_crossings (A,C,B) was_inside (ADJACENT Qs)
                      + polyseg_crossings (B,C,A) was_inside (ADJACENT Qs))`,
     REPEAT GEN_TAC THEN DISCH_THEN (fun thm -> REWRITE_TAC [thm])
       THEN DISCH_TAC THEN DISCH_THEN
       (MP_TAC o SPECL [`was_inside:bool`] o MATCH_MP polyseg_crossings_even_change)
       THEN ASSUM_LIST (CONV_TAC o LAND_CONV o LAND_CONV o ONCE_REWRITE_CONV)
       THEN REWRITE_TAC [HD;GSYM APPEND]
       THEN SIMP_TAC [not_on_polyseg_new_was_inside2
                     ;APPEND_EQ_NIL;NOT_CONS_NIL]
       THEN DISCH_THEN (K ALL_TAC) THEN ASM_REWRITE_TAC [APPEND]
       THEN POP_ASSUM ACCEPT_TAC) in
  let fixpoint = prove
    (`!Ps. polyseg_new_was_inside (A,B,C) was_inside Ps
          = polyseg_new_was_inside (A,B,C)
        (polyseg_new_was_inside (A,B,C) was_inside Ps) Ps`,
     LIST_INDUCT_TAC THEN REWRITE_TAC [polyseg_new_was_inside;new_was_inside]
       THEN ASM_MESON_TAC []) in
  GEN_ALL
    (REWRITE_RULE [GSYM fixpoint]
       (SPECL [`polyseg_new_was_inside (A,B,C) was_inside (ADJACENT Qs)`] 
          lemma));;

(* Key result: the number of crossings at AB for a triangle ABC is exactly the
   same as the number of crossings at AB for a triangle AB'C', where B' is on
   the ray AB, and C' is an arbitrary point in the plane. *)
let change_triangle =
  let new_was_inside_tac y cross_change_new_was_inside =
    SUBGOAL_THEN (vsubst [y,`Y:point`]
                    `!X. on_polyseg [x;Y] X ==>
                         (between A X B <=> between A X B')`)
      (ASSUME_TAC o REWRITE_RULE [on_polyseg_pair])
      THENL [GEN_TAC THEN DISCH_TAC
                THEN MATCH_MP_TAC cross_change_side_lemma
                THEN EXISTS_TAC `x:point` THEN EXISTS_TAC y
                THEN ASM_REWRITE_TAC [new_was_inside;on_triangle]
            ;ALL_TAC]
      THEN ASM_CASES_TAC `between A x B`
      THENL [POP_ASSUM (fun thm -> REWRITE_ASM_TAC [thm] THEN MP_TAC thm)
                THEN POP_ASSUM MP_TAC
                THEN ASM_REWRITE_TAC [new_was_inside;on_triangle]
                THEN SIMP_TAC [] THEN MESON_TAC
                [same_side_same_side;on_triangle;in_triangle_not_on_triangle]
            ;DISCH_TAC THEN MATCH_MP_TAC cross_change_new_was_inside
              THEN ASM_REWRITE_TAC []] in
  let lemma_prf cross_change_eq cross_change_new_was_inside = 
    LIST_INDUCT_TAC2 THEN REPEAT GEN_TAC THEN DISCH_THEN SUBST1_TAC
      THEN REWRITE_TAC
      [ADJACENT_CLAUSES;polyseg_new_was_inside;polyseg_crossings;APPEND
      ;ADD_CLAUSES]
      THEN TRY (POP_ASSUM MP_TAC)
      THEN SIMP_TAC []
      THEN REWRITE_TAC [HD;APPEND;GSYM IN_SET_OF_LIST;set_of_list]
      THEN REWRITE_TAC [FORALL_IN_INSERT;IN_SET_OF_LIST]
      THEN ONCE_REWRITE_TAC [GSYM MEM_REVERSE]
      THEN REWRITE_TAC [REVERSE_APPEND;REVERSE;APPEND]
      THEN REWRITE_TAC [GSYM IN_SET_OF_LIST;set_of_list]
      THEN REWRITE_TAC [FORALL_IN_INSERT;IN_SET_OF_LIST;MEM_REVERSE]
      THEN TRY (DISCH_THEN (ASSUME_TAC o REWRITE_RULE [IMP_IMP;HD;APPEND])
                  THEN CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV
                                              [on_polyseg_CONS2']))
                  THEN CONV_TAC (RAND_CONV
                                   (LAND_CONV (PAT_CONV `\y. ~(?X. x /\ y)`
                                                 (ONCE_REWRITE_CONV
                                                    [on_polyseg_CONS2']))))
                  THEN REWRITE_TAC [DE_MORGAN_THM;LEFT_OR_DISTRIB
                                   ;EXISTS_OR_THM])
      THEN REWRITE_TAC [IMP_CONJ] THEN REPEAT DISCH_TAC
      THENL
      [MATCH_MP_TAC (TAUT `(Q ==> P) /\ Q ==> P /\ Q `) THEN CONJ_TAC
          THENL [DISCH_TAC THEN MATCH_MP_TAC
                    (REWRITE_RULE [IMP_IMP] cross_change_eq)
                    THEN ASM_REWRITE_TAC []
                ;new_was_inside_tac `P:point` cross_change_new_was_inside]
      ;CONJ_TAC
        THENL [MATCH_MP_TAC (ARITH_RULE `a = x /\ b = y ==> a + b = x + y`)
                  THEN CONJ_TAC
                THENL [MATCH_MP_TAC (REWRITE_RULE [IMP_IMP] cross_change_eq)
                          THEN ASM_REWRITE_TAC []
                      ;FIRST_X_ASSUM
                        (MATCH_MP_TAC o CONJUNCT1
                           o REWRITE_RULE [TAUT `P ==> Q /\ R <=> (P ==> Q)
                                            /\ (P ==> R)`
                                          ;FORALL_AND_THM])
                        THEN EXISTS_TAC `CONS y (APPEND ys [P:point])`
                        THEN ASM_REWRITE_TAC []
                        THEN new_was_inside_tac `y:point`
                                cross_change_new_was_inside]
              ;FIRST_X_ASSUM
                (MATCH_MP_TAC o CONJUNCT2
                   o REWRITE_RULE [TAUT `P ==> Q /\ R <=> (P ==> Q)
                                    /\ (P ==> R)`;FORALL_AND_THM]) 
                THEN EXISTS_TAC `CONS y (APPEND ys [P:point])`
                THEN ASM_REWRITE_TAC []
                THEN new_was_inside_tac `y:point`
                  cross_change_new_was_inside]] in
  let lemma1 = prove
    (`!Ps Qs was_inside was_inside'.
        Qs = APPEND Ps [P]
        ==> on_plane A 'a /\ on_plane B 'a /\ on_plane C 'a /\ on_plane C' 'a
        /\ ~on_polyseg Qs A
        /\ (between A B B' \/ between A B' B \/ ~(A = B) /\ B = B')
        /\ on_line A (line_of_half_plane hp)
        /\ on_line B (line_of_half_plane hp)
        /\ on_half_plane hp C /\ on_half_plane hp C'
        ==> ~(?X. on_polyseg [B; B'] X /\ on_polyseg Qs X)
        ==> (between A (HD Qs) B ==> was_inside = was_inside')
        ==> polyseg_crossings (A,B,C) was_inside (ADJACENT Qs)
        = polyseg_crossings (A,B',C') was_inside' (ADJACENT Qs)
          /\ (between A P B
              ==> polyseg_new_was_inside (A,B,C) was_inside (ADJACENT Qs)
                  = polyseg_new_was_inside (A,B',C') was_inside'
                      (ADJACENT Qs))`,
     lemma_prf cross_change_eq cross_change_new_was_inside) in
  let lemma2 = prove
    (`!Ps Qs was_inside was_inside'.
        Qs = APPEND Ps [P]
        ==> on_plane A 'a /\ on_plane B 'a /\ on_plane C 'a /\ on_plane C' 'a
        /\ (!X. MEM X Qs ==> on_plane X 'a)
        /\ ~(?a. on_line A a /\ on_line B' a /\ on_line C' a)
        /\ ~on_polyseg Qs A
        /\ (between A B B' \/ between A B' B \/ ~(A = B) /\ B = B')
        /\ on_line A (line_of_half_plane hp)
        /\ on_line B (line_of_half_plane hp)
        /\ on_half_plane hp C /\ ~on_half_plane hp C'
        ==> ~(?X. on_polyseg [B; B'] X /\ on_polyseg Qs X)
        ==> (between A (HD Qs) B ==> was_inside = ~was_inside')
        ==> polyseg_crossings (A,B,C) was_inside (ADJACENT Qs)
            = polyseg_crossings (A,B',C') was_inside' (ADJACENT Qs)
            /\ (between A P B
                ==> polyseg_new_was_inside (A,B,C) was_inside (ADJACENT Qs)
                = ~polyseg_new_was_inside (A,B',C') was_inside'
                    (ADJACENT Qs))`,
     lemma_prf cross_change_eq2 cross_change_new_was_inside2) in prove 
  (`!was_inside A B B' C C' P Ps Qs.
      Qs = CONS P (APPEND Ps [P])
      /\ on_plane A 'a /\ on_plane B 'a /\ on_plane C 'a /\ on_plane C' 'a
      /\ (!X. MEM X Qs ==> on_plane X 'a)
      /\ ~(?a. on_line A a /\ on_line B a /\ on_line C a)
      /\ ~(?a. on_line A a /\ on_line B' a /\ on_line C' a)
      /\ ~on_polyseg Qs A
      /\ (between A B B' \/ between A B' B \/ ~(A = B) /\ B = B')
      /\ ~(?X. on_polyseg [B; B'] X /\ on_polyseg Qs X)
      ==> ?was_inside'.
            polyseg_crossings (A,B,C) (polyseg_new_was_inside (A,B,C)
                                          was_inside (ADJACENT Qs))
            (ADJACENT Qs)
          = polyseg_crossings (A,B',C') (polyseg_new_was_inside (A,B',C')
                                           was_inside' (ADJACENT Qs))
            (ADJACENT Qs)`,
   SIMP_TAC [] THEN REPEAT GEN_TAC THEN REWRITE_TAC [IMP_CONJ]
     THEN REPEAT DISCH_TAC
     THEN FIRST_ASSUM
     (X_CHOOSE_TAC `hp:half_plane` o
        MATCH_MP UNIQUE_EXISTS_EXISTS o MP
        (SPECL [`A:point`;`B:point`;`C:point`] unique_half_plane))
     THEN ASM_CASES_TAC `on_half_plane hp C'`
     THENL [EXISTS_TAC `was_inside:bool`
               THEN (lemma1
                        |> SPECL [`CONS (P:point) Ps`;`Qs:point list` 
                                 ;`was_inside:bool`;`was_inside:bool`]
                        |> MP_TAC)
               THEN ASM_REWRITE_TAC [APPEND]
               THEN (lemma1 |>
                   SPECL [`CONS (P:point) Ps`;`Qs:point list` 
                         ;`polyseg_new_was_inside (A,B,C) was_inside 
                           (ADJACENT Qs)` 
                         ;`polyseg_new_was_inside (A,B',C') was_inside
                           (ADJACENT Qs)`] |> MP_TAC)
               THEN ASM_REWRITE_TAC [APPEND;HD] THEN SIMP_TAC []
           ;EXISTS_TAC `~was_inside`
             THEN (lemma2
                      |> SPECL [`CONS (P:point) Ps`;`Qs:point list` 
                               ;`was_inside:bool`;`~(was_inside)`]
                      |> MP_TAC)
             THEN ASM_REWRITE_TAC [APPEND]
             THEN (lemma2
                      |> SPECL [`CONS (P:point) Ps`;`Qs:point list` 
                               ;`polyseg_new_was_inside (A,B,C) was_inside 
                                 (ADJACENT Qs)` 
                               ;`polyseg_new_was_inside (A,B',C') (~was_inside) 
                                 (ADJACENT Qs)`] |> MP_TAC)
             THEN ASM_REWRITE_TAC [APPEND;HD] THEN SIMP_TAC []]);;

let cross_nz_intersect = prove
  (`!Ps A B C was_inside. ~(polyseg_crossings (A,B,C) was_inside (ADJACENT Ps) = 0)
        ==> ?Q. on_polyseg Ps Q /\ between A Q B`,
   LIST_INDUCT_TAC2 THEN REWRITE_TAC [ADJACENT_CLAUSES;polyseg_crossings]
     THEN SIMP_TAC [ARITH_RULE `x < 2 ==> (~(x + y = 0) <=> x = 1 \/ ~(y = 0))`
                   ;crossing_lt_2]
     THEN REWRITE_TAC [crossing] THEN unfold_crossing_tac
     THEN REWRITE_TAC [on_polyseg_CONS2] THEN REPEAT STRIP_TAC
     THENL [ASM_MESON_TAC []
           ;FIRST_X_ASSUM (FIRST_MATCH (X_CHOOSE_TAC `Q:point`))
             THEN EXISTS_TAC `Q:point` THEN ASM_REWRITE_TAC []]);;

let on_polyseg_dups = prove
  (`!Ps Qs B P. ALL (\P. P = B) Ps
     ==> (on_polyseg (CONS B (APPEND Ps Qs)) P <=> on_polyseg (CONS B Qs) P)`,
   LIST_INDUCT_TAC THEN ASM_SIMP_TAC [APPEND;ALL;on_polyseg_dup])
      |> REWRITE_RULE [EQ_SYM_EQ];;

(* Try making this on_polyseg_CONS2'. Many proofs will need fixing, but at
   least this doesn't loop on rewriting. *)
let on_polyseg_CONS2'' = REWRITE_RULE [on_polyseg_pair] on_polyseg_CONS2';;

let polyseg_new_was_inside_syms = prove
  (`!segs was_inside. polyseg_new_was_inside (B,A,C) was_inside segs
        = polyseg_new_was_inside (A,B,C) was_inside segs
        /\ polyseg_new_was_inside (A,C,B) was_inside segs
           = polyseg_new_was_inside (A,B,C) was_inside segs`,
   LIST_INDUCT_TAC
     THEN ASM_REWRITE_TAC [polyseg_new_was_inside;new_was_inside_syms]);;

(* The high-level structure of the proof intersect_polyseg_closed is contained
   in this theorem. We induct on the length of Ps, and consider triangles of
   adjacent vertices sharing an edge not in Ps. We can assume that the oddness
   of crossings at the shared edges is preserved until we find that Qs
   intersects a real edge of Ps. *)
let odd_cross_closed_polyseg = theorem
  "!Ps Qs A B.
     LENGTH Qs >= 2
     /\ HD Qs = LAST Qs
     /\ on_plane A 'a /\ on_plane B 'a
     /\ (!X. MEM X Ps ==> on_plane X 'a)
     /\ (!X. MEM X Qs ==> on_plane X 'a)
     /\ ~(A = B) 
     /\ (!C. on_plane C 'a
             /\ ~(?a. on_line A a /\ on_line B a /\ on_line C a)
             ==> ?was_inside. 
               ODD
                 (polyseg_crossings (A,B,C)
                   (polyseg_new_was_inside (A,B,C) was_inside (ADJACENT Qs))
                (ADJACENT Qs)))
   ==> ?X. on_polyseg (CONS B (APPEND Ps [A])) X
           /\ on_polyseg Qs X"
  [fix ["Ps:point list";"Qs:point list"]
  ;assume "LENGTH Qs >= 2 /\ HD Qs = LAST Qs" at [0]
  ;tactics [WF_INDUCT_TAC `LENGTH (Ps:point list)`
             THEN POP_ASSUM (LABEL_TAC "1")]
  ;fix ["A:point";"B:point"]
  ;consider ["Q:point";"Qs':point list"]
     st "Qs = CONS Q (APPEND Qs' [Q])" at [2] proof
     [so consider ["Q:point";"Qs':point list"] st "Qs = CONS Q Qs'" 
         from [0] by [list_CASES;LENGTH_EQ_NIL
                     ;ARITH_RULE `x >= 2 ==> ~(x = 0)`]
         at [2]
     ;so consider ["Q':point";"Qs'':point list"] st "Qs' = APPEND Qs'' [Q']"
       from [0] by [list_CASES_APPEND;LENGTH_EQ_NIL;LENGTH
                   ;ARITH_RULE `x = SUC y /\ x >= 2 ==> ~(y = 0)`] at [3]
     ;hence "LAST Qs = Q'"
       from [2] by [LAST;APPEND_EQ_NIL;NOT_CONS_NIL;LAST_APPEND]
     ;qed from [0;2;3] by [HD]]
  ;set "repeats = FST (BREAK (\P. ~(B = P)) Ps)"
  ;set "rest = SND (BREAK (\P. ~(B = P)) Ps)"
  ;per cases
    [[suppose "EX (\P. ~(B = P)) Ps" at [3]
     ;so consider ["C:point";"Ps':point list"]
       st "rest = CONS C Ps' /\ ~(B = C)"
       at [4;5] by [list_CASES;BREAK_SND_EX;HD]
     ;have "ALL (\P. B = P) repeats" at [6]
       by [ISPECL [`\P. ~(B = P:point)`;`Ps:point list`] BREAK_FST_ALL]
     ;hence "!X. on_polyseg (CONS B (APPEND Ps [A])) X
                   <=> on_polyseg (CONS B (CONS C (APPEND Ps' [A]))) X" proof
       [fix ["X:point"]
       ;have "on_polyseg (CONS B (APPEND Ps [A])) X
              <=> on_polyseg (CONS B (APPEND repeats (APPEND rest [A]))) X"
         by [APPEND_BREAK;APPEND_ASSOC]
       ;hence "... <=> on_polyseg (CONS B (APPEND rest [A])) X"
         from [6] by [on_polyseg_dups]
       ;qed from [4] by [APPEND]]
     ;unfolding from [this]
     ;assume "~on_polyseg Qs A /\ ~on_polyseg Qs B /\ ~on_polyseg Qs C"
       by [on_polyseg;MEM_APPEND;MEM] at [7]
     ;assume "on_plane A 'a /\ on_plane B 'a" at [8]
     ;assume "(!X. MEM X Ps ==> on_plane X 'a)
             /\ (!X. MEM X Qs ==> on_plane X 'a)" at [9]
     ;per cases
       [[suppose "?a. on_line A a /\ on_line B a /\ on_line C a" at [10]
        ;assume "~(A = B)" at [11]
        ;assume "~(?X. on_polyseg [B;C] X /\ on_polyseg Qs X)"
          using (MESON_TAC o mutual_rewrite)
          by [on_polyseg_CONS2'';on_polyseg_pair] at [12]
        ;assume "!C'. on_plane C' 'a
                    /\ ~(?a. on_line A a /\ on_line B a /\ on_line C' a)
                    ==> ?was_inside. 
                          ODD
                            (polyseg_crossings (A,B,C')
                            (polyseg_new_was_inside (A,B,C') was_inside (ADJACENT Qs))
                         (ADJACENT Qs))" at [13]
        ;have "between A B C \/ between A C B" at [14] proof
          [otherwise assume "A = C \/ between B A C"
              by [four] from [5;10;11] at [14]
          ;consider ["C':point"]
            st "on_plane C' 'a
                /\ ~(?a. on_line A a /\ on_line B a /\ on_line C' a)"
            by [plane_triangle] from [8;11] at [15]
          ;so consider ["was_inside:bool"] st
            "ODD (polyseg_crossings (A,B,C')
              (polyseg_new_was_inside (A,B,C') was_inside (ADJACENT Qs))
                (ADJACENT Qs))"
            from [13]
          ;hence "~(polyseg_crossings (A,B,C')
                     (polyseg_new_was_inside (A,B,C') was_inside (ADJACENT Qs))
                       (ADJACENT Qs) = 0)" by [ODD] at [16]
          ;consider ["X:point"] st "between A X B /\ on_polyseg Qs X"
            using K (USE_THEN "16" (MP_TAC o MATCH_MP cross_nz_intersect))
            at [17]
          ;hence "between B X C"
            using ORDER_TAC `{A:point,B,C,X}` from [10;14]
          ;qed from [12;17] by [on_polyseg_pair]
            using MESON_TAC o mutual_rewrite]
        ;hence "on_plane C 'a" at [15] by [g16;g21] from [8]
        ;have "!C'. on_plane C' 'a
                    /\ ~(?a. on_line A a /\ on_line C a /\ on_line C' a)
                    ==> (?was_inside. ODD
                              (polyseg_crossings (A,C,C')
                                 (polyseg_new_was_inside (A,C,C') was_inside
                                    (ADJACENT Qs))
                                (ADJACENT Qs)))" at [16] proof
          [fix ["C':point"]
          ;assume "on_plane C' 'a" at [16]
          ;assume "~(?a. on_line A a /\ on_line C a /\ on_line C' a)" at [17]
          ;obviously by_ncols
            (so consider ["was_inside:bool"] st
               "ODD (polyseg_crossings (A,B,C')
                     (polyseg_new_was_inside (A,B,C') was_inside (ADJACENT Qs))
                     (ADJACENT Qs))"
               from [10;11;13;16] at [18])
          ;obviously by_ncols
            (have "~(?a. on_line A a /\ on_line B a /\ on_line C' a)"
               from [10;11;17] at [19])
          ;have "~(?X. on_polyseg [C; B] X /\ on_polyseg Qs X)"
            using (MESON_TAC o mutual_rewrite) from [2;12]
            by [on_polyseg_pair;BET_SYM] at [20]
          ;hence "?was_inside'.
                    polyseg_crossings (A,B,C')
                       (polyseg_new_was_inside (A,B,C') was_inside
                         (ADJACENT Qs))
                       (ADJACENT Qs)
                    = polyseg_crossings (A,C,C')
                       (polyseg_new_was_inside (A,C,C') was_inside'
                         (ADJACENT Qs))
                       (ADJACENT Qs)"
            from [2;7;8;9;12;14;15;16;17;19]
            using K (MATCH_MP_TAC change_triangle)
          ;qed from [18]]
        ;have "LENGTH Ps' < LENGTH Ps" at [17] proof
          [have "LENGTH Ps = LENGTH (APPEND repeats rest)" by [APPEND_BREAK]
          ;hence "... = LENGTH repeats + SUC (LENGTH Ps')"
            by [LENGTH_APPEND;LENGTH] from [4]
          ;qed using (MAP_EVERY MP_TAC THEN' K ARITH_TAC)]
        ;have "!X. MEM X Ps' ==> on_plane X 'a" at [18] proof
          [have "!X. MEM X rest ==> on_plane X 'a" from [9]
              by [MEM_APPEND;APPEND_BREAK]
          ;qed from [4] by [MEM]]
        ;hence "?X. on_polyseg (CONS C (APPEND Ps' [A])) X
                    /\ on_polyseg Qs X"
          using K (USE_THEN "1" (FIRST_MATCH MATCH_MP_TAC))
          from [1;8;9;14;15;16;17] by [BET_NEQS]
        ;qed by [on_polyseg_CONS2]]
       ;[suppose "~(?a. on_line A a /\ on_line B a /\ on_line C a)" at [10]
        ;have "on_plane C 'a" at [11] proof
          [have "MEM C (APPEND repeats rest)" from [4] by [MEM;MEM_APPEND]
          ;qed from [9] by [APPEND_BREAK]]
        ;so assume "?was_inside. 
                      ODD (polyseg_crossings (A,B,C)
                             (polyseg_new_was_inside (A,B,C) was_inside
                               (ADJACENT Qs))
                            (ADJACENT Qs))" from [10]
        ;so consider ["was_inside:bool"]
           st "ODD (polyseg_crossings (A,B,C)
                      (polyseg_new_was_inside (A,B,C) was_inside
                         (ADJACENT Qs))
                       (ADJACENT Qs))"
           at [12]
        ;assume "~(?X. on_polyseg Qs X /\ between B X C)" by [on_polyseg_CONS2]
        ;hence "polyseg_crossings (B,C,A) 
                  (polyseg_new_was_inside (A,B,C) was_inside (ADJACENT Qs))
                  (ADJACENT Qs) = 0" at [13] 
          using K
          (MATCH_MP_TAC (REWRITE_RULE []
                           (CONV_RULE (ONCE_DEPTH_CONV CONTRAPOS_CONV)
                              cross_nz_intersect)))
        ;hence "EVEN
                 (polyseg_crossings (A,B,C)
                   (polyseg_new_was_inside (A,B,C) was_inside (ADJACENT Qs))
                   (ADJACENT Qs) +
                  polyseg_crossings (A,C,B)
                    (polyseg_new_was_inside (A,B,C) was_inside (ADJACENT Qs))
                    (ADJACENT Qs) +
                 polyseg_crossings (B,C,A)
                   (polyseg_new_was_inside (A,B,C) was_inside (ADJACENT Qs))
                   (ADJACENT Qs))"
          using K (MATCH_MP_TAC
                     (REWRITE_RULE [IMP_IMP] polyseg_crossings_even))
          from [2;7;8;9;10;11;12]
        ;hence "ODD (polyseg_crossings (A,C,B)
                     (polyseg_new_was_inside (A,B,C) was_inside
                        (ADJACENT Qs))
                     (ADJACENT Qs))"
          using (MESON_TAC o mutual_rewrite)
          from [12;13] by [ADD_CLAUSES;EVEN_ADD;NOT_EVEN] at [12]
        ;have "!C'. on_plane C' 'a
                   /\ ~(?a. on_line A a /\ on_line C a /\ on_line C' a)
                   ==> (?was_inside. ODD
                             (polyseg_crossings (A,C,C')
                                (polyseg_new_was_inside (A,C,C') was_inside
                                   (ADJACENT Qs))
                               (ADJACENT Qs)))" at [13] proof
          [fix ["C':point"]
          ;assume "on_plane C' 'a" at [14]
          ;assume "~(?a. on_line A a /\ on_line C a /\ on_line C' a)" at [15]
          ;hence "?was_inside'.
                    polyseg_crossings (A,C,B)
                       (polyseg_new_was_inside (A,C,B) was_inside
                         (ADJACENT Qs))
                       (ADJACENT Qs)
                    = polyseg_crossings (A,C,C')
                       (polyseg_new_was_inside (A,C,C') was_inside'
                         (ADJACENT Qs))
                       (ADJACENT Qs)"
            from [2;7;8;9;10;11;14] by [g11_weak;on_polyseg_dup
                                       ;on_polyseg_sing]
            using K (MATCH_MP_TAC change_triangle)
          ;qed from [12] by [polyseg_new_was_inside_syms]
            using (MESON_TAC o mutual_rewrite)]
        ;(* Repetition. Derive before case-split. *)
         have "LENGTH Ps' < LENGTH Ps" at [14] proof
           [have "LENGTH Ps = LENGTH (APPEND repeats rest)"
               by [APPEND_BREAK]
           ;hence "... = LENGTH repeats + SUC (LENGTH Ps')"
             by [LENGTH_APPEND;LENGTH] from [4]
           ;qed using (MAP_EVERY MP_TAC THEN' K ARITH_TAC)]
        ;have "!X. MEM X Ps' ==> on_plane X 'a" at [15] proof
          [have "!X. MEM X rest ==> on_plane X 'a" from [9]
              by [MEM_APPEND;APPEND_BREAK]
          ;qed from [4] by [MEM]]
        ;hence "?X. on_polyseg (CONS C (APPEND Ps' [A])) X
                    /\ on_polyseg Qs X"
          using K (USE_THEN "1" (FIRST_MATCH MATCH_MP_TAC))

          
          from [8;9;10;11;13;14;15] by [g11_weak]
        ;qed by [on_polyseg_CONS2]]]]
    ;[suppose "~EX (\P. ~(B = P)) Ps"
     ;hence "ALL (\P. B = P) Ps" using (MESON_TAC o mutual_rewrite)
       by [NOT_EX]
     ;hence "!X. on_polyseg (CONS B (APPEND Ps [A])) X <=> on_polyseg [B;A] X" 
       by [on_polyseg_dups]
     ;unfolding from [this] by [on_polyseg_pair;BET_SYM]
     ;assume "~(A = B) /\ on_plane A 'a /\ on_plane B 'a"
     ;so consider ["C:point"]
       st "on_plane C 'a
            /\ ~(?a. on_line A a /\ on_line B a /\ on_line C a)"
       by [plane_triangle]
     ;so assume "?was_inside. 
                     ODD (polyseg_crossings (A,B,C)
                           (polyseg_new_was_inside (A,B,C) was_inside 
                             (ADJACENT Qs))
                           (ADJACENT Qs))"
     ;so consider ["was_inside:bool"] st
       "~(polyseg_crossings (A,B,C)
            (polyseg_new_was_inside (A,B,C) was_inside
                (ADJACENT Qs))
            (ADJACENT Qs) = 0)" at [3] by [ODD]
     ;qed by [cross_nz_intersect;ODD]
       using K (USE_THEN "3" (MP_TAC o MATCH_MP cross_nz_intersect))]]];;

(* The concluding theorem for polygonal segments. *)
let intersect_polyseg_closed = theorem
  "!P1 P2 Ps Q1 Q2 Qs X 'a. 
   on_plane P1 'a /\ on_plane P2 'a /\ on_plane Q1 'a /\ on_plane Q2 'a 
   /\ (!X. MEM X Ps ==> on_plane X 'a) /\ (!X. MEM X Qs ==> on_plane X 'a) 
   /\ ~(?a. on_line P1 a /\ on_line P2 a /\ on_line Q1 a)
   /\ ~(?a. on_line Q1 a /\ on_line Q2 a /\ on_line P1 a)
   /\ between P1 X P2 /\ between Q1 X Q2
   /\ P1 = LAST (CONS P2 Ps) /\ Q1 = LAST (CONS Q2 Qs)
   ==> ?Y. on_polyseg (CONS P2 Ps) Y /\ on_polyseg (CONS Q1 (CONS Q2 Qs)) Y
           \/ on_polyseg (CONS P1 (CONS P2 Ps)) Y /\ on_polyseg (CONS Q2 Qs) Y"
  [unfolding by [EXISTS_OR_THM]
  ;fix ["P1:point";"P2:point";"Ps:point list"
       ;"Q1:point";"Q2:point";"Qs:point list"
       ;"X:point";"'a:plane"]
  ;assume "on_plane P1 'a /\ on_plane P2 'a
           /\ on_plane Q1 'a /\ on_plane Q2 'a" at [0]
  ;assume "(!X. MEM X Ps ==> on_plane X 'a)
           /\ (!X. MEM X Qs ==> on_plane X 'a)" at [1]
  ;assume "~(?a. on_line P1 a /\ on_line P2 a /\ on_line Q1 a)" at [2]
  ;assume "~(?a. on_line Q1 a /\ on_line Q2 a /\ on_line P1 a)" at [3]
  ;assume "between P1 X P2 /\ between Q1 X Q2" at [4]
  ;hence "~(P1 = P2) /\ ~(Q1 = Q2)" at [5] by [BET_NEQS]
  ;obviously (by_ncols o Di.conjuncts)
    (have "!was_inside C. crossing (P1,P2,C) was_inside Q1 Q2 = 1"
       from [3;4] by [crossing;g21] at [6])
  ;hence "!was_inside C.
            polyseg_crossings (P1,P2,C) was_inside 
              (ADJACENT (CONS Q1 (CONS Q2 Qs))) > 0"
     by [polyseg_crossings;ADJACENT_CONS;ARITH_RULE `1 + x = y ==> y > 0`]
     at [7]
  ;per cases
    [[suppose "?was_inside C.
                 polyseg_crossings (P1,P2,C) was_inside 
                   (ADJACENT (CONS Q1 (CONS Q2 Qs))) > 1"
     ;so consider ["was_inside:bool";"C:point"]
       st "polyseg_crossings (P1,P2,C) was_inside 
              (ADJACENT (CONS Q1 (CONS Q2 Qs))) > 1" at [8]
     ;have "~(Qs = [])" proof
       [otherwise assume "Qs = []"
       ;qed from [6;8] by [ADJACENT_CLAUSES;polyseg_crossings
                         ;ADD_CLAUSES;GT;LT;LT_REFL]
         using (MESON_TAC o mutual_rewrite)]
     ;so consider ["Q3:point";"Qs':point list"]
       st "CONS Q3 Qs' = Qs" at [9]
       by [list_CASES;APPEND_EQ_NIL;NOT_CONS_NIL]
     ;have "?was_inside.
             ~(polyseg_crossings (P1,P2,C) was_inside
               (ADJACENT (CONS Q2 (CONS Q3 Qs'))) = 0)" at [10] proof
       [hence "polyseg_crossings (P1,P2,C) was_inside
                (ADJACENT (CONS Q1 (CONS Q2 Qs)))
               = 1 + polyseg_crossings (P1,P2,C) 
                      (new_was_inside (P1,P2,C) was_inside Q1 Q2)
                      (ADJACENT (CONS Q2 Qs))"
           from [6] by [polyseg_crossings;ADJACENT_CONS]
       ;take ["(new_was_inside (P1,P2,C) was_inside Q1 Q2)"]
       ;qed by [ARITH_RULE `x > 1 /\ x = 1 + y ==> ~(y = 0)`]
         from [8;9]]
     ;qed using K (USE_THEN "10"
                     (CHOOSE_THEN (MP_TAC o MATCH_MP cross_nz_intersect)))
       from [9] by [on_polyseg_CONS2]]
    ;[suppose "!was_inside C.
                  polyseg_crossings (P1,P2,C) was_inside 
                 (ADJACENT (CONS Q1 (CONS Q2 Qs))) = 1"
     ;hence "!was_inside C.
               ODD (polyseg_crossings (P1,P2,C) was_inside 
                     (ADJACENT (CONS Q1 (CONS Q2 Qs))))"
       at [8] by [ODD;ONE]
     ;assume "P1 = LAST (CONS P2 Ps) /\ Q1 = LAST (CONS Q2 Qs)" at [9]
     ;hence "~(Ps = [])" by [LAST] from [5]
     ;so consider ["PL:point";"Ps':point list"]
       st "Ps = APPEND Ps' [PL]"
       by [list_CASES_APPEND] at [10]
     ;unfolding from [this]
     ;hence "PL = P1" from [9]
       by [LAST_APPEND;LAST;NOT_CONS_NIL;APPEND_EQ_NIL]
     ;unfolding from [this]
     ;tactics [DISJ1_TAC THEN MATCH_MP_TAC odd_cross_closed_polyseg]
     ;thus "!Y. MEM Y Ps' ==> on_plane Y 'a" proof
       [have "!Y. MEM Y (APPEND Ps' [PL]) ==> on_plane Y 'a" from [1;10]
       ;qed by [MEM_APPEND]]
     ;unfolding from [this]
     ;thus "LAST (CONS Q2 Qs) = Q1" from [9]
     ;unfolding from [this]
     ;have "LAST (CONS Q1 (CONS Q2 Qs)) = Q1" from [9] by [LAST;NOT_CONS_NIL] 
     ;unfolding from [this]
       by [LENGTH;ONE;TWO;GE;LE_SUC;LE_0;HD;LAST;NOT_CONS_NIL]
     ;have "!C. ?was_inside. 
                 ODD
                  (polyseg_crossings (P1,P2,C)
                    (polyseg_new_was_inside (P1,P2,C) was_inside
                    (ADJACENT (CONS Q1 (CONS Q2 Qs))))
                  (ADJACENT (CONS Q1 (CONS Q2 Qs))))" proof
       [fix ["C:point"]
       ;take ["T"]
       ;qed from [8]]
     ;qed from [0;1;5] by [MEM]]]
    by [ARITH_RULE `x > 0 ==> (~(x > 1) <=> x = 1)`] from [7]];;

(* Slightly more elegant version, though not as useful given our focus on
 *triangles* *)
let intersect_polyseg_closed' =
  let lemma = prove
    (`between P1 X P2 /\ between Q1 X Q2
      ==> (~(?a. on_line P1 a /\ on_line P2 a /\ on_line Q1 a /\ on_line Q2 a)
           <=> ~(?a. on_line P1 a /\ on_line P2 a /\ on_line Q1 a)
                /\ ~(?a. on_line Q1 a /\ on_line Q2 a /\ on_line P1 a))`,
     DISCH_TAC THEN EQ_TAC THENL
       [DISCH_TAC THEN CONJ_TAC THEN REFUTE_THEN ASSUME_TAC
           THEN discover_tac (by_cols o Di.conjuncts) ASM_MESON_TAC
       ;ASM_MESON_TAC []]) in
  prove
    (`!P1 P2 Ps Q1 Q2 Qs X 'a. 
        on_plane P1 'a /\ on_plane P2 'a /\ on_plane Q1 'a /\ on_plane Q2 'a 
        /\ (!X. MEM X Ps ==> on_plane X 'a) /\ (!X. MEM X Qs ==> on_plane X 'a)
        /\ ~(?a. on_line P1 a /\ on_line P2 a /\ on_line Q1 a /\ on_line Q2 a)
        /\ between P1 X P2 /\ between Q1 X Q2 
        /\ P1 = LAST (CONS P2 Ps) /\ Q1 = LAST (CONS Q2 Qs) 
        ==> ?Y. on_polyseg (CONS P2 Ps) Y
                /\ on_polyseg (CONS Q1 (CONS Q2 Qs)) Y
                \/ on_polyseg (CONS P1 (CONS P2 Ps)) Y
                   /\ on_polyseg (CONS Q2 Qs) Y`,
     REPEAT GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC intersect_polyseg_closed
       THEN MAP_EVERY EXISTS_TAC [`X:point`;`'a:plane`]
       THEN ASM_MESON_TAC [lemma]);;

(* If X lies outside a polygonal segment, and we cast a ray through a point Y
   on the polygonal segment, then we can take the first point of intersection
   along the ray. *)
let ray_cast =
  let ray_cast_lemma = theorem 
    "!P Q X Y. ~(on_polyseg [P;Q] X) /\ on_polyseg [P;Q] Y
                ==> ?Z. on_polyseg [P;Q] Z /\ (between X Z Y \/ Y = Z)
                /\ ~(?R. between X R Z /\ on_polyseg [P;Q] R)"
    [fix ["P:point";"Q:point";"X:point";"Y:point"]
    ;assume "~on_polyseg [P;Q] X /\ on_polyseg [P;Q] Y" at [0;1]
    ;have "P = Y \/ Q = Y \/ between P Y Q"
      by [on_polyseg;ADJACENT;ZIP;BUTLAST;TAIL
         ;NOT_CONS_NIL;PAIR_EQ;NOT_IN_EMPTY;MEM]
      from [1] at [2] using (MESON_TAC o mutual_simp)
    ;per cases
      [[suppose "P = Q" at [3]
       ;take ["P"]
       ;thus "on_polyseg [P;Q] P" by [on_polyseg;MEM]
       ;have "P = Y" from [1;3] by [on_polyseg_dup;on_polyseg_sing]
       ;qed from [3] by [BET_NEQS;g11_weak;on_polyseg_dup;on_polyseg_sing]]
      ;[suppose "~(P = Q)" at [3]
       ;consider ["a:line"] st "on_line P a /\ on_line Q a /\ on_line Y a"
         from [2] at [4] by [g11_weak;g21]
       ;per cases
         [[suppose "on_line X a" at [5]
          ;have "~(P = X) /\ ~(Q = X) /\ ~(between P X Q)" from [0]
            by [on_polyseg_pair]
            at [6] using (MESON_TAC o mutual_simp)
          ;(* HORRIBLE REPETITION. NEED WLOG *)
           per cases
             [[suppose "between P Q X" at [7]
              ;take ["Q"]
              ;thus "on_polyseg [P;Q] Q 
                     /\ (?a. on_line X a /\ on_line Y a /\ on_line Q a)"
                from [3;4;5] by [on_polyseg;MEM]
              ;thus "between X Q Y \/ Y = Q" 
                from [2;4;5;7] using ORDER_TAC `{P:point,Q,X,Y}`
              ;assume "?R. between X R Q /\ on_polyseg [P;Q] R"
              ;so consider ["R:point"] st "between X R Q /\ on_polyseg [P;Q] R" 
                at [8]
              ;hence "P = R \/ Q = R \/ between P R Q"
                by [on_polyseg_pair]
              ;qed using ORDER_TAC `{P:point,Q,R,X}` from [4;5;7;8]]
             ;[suppose "between Q P X" at [7]
              ;take ["P:point"]
              ;thus "on_polyseg [P;Q] P
                   /\ (?a. on_line X a /\ on_line Y a /\ on_line P a)" 
                from [3;4;5] by [on_polyseg;MEM]
              ;thus "between X P Y \/ Y = P"
                from [2;4;5;7] using ORDER_TAC `{P:point,Q,X,Y}`
              ;assume "?R. between X R P /\ on_polyseg [P;Q] R"
              ;so consider ["R:point"] st "between X R P /\ on_polyseg [P;Q] R"
                at [8]
              ;hence "P = R \/ Q = R \/ between P R Q"
                by [on_polyseg_pair]
              ;qed using ORDER_TAC `{P:point,Q,R,X}` from [4;5;7;8]]]
             from [3;4;5;6] using ORDER_TAC `{P:point,Q,X}`]
         ;[suppose "~on_line X a" at [5]
          ;take ["Y:point"]
          ;unfolding from [1] by [g11_weak]
          ;assume "?R. between X R Y /\ on_polyseg [P;Q] R"
          ;so consider ["R:point"] st
            "between X R Y /\ on_polyseg [P;Q] R" at [6]
          ;hence "P = R \/ Q = R \/ between P R Q"
            by [on_polyseg_pair]
            using (MESON_TAC o mutual_simp)
          ;obviously (by_cols o with_subst o Di.split)
            (hence "?a. on_line P a /\ on_line Q a /\ on_line X a"
               from [3;4;5;6])
          ;qed by [g12] from [3;4;5]]]]]] in
  theorem "!Ps X Y. ~(on_polyseg Ps X) /\ on_polyseg Ps Y
                    ==> ?Z. on_polyseg Ps Z /\ (between X Z Y \/ Y = Z)
                    /\ ~(?R. between X R Z /\ on_polyseg Ps R)"
    [LIST_INDUCT_TAC2 THEN TRY (POP_ASSUM (LABEL_TAC "0")) parts
        [[thus thesis by [on_polyseg_nil]]
        ;[thus thesis using
             K (ONCE_REWRITE_TAC [GSYM (SPECL [`P:point`;`[]:point list`]
                                          on_polyseg_dup)])
             by [ray_cast_lemma]]
        ;[fix ["X:point";"Y:point"]
         ;assume "~on_polyseg (CONS x (CONS y ys)) X
                  /\ on_polyseg (CONS x (CONS y ys)) Y" at [1]
         ;hence "~(on_polyseg [x;y] X) /\ ~(on_polyseg (CONS y ys) X)
                 /\ (on_polyseg [x;y] Y \/ on_polyseg (CONS y ys) Y)"
           at [2;3;4] using MESON_TAC by [on_polyseg_CONS2']
         ;per cases
           [[suppose "on_polyseg [x;y] Y"
            ;so consider ["Z:point"]
              st "on_polyseg [x;y] Z /\ (between X Z Y \/ Y = Z)
                  /\ ~(?R. between X R Z /\ on_polyseg [x;y] R)"
              at [5;6;7] using K (MATCH_MP_TAC ray_cast_lemma) from [2]
            ;per cases
              [[suppose "(?R. between X R Z /\ on_polyseg (CONS x (CONS y ys)) R)"
               ;so consider ["R:point"]
                 st "between X R Z /\ on_polyseg (CONS x (CONS y ys)) R" at [8]
               ;hence "on_polyseg (CONS y ys) R" from [7]
                 using MESON_TAC by [on_polyseg_CONS2']
               ;so consider ["Z':point"]
                 st "on_polyseg (CONS y ys) Z' /\ (between X Z' R \/ R = Z')
                    /\ ~(?R. between X R Z' /\ on_polyseg (CONS y ys) R)"
                 using K (USE_THEN "0" MATCH_MP_TAC)
                 at [9;10;11] from [3]
               ;obviously (by_cols o Di.split)
                 (hence "(?a. on_line R a /\ on_line X a /\ on_line Y a
                            /\ on_line Z a /\ on_line Z' a)"
                    at [12] from [6;8;10])
               ;take ["Z'"]
               ;hence "on_polyseg (CONS x (CONS y ys)) Z'"
                 using MESON_TAC from [9] by [on_polyseg_CONS2']
               ;thus "between X Z' Y \/ Y = Z'" from [6;7;8;10;11;12]
                 using ORDER_TAC `{R:point,X,Y,Z,Z'}`
               ;assume "?S. between X S Z' /\ on_polyseg (CONS x (CONS y ys)) S"
               ;so consider ["S:point"] st
                 "between X S Z' /\ on_polyseg (CONS x (CONS y ys)) S" at [13]
               ;hence "between X S Z" from [8;10;11;12] using
                 ORDER_TAC `{R:point,S,X,Z,Z'}`
               ;qed from [7;11;13] by [on_polyseg_CONS2']]
              ;[suppose "~(?R. between X R Z
                               /\ on_polyseg (CONS x (CONS y ys)) R)"
               ;take ["Z"]
               ;qed from [5;6;7] using MESON_TAC by [on_polyseg_CONS2']]]]
           ;[suppose "~on_polyseg [x;y] Y"
             (* Horrific repetition. *)
            ;so consider ["Z:point"]
              st "on_polyseg (CONS y ys) Z /\ (between X Z Y \/ Y = Z)
                  /\ ~(?R. between X R Z /\ on_polyseg (CONS y ys) R)"
              at [5;6;7] using K (USE_THEN "0" MATCH_MP_TAC) from [3;4]
            ;per cases
              [[suppose "(?R. between X R Z
                              /\ on_polyseg (CONS x (CONS y ys)) R)"
               ;so consider ["R:point"]
                 st "between X R Z /\ on_polyseg (CONS x (CONS y ys)) R" at [8]
               ;hence "on_polyseg [x;y] R" from [7]
                 using MESON_TAC by [on_polyseg_CONS2']
               ;so consider ["Z':point"]
                 st "on_polyseg [x;y] Z' /\ (between X Z' R \/ R = Z')
                     /\ ~(?R. between X R Z' /\ on_polyseg [x;y] R)"
                 using K (MATCH_MP_TAC ray_cast_lemma)
                 at [9;10;11] from [2]
               ;obviously (by_cols o Di.split)
                 (hence "(?a. on_line R a /\ on_line X a /\ on_line Y a
                              /\ on_line Z a /\ on_line Z' a)"
                    at [12] from [6;8;10])
               ;take ["Z'"]
               ;hence "on_polyseg (CONS x (CONS y ys)) Z'"
                 using MESON_TAC from [9] by [on_polyseg_CONS2']
               ;thus "between X Z' Y \/ Y = Z'" from [6;7;8;10;11;12]
                 using ORDER_TAC `{R:point,X,Y,Z,Z'}`
               ;assume "?S. between X S Z'
                            /\ on_polyseg (CONS x (CONS y ys)) S"
               ;so consider ["S:point"] st
                 "between X S Z' /\ on_polyseg (CONS x (CONS y ys)) S" at [13]
               ;hence "between X S Z" from [8;10;11;12] using
                 ORDER_TAC `{R:point,S,X,Z,Z'}`
               ;qed from [7;11;13] by [on_polyseg_CONS2']]
              ;[suppose "~(?R. between X R Z
                               /\ on_polyseg (CONS x (CONS y ys)) R)"
               ;take ["Z"]
               ;qed from [5;6;7] using MESON_TAC by [on_polyseg_CONS2']]]]]]]];;

(* If we move the vertex B further along AB, then all interior points of the
   original triangle as well as the old side AB all lie inside the new
   triangle. *)
let sub_triangle = theorem
  "!A A' B C P. in_triangle (A,A',C) P /\ between A A' B
                ==> in_triangle (A,B,C) P"
  [fix ["A:point";"A':point";"B:point";"C:point";"P:point"]
  ;assume "in_triangle (A,A',C) P /\ between A A' B" at [0]
  ;so consider ["Q:point"] st "between A' Q C /\ between A P Q"
    at [1] by [tri_cut3] 
  ;obviously (by_ncols o add_in_triangle o Di.conjuncts)
    (hence "in_triangle (A,B,C) Q"
       by [in_triangle2;g21;tri_syms] from [0])
  ;qed from [1] by [on_triangle_bet_in_triangle;on_triangle]];;

(* Primarily a lemma for squeeze. If you're on the line of a triangle's side,
   then you're not in the triangle. *)
let on_line_side_not_in_triangle = theorem
  "!A B C P. (?a. on_line A a /\ on_line B a /\ on_line P a)
              ==> ~in_triangle (A,B,C) P"
  [fix ["A:point";"B:point";"C:point";"P:point"]
  ;assume "in_triangle (A,B,C) P
           /\ ?a. on_line A a /\ on_line B a /\ on_line P a" at [0;1]
  ;consider ["hp:half_plane"]
     st "on_line A (line_of_half_plane hp)
         /\ on_line B (line_of_half_plane hp)
         /\ on_half_plane hp C
         /\ on_half_plane hp P"
     from [0] at [2;3;4;5] by [in_triangle]
  ;obviously (by_neqs o add_in_triangle)
    (have "on_line P (line_of_half_plane hp)" by [g12] from [0;1;2;3])
  ;qed by [in_triangle;half_plane_not_on_line] from [5]];;

(* The crucial theorem to navigate around a polygon. Here, we squeeze through
   a triangular crack, avoiding an arbitrary polygonal segment. 
   A version of this theorem with a very similar proof is in polygon_unused,
   but it uses a stronger premise to put the final segment from s to goal
   between a vertex of the polyseg. This would be needed to split one simple
   polygon into two, but since we're not needing such a result anymore, we use
   the following version of squeeze with the weaker premise. *)
(* We really should drop the assumption of non-collinearity. It makes proofs
   more annoying. *)
let squeeze = theorem
  "!P start goal 'a polyseg.
      ~(?a. on_line P a /\ on_line start a /\ on_line goal a)
      /\ on_plane P 'a /\ on_plane start 'a /\ on_plane goal 'a
      /\ (!X. MEM X polyseg ==> on_plane X 'a)
      /\ ~on_polyseg polyseg P
      /\ (!X. between P X start ==> ~on_polyseg polyseg X)
      /\ (!X. between P X goal ==> ~on_polyseg polyseg X)
      ==> ?s. between P s start
              /\ !X. in_triangle (P,s,goal) X ==> ~on_polyseg polyseg X"
  [fix ["P:point";"start:point";"goal:point";"'a:plane"]
  ;assume "~(?a. on_line P a /\ on_line start a /\ on_line goal a)" at [0]
  ;assume "on_plane P 'a /\ on_plane start 'a /\ on_plane goal 'a" at [1]
  ;hence ("!'b. on_plane P 'b /\ on_plane start 'b /\ on_plane goal 'b
              ==> 'b = 'a") at [2] from [0;1] by [g15]
  ;MATCH_MP_TAC list_INDUCT THEN CONJUNCTS_TAC parts
    [[unfolding by [on_polyseg_nil]
     ;qed from [0] by [g11_weak;three]]
    ;[fix ["Q:point";"Qs:point list"]
     ;assume "(!X. MEM X (CONS Q Qs) ==> on_plane X 'a)
                   /\ ~on_polyseg (CONS Q Qs) P" at [3]
     ;so assume
       "?s. between P s start
            /\ (!X. in_triangle (P,s,goal) X ==> ~on_polyseg Qs X)"
       by [MEM;on_polyseg_CONS]
     ;so consider ["s:point"]
       st "between P s start /\ !X. in_triangle (P,s,goal) X
               ==> ~on_polyseg Qs X" at [4]
     ;per cases
       [[suppose "Qs = []"
        ;unfolding from [this] by [on_polyseg_sing]
        ;assume "in_triangle (P,s,goal) Q" from [4]
        ;so consider ["s':point"]
          st "between s s' P /\ between goal Q s'"
          using K (MATCH_MP_TAC tri_cut3)
          at [6] by [in_triangle]
        ;hence "between P s' start" at [7] from [4]
          using ORDER_TAC `{P:point,s,s',start}`
        ;qed from [6] by [on_triangle;in_triangle_not_on_triangle;BET_SYM]]
       ;[suppose "~(Qs = [])"
        ;so consider ["R:point";"Rs:point list"]
          st "Qs = CONS R Rs" at [5] by [type_cases "list"]
        ;per cases
          [[suppose "?a. on_line goal a /\ on_line Q a /\ on_line R a" at [6]
           ;assume "?X. in_triangle (P,s,goal) X
                        /\ (Q = X \/ between Q X R)"
             from [4;5] by [on_polyseg_CONS2]
           ;so consider ["X:point"]
             st "in_triangle (P,s,goal) X
                 /\ (Q = X \/ between Q X R)" at [7]
           ;so consider ["s':point"]
             st "between goal X s' /\ between P s' s"
             from [6] by [tri_cut3;tri_syms] at [8]
           ;hence "between P s' start" using ORDER_TAC `{P:point,s,s',start}`
             from [4] at [9]
           ;have "!Y. in_triangle (P,s',goal) Y
                    ==> ~(Q = Y) /\ ~between Q Y R" proof
             [fix ["Y:point"]
             ;assume "in_triangle (P,s',goal) Y" at [10]
             ;otherwise assume "Q = Y \/ between Q Y R"
             ;obviously (by_cols o with_subst o Di.split)
               (hence "?a. on_line goal a /\ on_line s' a /\ on_line Y a"
                  from [6;7;8])
             ;qed from [10] by [on_line_side_not_in_triangle;tri_syms]]
           ;qed from [4;5;8;9] by [sub_triangle;on_polyseg_CONS2]]
          ;[suppose "~(?a. on_line goal a /\ on_line Q a /\ on_line R a)"
               at [6]
           ;assume "!X. between P X start
                        ==> ~on_polyseg (CONS Q Qs) X" at [7]
           ;assume "!X. between P X goal
                        ==> ~on_polyseg (CONS Q Qs) X" at [8]
           ;per cases
             [[suppose "in_triangle (P,s,goal) Q" at [9]
              ;so consider ["s':point"]
                st "between s s' P /\ between goal Q s'"
                using K (MATCH_MP_TAC tri_cut3)
                at [10] by [in_triangle]
              ;take ["s'"]
              ;hence "between P s' start" at [11] from [4]
                using ORDER_TAC `{P:point,s,s',start}`
              ;fix ["X:point"]
              ;assume "in_triangle (P,s',goal) X" at [12]
              ;hence "~(Q = X) /\ ~on_polyseg Qs X"
                from [4;10] by [on_triangle;in_triangle_not_on_triangle
                               ;BET_SYM;sub_triangle] at [13]
              ;so assume "between Q X R" at [14] from [5] by [on_polyseg_CONS2]
              ;have "~in_triangle (P,s',goal) R"
                at [15] from [4;5;10] by [MEM;on_polyseg;sub_triangle;BET_SYM]
              ;have "~on_triangle (P,s',goal) R" at [16] proof
                [unfolding by [on_triangle;DE_MORGAN_THM]
                ;thus "~between P R goal /\ ~between P R start"
                  at [16] from [5;7;8] by [MEM;on_polyseg]
                ;hence "~between P R s'" at [17] proof
                  [assume "between P R s'"
                  ;qed using ORDER_TAC `{P:point,R,start,s,s'}`
                    from [4;10;16]]
                ;obviously (by_ncols o Di.conjuncts)
                  (have "~between goal R s' /\ ~(R = s') /\ ~(R = goal)"
                     from [6;10] by [g11_weak;g21])
                ;qed from [3;5] by [MEM;on_polyseg;BET_SYM]]
              ;obviously (by_planes o add_in_triangle)
                (have "on_plane s' 'a /\ on_plane R 'a"
                   from [2;3;5;11;12] by [MEM;on_polyseg])
              ;so consider ["Y:point"] st
                "on_triangle (P,s',goal) Y /\ between X Y R" at [17]
                by [in_triangle_simple_closed] from [1;12;15;16]
              ;hence "between Q Y R" at [18]
                using ORDER_TAC `{Q:point,R,X,Y}` from [14]
              ;have "on_polyseg (CONS Q Qs) Y" proof
                [unfolding from [5] by [on_polyseg_CONS2];qed]
              ;obviously (by_ncols o Di.conjuncts)
                (hence
                   "~between P Y goal /\ ~between P Y start
                    /\ ~(Y = P) /\ ~(Y = goal)"
                   at [19] from [3;6;7;8;18] by [MEM;on_polyseg;g11_weak])
              ;have "~between P Y s'" proof
                [otherwise assume "between P Y s'"
                ;qed using ORDER_TAC `{P:point,s',Y,start}` from [11;19]]
              ;hence "between s' Y goal \/ Y = s'"
                from [17;19] by [on_triangle]
              ;obviously (by_cols o with_subst o Di.split)
                (hence "?a. on_line goal a /\ on_line s' a /\ on_line X a" 
                   from [10;14;17;18])
              ;qed from [12] by [on_line_side_not_in_triangle;tri_syms]]
             ;[suppose "~in_triangle (P,s,goal) Q" at [9]
              ;take ["s"]
              ;thus "between P s start" from [4]
              ;fix ["X:point"]
              ;assume "in_triangle (P,s,goal) X" at [10]
              ;so assume "between Q X R"
                at [11] from [4;5;9] by [on_polyseg_CONS2]
              ;have "~in_triangle (P,s,goal) R"
                at [12] from [4;5] by [MEM;on_polyseg]
              ;have "~between P Q s" at [13] proof
                [otherwise assume "between P Q s"
                ;hence "between P Q start"
                  from [4] using ORDER_TAC `{P:point,Q,start,s}`
                ;qed from [5;7;8] by [MEM;on_polyseg]]
              ;have "~between P R s" at [14] proof
                [otherwise assume "between P R s"
                ;hence "between P R start"
                  from [4] using ORDER_TAC `{P:point,R,start,s}`
                ;qed from [5;7;8] by [MEM;on_polyseg]]
              ;have "~(Q = s) /\ ~(R = s) /\ ~(Q = P) /\ ~(R = P)
                     /\ ~(Q = goal) /\ ~(R = goal)
                     /\ ~between P Q goal /\ ~between P R goal"
                at [15] from [3;4;5;6;7;8]
                by [MEM;on_polyseg;BET_SYM;g11_weak]
              ;obviously (by_planes o add_in_triangle o Di.conjuncts)
                (hence "on_plane s 'a /\ on_plane Q 'a /\ on_plane R 'a"
                   at [16] from [2;3;4;5;10] by [MEM])
              ;so consider ["Y:point"] st
                "(on_triangle (P,s,goal) Q
                 \/ on_triangle (P,s,goal) Y /\ between X Y Q)"
                from [1;9;10] by [in_triangle_simple_closed;BET_SYM]
              ;hence "between s Q goal
                      \/ on_triangle (P,s,goal) Y /\ between X Y Q"
                at [17] from [13;15] by [on_triangle]
              ;consider ["Z:point"] st
                "(on_triangle (P,s,goal) R
                 \/ on_triangle (P,s,goal) Z /\ between X Z R)"
                from [1;10;12;16] by [in_triangle_simple_closed;BET_SYM]
              ;hence "between s R goal
                      \/ on_triangle (P,s,goal) Z /\ between X Z R"
                at [18] from [14;15] by [on_triangle]
              ;have "!U. between Q U R /\ on_triangle (P,s,goal) U
                         ==> between s U goal" at [19] proof
                [fix ["U:point"]
                ;assume "between Q U R /\ on_triangle (P,s,goal) U" at [19]
                ;have "~between P U s" at [20] proof
                  [otherwise assume "between P U s"
                  ;hence "between P U start"
                    using ORDER_TAC `{P:point,s,start,U}` from [4]
                  ;qed from [5;7;8;19] by [on_polyseg_CONS2]]
                ;obviously (by_ncols o Di.conjuncts)
                  (have "~(P = U) /\ ~(goal = U) /\ ~(s = U)
                         /\ ~between P U start /\ ~between P U goal" 
                     from [3;4;5;6;7;8;19] by [on_polyseg_CONS2;g11_weak])
                ;qed from [19;20] by [on_triangle]]
              ;per cases
                [[suppose "between s Q goal /\ between s R goal"
                 ;obviously (by_eqs o add_in_triangle o Di.conjuncts)
                   qed from [10;11] by [BET_NEQS]]
                ;[suppose "between s Q goal /\ on_triangle (P,s,goal) Z 
                           /\ between X Z R" at [20]
                 ;hence "between Q Z R"
                   using ORDER_TAC `{Q:point,R,X,Z}` at [21] from [11]
                 ;hence "between s Z goal" from [19;20]
                 ;obviously (by_eqs o add_in_triangle o Di.conjuncts)
                   qed from [10;20;21] by [BET_NEQS]]
                (* Symmetric for R and Z*)
                ;[suppose "between s R goal /\ on_triangle (P,s,goal) Y
                           /\ between X Y Q" at [20]
                 ;hence "between Q Y R"
                   using ORDER_TAC `{Q:point,R,X,Y}` at [21] from [11]
                 ;hence "between s Y goal" from [19;20]
                 ;obviously (by_eqs o add_in_triangle o Di.conjuncts)
                   qed from [10;20;21] by [BET_NEQS]]
                ;[suppose "on_triangle (P,s,goal) Y /\ between X Y Q
                           /\ on_triangle (P,s,goal) Z /\ between X Z R"
                     at [20]
                 ;hence "between Q Z R"
                   using ORDER_TAC `{Q:point,R,X,Z}` at [21] from [11]
                 ;hence "between s Z goal" at [22] from [19;20]
                 ;have "between Q Y R"
                   using ORDER_TAC `{Q:point,R,X,Y}` from [11;20]
                 ;hence "between s Y goal" from [19;20]
                 ;clearly (by_eqs o add_in_triangle o Di.conjuncts)
                   (hence "Y = Z" from [10;11;20;22])
                 ;qed using ORDER_TAC `{Q:point,R,X,Y,Z}`
                   from [11;20;21]]]
                from [17;18]]]]]]]]]];;

(* We only need the following corollary. *)
let squeeze' = theorem
  "!P start goal 'a polyseg.
      ~(?a. on_line P a /\ on_line start a /\ on_line goal a)
      /\ on_plane P 'a /\ on_plane start 'a /\ on_plane goal 'a
      /\ (!X. MEM X polyseg ==> on_plane X 'a)
      /\ ~on_polyseg polyseg P
      /\ (!X. between P X start ==> ~on_polyseg polyseg X)
      /\ (!X. between P X goal ==> ~on_polyseg polyseg X)
      ==> (?s. between P s start
               /\ !X. between s X goal  ==> ~on_polyseg polyseg X)"
  [fix ["P:point";"start:point";"goal:point"
       ;"'a:plane";"polyseg:point list"]
  ;assume "~(?a. on_line P a /\ on_line start a /\ on_line goal a)
           /\ on_plane P 'a /\ on_plane start 'a /\ on_plane goal 'a
           /\ (!X. MEM X polyseg ==> on_plane X 'a)
           /\ ~on_polyseg polyseg P
           /\ (!X. between P X start ==> ~on_polyseg polyseg X)
           /\ (!X. between P X goal ==> ~on_polyseg polyseg X)"
     at [0]
  ;so consider ["s:point"]
     st "between P s start
         /\ (!X. in_triangle (P,s,goal) X ==> ~on_polyseg polyseg X)"
     using K (MATCH_MP_TAC squeeze) at [1]
  ;so consider ["s':point"] st "between P s' s" at [2] by [three;BET_NEQS]
  ;take ["s'"]
  ;hence "between P s' start" from [1]
     using ORDER_TAC `{P:point,s,s',start}`
     at [3]
  ;fix ["X:point"]
  ;assume "between s' X goal"
  ;obviously (by_ncols o Di.conjuncts)
     (hence "in_triangle (P,s,goal) X" from [0;1;2] by [in_triangle2;BET_SYM])
  ;qed from [1]];;

(* The following lemmas allow us to move around the polygon. One way to
   interpret the formalisation is in terms of a starting point X being able to
   extend an arm out to touch one of the nearby walls with its "hand."
   Alternatively, we say we are in a position where we have line of sight to
   the hand. *)

(* If we have line of sight to the inside of a wall, then we form a triangle
   with that wall. In other words, if you are in line with a wall, then you
   don't have line of sight to it. I like the shortness of this proof, but
   ORDER_TAC is *crazy* slow here. It'd be faster to manually case split on
   the position of X relative to P1 and P2. *)
let hand_triangle = theorem
  "!X hand P1 P2.
     ~(X = hand) /\ between P1 hand P2
     /\ ~(?Y. between P1 Y P2 /\ between X Y hand)
     ==> ~(?a. on_line P1 a /\ on_line P2 a /\ on_line X a)"
   [fix ["X:point";"hand:point";"P1:point";"P2:point"]
   ;assume "~(X = hand)" at [0]
   ;assume "between P1 hand P2" at [1]
   ;assume "~(?Y. between P1 Y P2 /\ between X Y hand)" at [2]
   ;otherwise assume "?a. on_line P1 a /\ on_line P2 a /\ on_line X a"
   ;so consider ["a:line"]
     st "on_line P1 a /\ on_line P2 a /\ on_line X a" at [3]
   ;consider ["A:point";"B:point";"C:point"]
     st "between X A hand /\ between P1 B hand /\ between hand C P2"
     from [0;1] by [three;BET_NEQS]
   ;hence "between P1 A P2 /\ between X A hand
           \/ between P1 B P2 /\ between X B hand
           \/ between P1 C P2 /\ between X C hand"
     using ORDER_TAC `{A,B,C,hand,P1:point,P2,X}`
     from [0;1;3]
   ;qed from [2]];;

(* If we have line of sight to what appears locally to be the wall of a simple
   polygon, then we can move to a point where we have line of sight with the
   next wall. *)
(* There are a lot of unpleasant subproofs here where I need a universal
   lemma, which is out of scope of both ORDER_TAC and my incidence automation. *)
let polygon_move = theorem
  "!P1 P2 P3 Ps X hand 'a.
     on_plane P1 'a /\ on_plane P2 'a /\ on_plane P3 'a
     /\ (!P. MEM P Ps ==> on_plane P 'a)
     /\ on_plane X 'a
     /\ between P1 hand P2
     /\ ~(P2 = P3)
     /\ ~on_polyseg (CONS P1 (CONS P2 (CONS P3 Ps))) X
     /\ ~on_polyseg (CONS P3 Ps) P2
     /\ ~(?Y. between X Y hand /\ on_polyseg (CONS P1 (CONS P2 (CONS P3 Ps))) Y)
     /\ ~(?Y. between P1 Y P2 /\ on_polyseg (CONS P2 (CONS P3 Ps)) Y)
     /\ ~(?Y. between P2 Y P3 /\ on_polyseg (CONS P3 Ps) Y)
     ==> ?hand' X'.
            seg_connected 'a
              (on_polyseg (CONS P1 (CONS P2 (CONS P3 Ps)))) X X'
            /\ between P2 hand' P3
            /\ ~on_polyseg (CONS P1 (CONS P2 (CONS P3 Ps))) X'
            /\ ~(?Y. between X' Y hand'
            /\ on_polyseg (CONS P1 (CONS P2 (CONS P3 Ps))) Y)"
  [fix ["P1:point";"P2:point";"P3:point";"Ps:point list"
       ;"X:point";"hand:point";"'a:plane"]
  ;assume "on_plane P1 'a /\ on_plane P2 'a /\ on_plane P3 'a" at [0]
  ;assume "!P. MEM P Ps ==> on_plane P 'a" at [1]
  ;assume "on_plane X 'a" at [2]
  ;assume "between P1 hand P2" at [3]
  ;assume "~(P2 = P3)" at [4]
  ;so consider ["hand':point"] st "between P2 hand' P3"
    by [three] from [4] at [5]
  ;assume "~on_polyseg (CONS P1 (CONS P2 (CONS P3 Ps))) X" at [6]
  ;assume "~on_polyseg (CONS P3 Ps) P2" at [7]
  ;assume "~(?Y. between X Y hand
                 /\ on_polyseg (CONS P1 (CONS P2 (CONS P3 Ps))) Y)" at [8]
  ;assume "~(?Y. between P1 Y P2 /\ on_polyseg (CONS P2 (CONS P3 Ps)) Y)" 
     at [9]
  ;assume "~(?Y. between P2 Y P3 /\ on_polyseg (CONS P3 Ps) Y)" at [10]
  ;have "~(?a. on_line P1 a /\ on_line P2 a /\ on_line X a)" at [11]
     from [3;6;8] by [hand_triangle;on_polyseg_CONS2]
  ;so consider ["hp:half_plane"] at [12]
     st "on_line P1 (line_of_half_plane hp) /\ on_line P2 (line_of_half_plane hp)
         /\ on_half_plane hp X"
     by [unique_half_plane]
  ;have "!'b. on_plane P1 'b /\ on_plane P2 'b /\ on_plane X 'b ==> 'b = 'a"
     from [0;2;11] by [g15] at [13]
  ;per cases
    [[suppose "on_half_plane hp P3" at [14]
     ;hence "~(?a. on_line P1 a /\ on_line P2 a /\ on_line P3 a)"
       from [3;12] by [half_plane_not_on_line;g12;BET_NEQS] at [15]
     ;have "!Y. between hand Y P2 ==> ~(on_polyseg (CONS P2 (CONS P3 Ps)) Y)"
       proof
       [fix ["Y:point"]
       ;assume "between hand Y P2"
       ;hence "between P1 Y P2" from [3] using ORDER_TAC `{hand:point,P1,P2,Y}`
       ;qed from [9] by [on_polyseg_CONS2]]
     ;obviously by_incidence
       (so consider ["s:point"] st
          "between hand s X
           /\ !Y. between s Y P2 ==> ~on_polyseg (CONS P2 (CONS P3 Ps)) Y"
          at [16;17]
          from [0;1;2;3;8;9;11;13] by [MEM;on_polyseg_CONS2;BET_SYM]
          using K (MATCH_MP_TAC squeeze' THEN EXISTS_TAC `'a:plane`))
     ;have "on_half_plane hp s"
       from [3;12;16] by [bet_on_half_plane;g12;g21] at [19]
     ;have "~(?a. on_line hand' a /\ on_line P2 a /\ on_line s a)" at [20]
       proof
       [otherwise assume "?a. on_line hand' a /\ on_line P2 a /\ on_line s a"
           at [20]
       ;have "~between s P2 P3" at [21] proof
         [have "!P. on_half_plane hp P ==> on_plane P 'a"
             from [0;3;12;14] by [half_plane_on_plane;g16;BET_NEQS]
         ;qed by [on_half_plane_not_bet] from [12;14;19]]
       ;have "~(s = P2) /\ ~(s = P3) /\ ~between P2 s P3" at [22]
         using (MESON_TAC o map (REWRITE_RULE [on_polyseg;MEM])
                  o map (REWRITE_RULE [on_polyseg_CONS2;BET_SYM]))
         from [8;16]
       ;have "~between P2 P3 s" from [17] by [BET_SYM]
         by [on_polyseg;MEM]
       ;qed from [4;5;20;21;22] using ORDER_TAC `{P2:point,P3,s}`]
     ;have "!Y. between P2 Y hand' ==> ~on_polyseg (CONS P3 Ps) Y" proof
       [fix ["Y:point"]
       ;assume "between P2 Y hand'"
       ;hence "between P2 Y P3"
         from [5] using ORDER_TAC `{hand':point,P2,P3,Y}`
       ;qed from [10] by [on_polyseg_CONS2]]
     ;obviously (by_incidence o Di.conjuncts)
       (so consider ["hand'':point"] st
          "between P2 hand'' P3
           /\ !Y. between hand'' Y s ==> ~on_polyseg (CONS P3 Ps) Y"
          from [0;1;3;4;5;7;10;13;16;17;20] by [on_polyseg_CONS2;BET_SYM;MEM]
          using K (MATCH_MP_TAC squeeze' THEN EXISTS_TAC `'a:plane`)
          at [21;22])
     ;take ["hand''";"s:point"]
     ;thus "between P2 hand'' P3" at [23] from [21]
     ;thus "~on_polyseg (CONS P1 (CONS P2 (CONS P3 Ps))) s"
       from [8;16] by [BET_SYM]
     ;thus "~(?Y. between s Y hand''
             /\ on_polyseg (CONS P1 (CONS P2 (CONS P3 Ps))) Y)" proof
       [otherwise assume
           "?Y. between s Y hand''
                /\ on_polyseg (CONS P1 (CONS P2 (CONS P3 Ps))) Y"
       ;so consider ["Y:point"]
         st "between s Y hand'' /\ on_polyseg [P1;P2;P3] Y"
         from [22] at [24] by [on_polyseg_CONS2;on_polyseg_pair;BET_SYM]
       ;obviously (by_ncols o Di.conjuncts)
         (hence "~on_polyseg [P2;P3] Y"
            from [4;5;20;23]
            by [on_polyseg_pair;g11_weak;g21])
       ;hence "on_polyseg [P1;P2] Y" from [24] at [25]
         by [on_polyseg_pair;on_polyseg_CONS2]
       ;have "on_half_plane hp hand''"
         from [12;14;23] by [bet_on_half_plane]
       ;hence "on_half_plane hp Y"
         from [19;24] by [bet_on_half_plane2] at [26]
       ;hence "between P1 Y P2"
         from [3;12;25] by [on_polyseg_pair;half_plane_not_on_line]
       ;qed from [3;12;26] by [BET_NEQS;g12;g21
                              ;half_plane_not_on_line]]
     ;unfolding from [5] by [seg_connected]
     ;take ["[X;s]"]
     ;tactics [REWRITE_TAC [NOT_CONS_NIL;GSYM IN_SET_OF_LIST;HD;LAST
                           ;DISJOINT_IMP;set_of_list]
                  THEN REWRITE_TAC [FORALL_IN_INSERT;NOT_IN_EMPTY]]
     ;obviously by_planes
       (thus "on_plane X 'a /\ on_plane s 'a"
          from [3;13;16])
     ;fix ["Y:point"]
     ;assume "between X Y s \/ Y = X \/ s = Y" by [IN;on_polyseg_pair] at [24]
     ;obviously (by_cols o Di.split)
       (hence "?a. on_line X a /\ on_line Y a /\ on_line hand a /\ on_line s a"
          from [16])
     ;hence "between X Y hand \/ X = Y" from [16;24]
       using ORDER_TAC `{hand:point,s,X,Y}`
     ;qed from [6;8] by [IN]]
    ;[suppose "on_line P3 (line_of_half_plane hp)" at [14]
     ;take ["hand'"]
     ;have "!Y. between hand Y hand' ==> ~on_polyseg (CONS P3 Ps) Y" at [15]
       proof
       [fix ["Y:point"]
       ;assume "between hand Y hand'" at [15]
       ;have "between P1 Y P2 \/ Y = P2 \/ between P2 Y P3"
         using ORDER_TAC `{P1:point,P2,P3,Y,hand,hand'}`
         from [3;5;12;14;15]
       ;qed from [7;9;10] by [on_polyseg_CONS2]]
     ;have "~(?a. on_line hand a /\ on_line hand' a /\ on_line X a)" proof
       [have "~(hand = hand')" from [3;5;9] by [on_polyseg_CONS2]
       ;obviously (by_ncols o Di.conjuncts) qed from [3;4;5;11;12;14]]
     ;obviously (by_incidence o Di.conjuncts)
       (so consider ["X':point"] st
          "between hand X' X
           /\ !Y. between X' Y hand' ==> ~on_polyseg (CONS P3 Ps) Y"
          from [0;1;2;3;4;5;8;9;11;12;13;14;15]
          by [on_polyseg_CONS2;MEM;BET_SYM] at [16;17]
          using K (MATCH_MP_TAC squeeze' THEN EXISTS_TAC `'a:plane`))
     ;take ["X':point"]
     ;have "!Y. between X Y X' ==> between hand Y X" at [18] proof
       [fix ["Y:point"]
       ;assume "between X Y X'"
       ;qed using ORDER_TAC `{hand:point,X,X',Y}` from [16]]
     ;thus "~(?Y. between X' Y hand'
                  /\ on_polyseg (CONS P1 (CONS P2 (CONS P3 Ps))) Y)" proof
       [otherwise
           assume "?Y. between X' Y hand'
                     /\ on_polyseg (CONS P1 (CONS P2 (CONS P3 Ps))) Y"
       ;so consider ["Y:point"]
         st "between X' Y hand'
             /\ on_polyseg (CONS P1 (CONS P2 (CONS P3 Ps))) Y" at [19]
       ;obviously (by_ncols o Di.conjuncts)
         (hence "~on_polyseg [P1;P2] Y /\ ~on_polyseg [P2;P3] Y"
            by [on_polyseg_pair;g11_weak;g21]
            from [3;4;5;11;12;14;16])
       ;qed from [17;19] by [on_polyseg_CONS2;on_polyseg_sing]]
     ;thus "between P2 hand' P3" from [5]
     ;thus "~on_polyseg (CONS P1 (CONS P2 (CONS P3 Ps))) X'"
       from [8;16] by [BET_SYM]
     ;unfolding by [seg_connected]
     ;take ["[X;X']"]
     ;tactics [REWRITE_TAC [NOT_CONS_NIL;GSYM IN_SET_OF_LIST;HD;LAST
                          ;DISJOINT_IMP;set_of_list]
                  THEN REWRITE_TAC [FORALL_IN_INSERT;NOT_IN_EMPTY]]
     ;obviously (by_planes o Di.conjuncts)
       (thus "on_plane X 'a /\ on_plane X' 'a" from [3;13;16])
     ;qed from [6;8;16;18] by [IN;BET_SYM;on_polyseg_pair]]
    ;[suppose "~on_half_plane hp P3 /\ ~on_line P3 (line_of_half_plane hp)" 
         at [14]
     ;consider ["s:point"]
       st "between P1 P2 s
           /\ ~on_polyseg (CONS P3 Ps) s
           /\ ~(?Y. between P2 Y s /\ on_polyseg (CONS P3 Ps) Y)"
       at [15] proof
       [consider ["s:point"]
           st "between P1 P2 s
               /\ ~(?Y. between P2 Y s /\ on_polyseg (CONS P3 Ps) Y)" at [15]
           proof
           [consider ["s:point"] st "between P1 P2 s"
               from [3] by [g22;BET_NEQS] at [15]
           ;so assume "?Y. between P2 Y s /\ on_polyseg (CONS P3 Ps) Y"
           ;so consider ["Y:point"]
             st "between P2 Y s /\ on_polyseg (CONS P3 Ps) Y" at [16]
           ;so consider ["s':point"]
             st "on_polyseg (CONS P3 Ps) s'
                 /\ (between P2 s' Y \/ Y = s')
                 /\ ~(?Y. between P2 Y s' /\ on_polyseg (CONS P3 Ps) Y)"
             using K (MP_TAC (SPECL [`CONS (P3:point) Ps`;`P2:point`;`Y:point`]
                                ray_cast))
             from [7] at [16] at [17;18;19]
           ;obviously (by_cols o Di.split)
             (have "?a. on_line P1 a /\ on_line P2 a
                        /\ on_line s a /\ on_line s' a /\ on_line Y a"
                from [15;16;18])
           ;hence "between P1 P2 s'" from [15;16;18]
             using ORDER_TAC `{P1:point,P2,s,s',Y}`
           ;qed from [19]]
       (* Here, we take a point before the first point of intersection. Similar
          to squeeze', this should probably be factored out as a lemma. *)
       ;so consider ["s':point"] st "between P2 s' s"
         by [three;BET_NEQS] at[16]
       ;hence "between P1 P2 s'" from [15]
         using ORDER_TAC `{P1:point,P2,s,s'}` at [17]
       ;have "!Y. between P2 Y s' ==> between P2 Y s" proof
         [fix ["Y:point"]
         ;assume "between P2 Y s'"
         ;qed using ORDER_TAC `{P2:point,Y,s,s'}` from [16]]
       ;qed from [15;16;17]]
     ;have "!Y. between hand Y s ==> ~on_polyseg (CONS P3 Ps) Y" at [16]
       proof
       [fix ["Y:point"]
       ;assume "between hand Y s"
       ;hence "between P1 Y P2 \/ P2 = Y \/ between P2 Y s"
         from [3;15] using ORDER_TAC `{hand:point,P1,P2,s,Y}`
       ;qed from [7;9;15] by [on_polyseg_CONS2]]
     ;have "~(hand = s)" by [g23] from [3;15]
     ;obviously (by_incidence o Di.conjuncts)
       (so consider ["s':point"] st
          "between hand s' X
           /\ !Y. between s' Y s ==> ~on_polyseg (CONS P3 Ps) Y"
          from [0;1;2;3;6;8;9;11;13;15;16]
          by [MEM;on_polyseg_CONS2;BET_SYM]
          using K (MATCH_MP_TAC squeeze' THEN EXISTS_TAC `'a:plane`)
          at [17;18])
     ;obviously (by_incidence o Di.conjuncts)
       (consider ["hand'':point"] st
          "between P2 hand'' P3
           /\ (!X. between hand'' X s ==> ~on_polyseg (CONS P3 Ps) X)"
          from [0;1;2;7;9;10;12;13;14;15] by [MEM] at [19;20]
          using K (MATCH_MP_TAC squeeze' THEN EXISTS_TAC `'a:plane`))
     ;take ["hand''";"s:point"]
     ;thus "between P2 hand'' P3" from [19]
     ;obviously (by_ncols o Di.conjuncts)
       (thus "~on_polyseg (CONS P1 (CONS P2 (CONS P3 Ps))) s"
          at [21] from [12;14;15] by [on_polyseg_CONS2;g21;g23])
     ;thus "~(?Y. between s Y hand''
           /\ on_polyseg (CONS P1 (CONS P2 (CONS P3 Ps))) Y)" proof
       [otherwise assume
         "?Y. between s Y hand''
              /\ on_polyseg (CONS P1 (CONS P2 (CONS P3 Ps))) Y"
       ;so consider ["Y:point"] st
         "between s Y hand''
              /\ on_polyseg (CONS P1 (CONS P2 (CONS P3 Ps))) Y"
       ;obviously (by_ncols o Di.conjuncts)
         (qed from [4;12;14;15;19;20] by [on_polyseg_CONS2;g21]
            using (MESON_TAC o mutual_rewrite))]
     ;unfolding by [seg_connected]
     ;take ["[X;s';s]"]
     ;tactics [REWRITE_TAC [NOT_CONS_NIL;GSYM IN_SET_OF_LIST;HD;LAST
                          ;DISJOINT_IMP;set_of_list]
                 THEN REWRITE_TAC [FORALL_IN_INSERT;NOT_IN_EMPTY]]
     ;obviously (by_planes o Di.conjuncts)
       (thus "on_plane X 'a /\ on_plane s 'a /\ on_plane s' 'a"
          from [3;13;15;17])
     ;have "!Y. between s' Y X
               ==> ~on_polyseg (CONS P1 (CONS P2 (CONS P3 Ps))) Y" proof
       [fix ["Y:point"]
       ;assume "between s' Y X"
       ;hence "between X Y hand" from [17]
         using ORDER_TAC `{hand:point,s',X,Y}`
       ;qed from [8]]
     ;hence "~(?Y. on_polyseg [s';X] Y 
                  /\ on_polyseg (CONS P1 (CONS P2 (CONS P3 Ps))) Y)"
       from [6;8;17] by [on_polyseg_pair;BET_SYM] at [22]
     ;have "on_half_plane hp s' /\ on_line s (line_of_half_plane hp)"
       from [3;12;15;17] by [bet_on_half_plane;g12;g21] at [23]
     ;hence "!Y. between s Y s' ==> ~on_polyseg [P2;P3] Y"
       from [12;14]
       by [on_polyseg_pair;half_plane_not_on_line;bet_on_half_plane;BET_SYM]
       at [24]
     ;hence "!Y. between s Y s' ==> ~on_polyseg (CONS P1 (CONS P2 (CONS P3 Ps))) Y"
       at [25] proof
       [fix ["Y:point"]
       ;assume "between s Y s'"
       ;obviously (by_ncols o Di.conjuncts)
           qed from [3;11;15;17;18;24]
           by [g21;on_polyseg_CONS2;on_polyseg_sing]]
     ;qed from [21;22]
       using (REWRITE_TAC THEN' (MESON_TAC o mutual_rewrite))
       by [on_polyseg_CONS2;on_polyseg_sing;IN;BET_SYM]]]];;

(* Changing the metaphor for "squeeze": if X and Y have line-of-sight to the
   wall P1P2, and they lie on the same side of P1P2, then they can be
   segment-connected. *)
let same_side_wall_connected = theorem
  "!P1 P2 Ps X Y hand hand' hp 'a. 
     on_plane P1 'a /\ on_plane P2 'a
     /\ (!P. MEM P Ps ==> on_plane P 'a)
     /\ on_plane X 'a /\ on_plane Y 'a
     /\ between P1 hand P2 /\ between P1 hand' P2
     /\ ~on_polyseg (CONS P1 (CONS P2 Ps)) X
     /\ ~on_polyseg (CONS P1 (CONS P2 Ps)) Y
     /\ ~(?Z. between X Z hand /\ on_polyseg (CONS P1 (CONS P2 Ps)) Z)
     /\ ~(?Z. between Y Z hand' /\ on_polyseg (CONS P1 (CONS P2 Ps)) Z)
     /\ ~(?Z. between P1 Z P2 /\ on_polyseg (CONS P2 Ps) Z)
     /\ on_line P1 (line_of_half_plane hp) /\ on_line P2 (line_of_half_plane hp)
     /\ on_half_plane hp X /\ on_half_plane hp Y
     ==> seg_connected 'a (on_polyseg (CONS P1 (CONS P2 Ps))) X Y"
  [fix ["P1:point";"P2:point";"Ps:point list"
       ;"X:point";"Y:point";"hand:point";"hand':point"
       ;"hp:half_plane";"'a:plane"]
  ;assume "on_plane P1 'a /\ on_plane P2 'a" at [0]
  ;assume "!P. MEM P Ps ==> on_plane P 'a" at [1]
  ;assume "on_plane X 'a /\ on_plane Y 'a" at [2]
  ;assume "between P1 hand P2 /\ between P1 hand' P2" at [3]
  ;assume "~on_polyseg (CONS P1 (CONS P2 Ps)) X
           /\ ~on_polyseg (CONS P1 (CONS P2 Ps)) Y" at [4]
  ;assume "~(?Z. between X Z hand /\ on_polyseg (CONS P1 (CONS P2 Ps)) Z)"
     at [5]
  ;assume "~(?Z. between Y Z hand' /\ on_polyseg (CONS P1 (CONS P2 Ps)) Z)"
     at [6]
  ;assume "~(?Z. between P1 Z P2 /\ on_polyseg (CONS P2 Ps) Z)" at [7]
  ;assume "on_line P1 (line_of_half_plane hp) /\ on_line P2 (line_of_half_plane hp)
           /\ on_half_plane hp X /\ on_half_plane hp Y" at [8]
  ;have "~(?a. on_line P1 a /\ on_line P2 a /\ on_line X a)" at [9]
     from [3;8] by [half_plane_not_on_line;g12;BET_NEQS]
  ;have "~(?a. on_line P1 a /\ on_line P2 a /\ on_line Y a)" at [10]
     from [3;8] by [half_plane_not_on_line;g12;BET_NEQS]
  ;have "!'b. on_plane P1 'b /\ on_plane P2 'b /\ on_plane X 'b ==> 'b = 'a"
     from [0;2;9] by [g15] at [11]
  ;consider ["s:point"] st
     "between hand s X
      /\ !Z. between s Z hand' ==> ~on_polyseg (CONS P2 Ps) Z" at [12;13] proof
     [per cases
         [[suppose "hand = hand'" at [12]
          ;have "~(X = hand)" from [3;4] by [on_polyseg_CONS2]
          ;so consider ["s:point"] st "between X s hand" by [three] at [13]
          ;have "!Z. between s Z hand' ==> ~on_polyseg (CONS P2 Ps) Z" proof
            [fix ["Z:point"]
            ;assume "between s Z hand" from [12]
            ;hence "between X Z hand" from [13]
              using ORDER_TAC `{s:point,X,Z,hand}`
            ;qed from [5] by [on_polyseg_CONS2]]
          ;qed from [13] by [BET_SYM]]
         ;[suppose "~(hand = hand')" at [12]
          ;have "!Z. between hand Z hand' ==> ~on_polyseg (CONS P2 Ps) Z" proof
            [fix ["Z:point"]
            ;assume "between hand Z hand'"
            ;hence "between P1 Z P2" from [3]
              using ORDER_TAC `{hand:point,hand',P1,P2,Z}`
            ;qed from [7]]
          ;obviously (by_incidence o Di.conjuncts)
            (qed from [0;1;2;3;5;7;9;11;12] by [MEM;on_polyseg_CONS2;BET_SYM]
               using K (MATCH_MP_TAC squeeze' THEN EXISTS_TAC `'a:plane`))]]]
  ;have "!Z. on_polyseg [X;s] Z ==> ~on_polyseg (CONS P1 (CONS P2 Ps)) Z"
     at [14] proof
     [have "!Z. between X Z s ==> ~on_polyseg (CONS P1 (CONS P2 Ps)) Z" proof
         [fix ["Z:point"]
         ;assume "between X Z s"
         ;hence "between X Z hand"
           using ORDER_TAC `{hand:point,s,X,Z}` from [12]
         ;qed from [5]]
     ;qed from [4;5;12] by [BET_SYM;on_polyseg_pair]]
  ;have "!P. on_half_plane hp P ==> on_plane P 'a" at [15]
     from [0;2;3;8] by [half_plane_on_plane;g16;BET_NEQS]
  ;have "on_half_plane hp s"
     from [3;8;12] by [bet_on_half_plane;bet_on_half_plane2;g12;g21] at [16]
  ;per cases
    (* This case would have been unnecessary had we removed the assumption of
       non-collinearity from squeeze. *)
    [[suppose "?a. on_line hand' a /\ on_line s a /\ on_line Y a" at [17]
     ;unfolding by [seg_connected]
     ;take ["[X:point;s:point;Y:point]"]
     ;tactics [REWRITE_TAC [NOT_CONS_NIL;GSYM IN_SET_OF_LIST;HD;LAST
                           ;DISJOINT_IMP;set_of_list]
                  THEN REWRITE_TAC [FORALL_IN_INSERT;NOT_IN_EMPTY]]
     ;obviously (by_planes o Di.conjuncts)
       (thus "on_plane X 'a /\ on_plane s 'a /\ on_plane Y 'a"
          from [3;11;12;17])
     ;assume "~(s = Y)"
       from [14] by [IN;on_polyseg_CONS2;on_polyseg_sing;BET_REFL2] at [18]
     ;have "between hand' s Y \/ between hand' Y s" at [19] proof
       [otherwise assume "~between hand' s Y /\ ~between hand' Y s" at [19]
       ;have "on_line hand' (line_of_half_plane hp)"
         at [20] from [3;8] by [g21;g12]
       ;hence "~(s = hand') /\ ~(Y = hand')"
         at [21] from [8;16] by [half_plane_not_on_line]
       ;have "~between s hand' Y" by [on_half_plane_not_bet]
         from [8;15;16;20]
       ;qed from [17;18;19;21] using ORDER_TAC `{hand':point,s,Y}`]
     ;have "!Z. between s Z Y ==> ~on_polyseg (CONS P1 (CONS P2 Ps)) Z" proof
       [fix ["Z:point"]
       ;assume "between s Z Y" at [20]
       ;hence "on_half_plane hp Z" from [8;16] by [bet_on_half_plane2]
       ;hence "~on_polyseg [P1;P2] Z" at [21]
         from [8] by [half_plane_not_on_line;g12;g21;on_polyseg_pair]
       ;have "between hand' Z Y \/ between hand' Z s"
         from [17;19;20] using ORDER_TAC `{hand':point,s,Y,Z}`
       ;qed from [6;13;21] by [BET_SYM;on_polyseg_CONS2;on_polyseg_pair]]
     ;qed from [4;14] by [IN;on_polyseg_CONS2;on_polyseg_sing;BET_SYM]]
    ;[suppose "~(?a. on_line hand' a /\ on_line s a /\ on_line Y a)" at [17]
     ;obviously (by_planes o Di.conjuncts)
       (so consider ["s':point"] st
          "between hand' s' s
           /\ !Z. between s' Z Y ==> ~on_polyseg (CONS P2 Ps) Z"
          from [0;1;2;3;6;7;11;12;13] by [on_polyseg_CONS2;BET_SYM;MEM]
          using K (MATCH_MP_TAC squeeze' THEN EXISTS_TAC `'a:plane`)
          at [18;19])
     ;unfolding by [seg_connected]
     ;take ["[X:point;s:point;s':point;Y:point]"]
     ;tactics [REWRITE_TAC [NOT_CONS_NIL;GSYM IN_SET_OF_LIST;HD;LAST
                           ;DISJOINT_IMP;set_of_list]
                  THEN REWRITE_TAC [FORALL_IN_INSERT;NOT_IN_EMPTY]]
     ;obviously (by_planes o Di.conjuncts)
       (thus "on_plane s 'a /\ on_plane s' 'a 
              /\ on_plane X 'a /\ on_plane Y 'a"
          from [0;2;3;11;12;18])
     ;have "on_line hand (line_of_half_plane hp)
            /\ on_line hand' (line_of_half_plane hp)"
       from [3;8] by [g12;g21]
     ;hence "on_half_plane hp s /\ on_half_plane hp s'
             /\ !Z. between s Z s' \/ between s' Z Y
                    ==> on_half_plane hp Z"
       from [8;12;16;18] by [bet_on_half_plane;bet_on_half_plane2]
       at [20]
     ;have "!Z. on_half_plane hp Z ==> ~on_polyseg [P1;P2] Z"
       from [3;8] by [on_polyseg_pair;g12;g21;half_plane_not_on_line]
     ;hence "!Z. on_polyseg [s;s';Y] Z ==> ~on_polyseg [P1;P2] Z"
       from [8;20] by [on_polyseg_CONS2;on_polyseg_sing] at [21]
     ;have "!Z. between s Z s' ==> ~on_polyseg (CONS P2 Ps) Z" proof
       [fix ["Z:point"]
       ;assume "between s Z s'"
       ;hence "between s Z hand'" from [18]
         using ORDER_TAC `{hand':point,s,s',Z}`
       ;qed from [13]]
     ;qed from [4;13;14;18;19;21] by
       [IN;on_polyseg_CONS2;on_polyseg_sing;BET_SYM]]]];;

(* If we have line of sight to a vertex, then we have line of sight to an edge
   with that vertex. *)
let vertex_to_wall = theorem
  "!P1 P2 P3 Ps X 'a.
   on_plane P1 'a /\ on_plane P2 'a /\ on_plane P3 'a /\ on_plane X 'a
   /\ (!P. MEM P Ps ==> on_plane P 'a)
   /\ ~between P1 P3 P2 /\ ~between P2 P1 P3
   /\ ~(P1 = P2) /\ ~(P1 = P3)
   /\ ~on_polyseg (CONS P3 Ps) P2
   /\ ~(?Z. between P1 Z P2 /\ on_polyseg (CONS P2 (CONS P3 Ps)) Z)
   /\ ~(?Z. between P2 Z P3 /\ on_polyseg (CONS P3 Ps) Z)
   /\ ~on_polyseg (CONS P1 (CONS P2 (CONS P3 Ps))) X
   /\ ~(?Z. between P2 Z X /\ on_polyseg (CONS P1 (CONS P2 (CONS P3 Ps))) Z)
   ==> ?Y. (between P1 Y P2 \/ between P2 Y P3)
           /\ ~(?Z. between X Z Y
                    /\ on_polyseg (CONS P1 (CONS P2 (CONS P3 Ps))) Z)"
  [fix ["P1:point";"P2:point";"P3:point";"Ps:point list";"X:point";"'a:plane"]
  ;assume "on_plane P1 'a /\ on_plane P2 'a /\ on_plane P3 'a /\ on_plane X 'a"
     at [0]
  ;assume "!P. MEM P Ps ==> on_plane P 'a" at [1]
  ;assume "~between P1 P3 P2 /\ ~between P2 P1 P3" at [2]
  ;assume "~(P1 = P2) /\ ~(P1 = P3)" at [3]
  ;assume "~on_polyseg (CONS P3 Ps) P2" at [4]
  ;assume "~on_polyseg (CONS P1 (CONS P2 (CONS P3 Ps))) X" at [5]
  ;assume "~(?Z. between P1 Z P2 /\ on_polyseg (CONS P2 (CONS P3 Ps)) Z)"
     at [6]
  ;assume "~(?Z. between P2 Z P3 /\ on_polyseg (CONS P3 Ps) Z)"
     at [7]
  ;assume "~(?Z. between P2 Z X
                 /\ on_polyseg (CONS P1 (CONS P2 (CONS P3 Ps))) Z)" at [8]
  ;per cases
    [[suppose "?a. on_line P1 a /\ on_line P2 a /\ on_line X a" at [9]
     ;have "~(?a. on_line P2 a /\ on_line P3 a /\ on_line X a)" at [10] proof
       [otherwise assume "?a. on_line P2 a /\ on_line P3 a /\ on_line X a"
           at [10]
       ;have "~(P1 = X) /\ ~(P2 = X) /\ ~(P3 = X)
              /\ ~between P1 X P2 /\ ~between P2 P1 X /\ ~between P2 X P3
              /\ ~between P2 P3 X" at [11]
         from [5;8] by [on_polyseg;MEM;on_polyseg_CONS2]
       ;(* We could do the next three steps in one go, but ORDER_TAC is taking 
           forever. *)
        have "~between P2 P1 P3 /\ ~(P2 = P3)" at [12]
          from [2;4] by [on_polyseg;MEM;on_polyseg_CONS2]
       ;hence "between P1 P2 P3" from [2;3;9;10;11]
         using ORDER_TAC `{P1:point,P2,P3}`
       ;qed using ORDER_TAC `{P1:point,P2,P3,X}` from [9;10;11]]
     ;so consider ["s:point"] st
       "between P2 s P3
        /\ !Z. between s Z X ==> ~on_polyseg (CONS P3 Ps) Z"
       from [0;1;4;7;8] by [on_polyseg;MEM;on_polyseg_CONS2]
       using K (MATCH_MP_TAC squeeze' THEN EXISTS_TAC `'a:plane`)
       at [11;12]
     ;take ["s:point"]
     ;have "~(?Z. between X Z s /\ on_polyseg [P1;P2;P3] Z)" proof
       [otherwise assume "?Z. between X Z s /\ on_polyseg [P1;P2;P3] Z"
       ;so consider ["Z:point"] st "between X Z s /\ on_polyseg [P1;P2;P3] Z"
         at [13]
       ;obviously (by_ncols o Di.conjuncts)
         (qed using (MESON_TAC o mutual_rewrite)
            from [3;9;10;11]
            by [on_polyseg_CONS2;on_polyseg_sing;g11_weak;g21])]
     ;qed from [11;12] by [on_polyseg_CONS2;on_polyseg_sing;BET_SYM]]
    ;[suppose "~(?a. on_line P1 a /\ on_line P2 a /\ on_line X a)" at [9]
     ;so consider ["s:point"] st
       "between P2 s P1
        /\ !Z. between s Z X ==> ~on_polyseg (CONS P3 Ps) Z"
       from [0;1;4;6;8] by [on_polyseg_CONS2;on_polyseg;MEM;BET_SYM]
       using K (MATCH_MP_TAC squeeze' THEN EXISTS_TAC `'a:plane`)
       at [10;11]
     ;per cases
       [[suppose "?Z. between s Z X /\ between P2 Z P3"
        ;so consider ["Z:point"] st "between s Z X /\ between P2 Z P3" at [12]
        ;take ["Z:point"]
        ;have "!Z'. between X Z' Z
                  ==> ~on_polyseg (CONS P1 (CONS P2 (CONS P3 Ps))) Z'" proof
          [fix ["Z':point"]
          ;assume "between X Z' Z" at [13]
          ;hence "between s Z' X" at [14] from [12;13]
            using ORDER_TAC `{s:point,X,Z,Z'}`
          ;(* Need to fix this so that we can have equality in any direction. This
              does not work with the discoverer if we do s' = Z'*)
           hence "~(Z' = s)" from [13] by [g21;g23]
          ;obviously (by_ncols o Di.conjuncts)
            (qed  from [3;9;10;11;12;13;14]
               by [on_polyseg_CONS2;g11_weak;g21])]
        ;qed from [12]]
       ;[case "~(?Z. between s Z X /\ between P2 Z P3)" at [12]
        ;take ["s:point"]
        ;have "!Z. between X Z s
                 ==> ~on_polyseg (CONS P1 (CONS P2 (CONS P3 Ps))) Z" proof
          [fix ["Z:point"]
          ;assume "between X Z s" at [13]
          ;obviously (by_ncols o Di.conjuncts)
            (qed from [3;9;10;11;12;13] by [on_polyseg_CONS2;g11_weak;g21])]
        ;qed from [10] by [BET_SYM]]]]]];;

(* Finally, the definition of simple polygons. *)
let simple_polygon = new_definition
  `simple_polygon 'a ps <=> 3 <= LENGTH ps 
                            /\ HD ps = LAST ps
                            /\ (!p. MEM p ps ==> on_plane p 'a)
                            /\ PAIRWISE (\p q. ~(p = q)) (BUTLAST ps)
                            /\ (!p p' x. MEM (p,p') (ADJACENT ps)
                                         /\ between p x p' ==> ~(MEM x ps))
                            /\ PAIRWISE (\(p,p') (q,q').
                                ~(?x. between p x p' /\ between q x q'))
                               (ADJACENT ps)`;;

(* Quick sanity check: triangles are simple polygons. *)
let triangle_is_simple =
  prove
  (`!A B C 'a. ~(?a. on_line A a /\ on_line B a /\ on_line C a)
               /\ on_plane A 'a /\ on_plane B 'a /\ on_plane C 'a 
               ==> simple_polygon 'a [A;B;C;A]`,
   REWRITE_TAC [simple_polygon] THEN CONV_TAC (REDEPTH_CONV num_CONV)
     THEN REWRITE_TAC [LENGTH;LE] THEN REPEAT GEN_TAC THEN DISCH_TAC 
     THEN ASM_REWRITE_TAC [HD;LAST;NOT_CONS_NIL;FORALL_IN_INSERT;NOT_IN_EMPTY
                          ;PAIRWISE;ALL;BUTLAST;ADJACENT_CLAUSES
                          ;GSYM IN_SET_OF_LIST;set_of_list]
     THEN REWRITE_TAC [PAIR_EQ;IN_INSERT;NOT_IN_EMPTY]
     THEN CONJ_TAC
     THENL [ASM_MESON_TAC [g11_weak]
           ;CONJ_TAC THENL [ASM_MESON_TAC [g21]
                           ;REWRITE_TAC [GSYM DE_MORGAN_THM]
                             THEN STRIP_TAC
                             THEN discover_tac (by_cols o Di.conjuncts)
                             ASM_MESON_TAC]]);;

(* These are not particularly useful in Mizar Light, because of the interplay
   with rewriting, and are probably not that useful in general. However, the
   list expressions in the following proofs are ugly as sin without the infix
   notation, and difficult to reason about. *)
parse_as_infix ("^", (16,"left"));;
let append_infix = new_definition `xs ^ ys = APPEND xs ys`;;
parse_as_infix ("::", (16,"right"));;
let cons_infix = new_definition `xs :: ys = CONS xs ys`;;
extend_basic_rewrites [append_infix;cons_infix];;

(* For any simple polygon, there are two points in the plane and not on the
   polygon which cannot be connected by a polygonal segment. In other words, a
   simple polygon separates the plane into at least two segment-connected
   regions. *)
let jordan_poly1 = theorem
  "!'a Ps. simple_polygon 'a Ps
           ==> ?P Q. on_plane P 'a /\ on_plane Q 'a
                     /\ ~on_polyseg Ps P /\ ~on_polyseg Ps Q
                     /\ ~seg_connected 'a (on_polyseg Ps) P Q"
  [fix ["'a:plane";"Ps:point list"]
  ;assume "simple_polygon 'a Ps" at [0]
  ;so consider ["Qs:point list";"Rs:point list"]
     st "Ps = Qs ^ Rs /\ LENGTH Qs = 3" at [1]
     by [CHOOSE_PREFIX;simple_polygon]
  ;so consider ["P:point";"Q:point";"R:point"]
     st "Qs = [P;Q;R]" at [2]
     using (MESON_TAC o map (CONV_RULE (ONCE_DEPTH_CONV LENGTH_EQ_CONV)))
  ;hence "~(P = Q)" from [0;1] by [simple_polygon;PAIRWISE_APPEND;PAIRWISE
                                  ;BUTLAST;NOT_CONS_NIL;APPEND;ALL]
     using (MESON_TAC o mutual_simp)
  ;so consider ["M:point"] st "between P M Q" at [3] by [three]
  ;have "~on_polyseg (Q :: R :: Rs) M"
     by [ADJACENT_CLAUSES;MEM;PAIR_EQ;PAIRWISE;GSYM ALL_MEM
        ;FORALL_PAIR_THM;APPEND;simple_polygon;on_polyseg]
     from [0;1;2;3] at [4]
     using (REWRITE_TAC THEN' (MESON_TAC o mutual_simp))
  ;have "!Z. ~(?a. on_line P a /\ on_line Q a /\ on_line Z a)
             ==> ?Z'. between M Z' Z /\ ~on_polyseg Ps Z'
                  /\ !W. between M W Z' ==> ~on_polyseg Ps W"
     at [5] proof
     [have "!Z. ~(?a. on_line P a /\ on_line Q a /\ on_line Z a)
                ==> ?Z'. between M Z' Z
                     /\ !W. between M W Z' ==> ~on_polyseg Ps W"
         at [5] proof
         [fix ["Z:point"]
         ;assume "~(?a. on_line P a /\ on_line Q a /\ on_line Z a)" at [5]
         ;per cases
           [[suppose "?Z'. between M Z' Z /\ on_polyseg ([Q;R] ^ Rs) Z'"
            ;so consider ["Z':point"]
              st "between M Z' Z /\ on_polyseg ([Q;R] ^ Rs) Z'"
              at [6]
            ;obviously (by_ncols o Di.conjuncts)
              (so consider ["Z'':point"]
                 st "on_polyseg ([Q;R] ^ Rs) Z''
                     /\ (between M Z'' Z' \/ Z' = Z'')
                     /\ ~(?W. between M W Z'' /\ on_polyseg ([Q;R] ^ Rs) W)"
                 by [on_polyseg_CONS2;APPEND;g21] from [1;2;3;4;5]
                 using (K (MATCH_MP_TAC ray_cast) THEN' REWRITE_TAC
                          THEN' (MESON_TAC o mutual_rewrite))
                 at [7])
            ;obviously (by_cols o Di.split o Di.conjuncts)
              (hence "?a. on_line M a /\ on_line Z a
                   /\ on_line Z' a /\ on_line Z'' a" by [g21] from [6])
            ;hence "between M Z'' Z" using ORDER_TAC `{M:point,Z,Z',Z''}`
              at [8] from [6;7]
            ;take ["Z'':point"]
            ;unfolding from [this]
            ;fix ["W:point"]
            ;assume "between M W Z''" at [9]
            ;obviously by_ncols
              (qed from [1;2;3;5;7;8] by [on_polyseg_CONS2;g11_weak;g21;APPEND]
                 using (REWRITE_TAC THEN' (MESON_TAC o mutual_rewrite)))]
           ;[suppose "~(?Z'. between M Z' Z /\ on_polyseg ([Q; R] ^ Rs) Z')"
                at [6]
            ;obviously by_neqs
              (consider ["Z':point"]
                 st "between M Z' Z" at [7] from [3;5] by [three])
            ;take ["Z':point"]
            ;unfolding from [this]
            ;fix ["W:point"]
            ;assume "between M W Z'"
            ;hence "between M W Z" using ORDER_TAC `{M:point,W,Z,Z'}` from [7]
            ;obviously by_ncols
              (qed from [1;2;3;5;6] by [g11_weak;g21;on_polyseg_CONS2;APPEND]
                 using (REWRITE_TAC THEN' (MESON_TAC o mutual_rewrite)))]]]
     ;fix ["Z:point"]
     ;assume "~(?a. on_line P a /\ on_line Q a /\ on_line Z a)" at [6]
     ;so consider ["Z':point"]
       st "between M Z' Z /\ !W. between M W Z' ==> ~on_polyseg Ps W"
       at [7] from [5]
     ;so consider ["Z'':point"] st "between M Z'' Z'" at [8]
       by [three;BET_NEQS]
     ;take ["Z''"]
     ;hence "between M Z'' Z" using ORDER_TAC `{M:point,Z,Z',Z''}`
       from [7]
     ;hence "~on_polyseg Ps Z''" from [7;8]
     ;fix ["W:point"]
     ;assume "between M W Z''"
     ;hence "between M W Z'" from [8] using ORDER_TAC `{M:point,W,Z',Z''}`
     ;qed from [7]]
  ;have "on_plane P 'a /\ on_plane Q 'a"
    from [0;1;2] by [simple_polygon;MEM;MEM_APPEND]
    at [6]
  ;so consider ["X:point"]
    st "on_plane X 'a /\ ~(?a. on_line P a /\ on_line Q a /\ on_line X a)"
    from [3] by [BET_NEQS;plane_triangle] at [7]
  ;so consider ["X':point"] st
    "between M X' X /\ ~on_polyseg Ps X'
      /\ !W. between M W X' ==> ~on_polyseg Ps W"
    from [5] at [8]
  ;so consider ["Y:point"] st "between X M Y"
    from [3] by [BET_NEQS;g22] at [9]
  ;obviously (by_ncols o Di.conjuncts)
    (so consider ["Y':point"] st
       "between M Y' Y /\ ~on_polyseg Ps Y'
         /\ !W. between M W Y' ==> ~on_polyseg Ps W"
       from [3;5;7] at [10])
  ;take ["X':point";"Y':point"]
  ;have "!W. between X' W Y' ==> ~on_polyseg (Q :: R :: Rs) W" at [11] proof
    [fix ["W:point"]
    ;assume "between X' W Y'"
    ;hence "between M W X' \/ M = W \/ between M W Y'"
      from [8;9;10] using ORDER_TAC `{M:point,W,X,Y,X',Y'}`
    ;qed from [1;2;4;8;10]
      by [APPEND;on_polyseg_CONS2]
      using (REWRITE_TAC THEN' MESON_TAC o mutual_simp)]
  ;have "!'b. on_plane P 'b /\ on_plane Q 'b /\ on_plane X 'b ==> 'b = 'a"
    by [g15] from [6;7] at [12]
  ;obviously (by_planes o Di.conjuncts)
    (hence "on_plane X' 'a /\ on_plane Y' 'a" from [3;8;9;10])
  ;have "~seg_connected 'a (on_polyseg Ps) X' Y'" proof
    [otherwise consider ["path:point list"]
        st "~(path = [])
           /\ (!P. MEM P path ==> on_plane P 'a)
           /\ HD path = Y' /\ LAST path = X'
           /\ DISJOINT (on_polyseg path) (on_polyseg Ps)" at [13]
        by [seg_connected;seg_connected_sym]
    ;so consider ["Y'':point";"path':point list"]
      st "path = Y'' :: path'" by [list_CASES]
    ;hence "path = Y' :: path'" from [13] by [HD] at [14]
    ;hence "between X' M Y'" from [8;9;10] at [15]
      using ORDER_TAC `{M:point,X,Y,X',Y'}`
    ;obviously (by_planes o Di.conjuncts)
      (have "on_plane P 'a /\ on_plane Q 'a /\ on_plane X' 'a /\ on_plane Y' 'a
              /\ (!X. MEM X (CONS R Rs) ==> on_plane X 'a) 
              /\ (!X. MEM X path' ==> on_plane X 'a)"
         from [0;1;2;3;8;9;10;12;13;14] by [MEM;MEM_APPEND;simple_polygon])
    ;obviously (by_ncols o Di.conjuncts)
      (so consider ["intersection:point"]
         st "on_polyseg (Q :: R :: Rs) intersection
              /\ on_polyseg (X' :: Y' :: path') intersection
              \/ on_polyseg (P :: Q :: R :: Rs) intersection
              /\ on_polyseg (Y' :: path') intersection"
         from [0;1;2;3;7;8;13;14;15]
         by [simple_polygon;LAST_APPEND;HD;LAST;NOT_CONS_NIL;APPEND
            ;MEM_APPEND;MEM]
         using ((K (REWRITE_TAC [])
                   THEN' (K (MATCH_MP_TAC intersect_polyseg_closed))
                   THEN' (K (EXISTS_TAC `M:point` THEN
                               EXISTS_TAC `'a:plane`))
                   THEN' ((REWRITE_TAC THEN' MESON_TAC) o mutual_simp))))
    ;hence "on_polyseg (Q :: R :: Rs) intersection 
            /\ on_polyseg [X';Y'] intersection"
      from [1;2;13;14] by [on_polyseg_CONS2;DISJOINT_IMP;IN;APPEND;on_polyseg_pair]
      using (MESON_TAC o mutual_simp) at [16]
    ;qed from [1;2;8;10;11] by [APPEND;on_polyseg_pair;on_polyseg_CONS2]
      using (MESON_TAC o mutual_simp)]
  ;qed from [8;10]];;

let rotate_polyseg = 
  let lemma = prove
    (`on_polyseg (([p] ^ (ps  ^ [q])) ^ (ps' ^ [p])) x
      <=> on_polyseg (([q] ^ (ps' ^ [p])) ^ (ps  ^ [q])) x`,
     REWRITE_TAC [on_polyseg]
       THEN SIMP_TAC [ADJACENT_APPEND;NOT_CONS_NIL;APPEND_EQ_NIL]
       THEN REWRITE_TAC
       [HD;LAST;APPEND;APPEND_EQ_NIL;NOT_CONS_NIL;LAST_APPEND
       ;ADJACENT_CLAUSES;MEM;MEM_APPEND;PAIR_EQ]
       THEN MESON_TAC [BET_REFL2]) in
  REWRITE_RULE []
    (prove (`!p q ps ps'. on_polyseg ([p] ^ ps  ^ [q] ^ ps' ^ [p])
            = on_polyseg ([q] ^ ps' ^ [p] ^ ps  ^ [q])`,
            REWRITE_TAC [EXTENSION;IN] THEN REPEAT GEN_TAC
              THEN ACCEPT_TAC (REWRITE_RULE [APPEND_ASSOC] lemma)));;

let UNION_ACI = prove
  (`s UNION t = t UNION s /\
    (s UNION t) UNION u = s UNION (t UNION u) /\
    s UNION (t UNION u) = t UNION (s UNION u) /\
    s UNION s = s /\
    s UNION (s UNION t) = s UNION t`,
   SET_TAC []);;

let LAMBDA_PAIR_THM' = prove
  (`!P. (\(x,y). P x y) = \p. P (FST p) (SND p)`,
  REWRITE_TAC [LAMBDA_PAIR_THM]);;

let rotate_simple_polygon = 
  (* This is all we need to know about pairwise, but it could be generalised,
     perhaps using Permutations.ml: if f is symmetric, then PAIRWISE f xs <=>
     PAIRWISE f ys whenever xs and ys are permutations of each other. *)
  let lemma = prove
    (`(!x y. f x y <=> f y x)
       ==> (PAIRWISE f (CONS x (APPEND xs (CONS y ys)))
            <=> PAIRWISE f (CONS y (APPEND ys (CONS x xs))))`,
     REWRITE_TAC [PAIRWISE;PAIRWISE_APPEND;MEM;MEM_APPEND;GSYM ALL_MEM]
      THEN MESON_TAC []) in
  let lemma = 
    prove
      (`!p ps q qs. simple_polygon 'a (([p] ^ (ps  ^ [q])) ^ (ps' ^ [p]))
         <=> simple_polygon 'a (([q] ^ (ps' ^ [p])) ^ (ps  ^ [q]))`,
       REWRITE_TAC [simple_polygon]
         THEN SIMP_TAC [BUTLAST_APPEND;APPEND_EQ_NIL;NOT_CONS_NIL]
         THEN REWRITE_TAC [ALL_DISTINCT_CARD;SET_OF_LIST_APPEND
                          ;UNION_ACI;LENGTH;LENGTH_APPEND;ADD_CLAUSES;ADD_SYM 
                          ;BUTLAST]
         THEN SIMP_TAC [ADJACENT_APPEND;APPEND;NOT_CONS_NIL
                       ;APPEND_EQ_NIL;BUTLAST_APPEND]
         THEN SIMP_TAC [HD_APPEND;NOT_CONS_NIL;APPEND_EQ_NIL;HD;LAST_APPEND
                       ;LAST;LAMBDA_PAIR_THM']
         THEN REWRITE_TAC [ADJACENT_CLAUSES;APPEND;LAMBDA_PAIR_THM'
                          ;MEM;MEM_APPEND]
         THEN SIMP_TAC [lemma;CONJ_ACI;EQ_SYM_EQ]
         THEN MESON_TAC []) in
  prove (`!p q ps ps' 'a.
            simple_polygon 'a ([p] ^ ps ^ [q] ^ ps' ^ [p])
            = simple_polygon 'a ([q] ^ ps' ^ [p] ^ ps ^ [q])`,
         REWRITE_TAC [REWRITE_RULE [APPEND_ASSOC] lemma]);;

let simple_polygon_lt_3 = prove
  (`!Ps 'a. simple_polygon 'a Ps ==> 3 < LENGTH Ps`,
   REPEAT GEN_TAC THEN REWRITE_TAC [simple_polygon;LE_LT;IMP_CONJ]
     THEN STRIP_TAC THEN ASM_REWRITE_TAC []
     THEN POP_ASSUM (REPEAT_TCL CHOOSE_THEN SUBST1_TAC
                       o CONV_RULE (ONCE_DEPTH_CONV LENGTH_EQ_CONV)
                       o ONCE_REWRITE_RULE [EQ_SYM_EQ])
     THEN SIMP_TAC [HD;LAST;NOT_CONS_NIL;ADJACENT_CLAUSES;MEM;PAIR_EQ;PAIRWISE;
                    ALL;BET_SYM;BUTLAST]
     THEN MESON_TAC [three]);;

let rotation_of = new_definition
  `rotation_of Ps Qs <=>
     ?P:point Q Ps' Ps''. Ps = [P] ^ Ps' ^ [Q] ^ Ps'' ^ [P]
                          /\ Qs = [Q] ^ Ps'' ^ [P] ^ Ps' ^ [Q]
                          \/ Ps = Qs`;;

(* If we can see the polygon's first vertex, then we can rotate the polygon so
   that we see its first wall. *)
let rotate_to_wall = theorem
  "!P Ps 'a X.
     simple_polygon 'a (P :: Ps)
     /\ on_plane X 'a
     /\ ~on_polyseg (P :: Ps) X
     /\ (!Z. between P Z X ==> ~on_polyseg (P :: Ps) Z)
     ==> ?hand' Q Qs R. rotation_of (P :: Ps) (Q :: R :: Qs)
                        /\ between Q hand' R
                        /\ !Z. between hand' Z X
                               ==> ~on_polyseg (Q :: R :: Qs) Z"
  [fix ["P:point";"Ps:point list";"'a:plane";"X:point"]
  ;assume "simple_polygon 'a (P :: Ps)" at [0]
  ;assume "on_plane X 'a" at [1]
  ;assume "~on_polyseg (CONS P Ps) X" at [2]
  ;assume "!Z. between P Z X ==> ~on_polyseg (CONS P Ps) Z" at [3]
  ;so consider ["Q:point";"Qs:point list"]
     st "Ps = Qs ^ [Q; P]" at [4] proof
     [hence "3 <= LENGTH (P :: Ps)" from [0] by [simple_polygon]
     ;hence "... <= SUC (LENGTH Ps)" by [LENGTH]
     ;hence "2 <= LENGTH Ps" using ARITH_TAC_THMS
     ;so consider ["Qs:point list";"Rs:point list"]
       st "Ps = Qs ^ Rs /\ LENGTH Rs = 2"
       by [CHOOSE_SUFFIX] at [4]
     ;so consider ["Q:point";"R:point"] st "Rs = [Q;R]"
       using (MESON_TAC o map (CONV_RULE (ONCE_DEPTH_CONV LENGTH_EQ_CONV)))
     ;take ["Q:point";"Qs"]
     ;qed from [0;4] using (MESON_TAC o mutual_simp)
       by [simple_polygon;HD;LAST;APPEND_EQ_NIL;NOT_CONS_NIL;LAST_APPEND
          ;APPEND_EQ;LENGTH;CONS_11]]
  ;hence "simple_polygon 'a (Q :: P :: Qs ^ [Q])
          /\ ~on_polyseg (Q :: P :: Qs ^ [Q]) X
          /\ !Z. between P Z X ==> ~on_polyseg (Q :: P :: Qs ^ [Q]) Z"
     from [0;2;3] by [REWRITE_RULE [APPEND;APPEND_NIL;GSYM APPEND_ASSOC]
                         (SPECL [`P:point`;`Q:point`;`Qs:point list`
                                ;`[]:point list`;`'a:plane`]
                            rotate_simple_polygon)
                     ;REWRITE_RULE [APPEND;APPEND_NIL;GSYM APPEND_ASSOC]
                       (SPECL [`P:point`;`Q:point`;`Qs:point list`
                              ;`[]:point list`]
                          rotate_polyseg)]
     at [5]
  ;have "~(Qs = [])" proof
   [otherwise assume "Qs = []"
   ;hence "LENGTH (P :: Ps) = 3"
     by [LENGTH;LENGTH_APPEND;ADD_CLAUSES] from [4]
     using (K (CONV_TAC (REDEPTH_CONV num_CONV))
              THEN' REWRITE_TAC THEN' MESON_TAC)
   ;qed from [0] by [simple_polygon_lt_3;LT_REFL]]
  ;so consider ["R:point";"Rs:point list"]
     st "Qs = R :: Rs" by [list_CASES] at [6]
  ;hence "simple_polygon 'a (Q :: P :: R :: Rs ^ [Q])
          /\ ~on_polyseg (Q :: P :: R :: Rs ^ [Q]) X
          /\ !Z. between P Z X ==> ~on_polyseg (Q :: P :: R :: Rs ^ [Q]) Z" 
     by [APPEND] from [5] at [7]
  ;consider ["Y:point"]
     st "(between Q Y P \/ between P Y R)
         /\ ~(?Z. between X Z Y
                  /\ on_polyseg (Q :: P :: R :: (Rs ^ [Q])) Z)" at [8]
     proof
     [tactics
         [REWRITE_TAC [] THEN MATCH_MP_TAC vertex_to_wall
            THEN EXISTS_TAC `'a:plane`
            THEN USE_THEN "1" MP_TAC
            THEN USE_THEN "7" MP_TAC
            THEN SIMP_TAC [simple_polygon;BUTLAST;APPEND_EQ_NIL;NOT_CONS_NIL
                          ;ADJACENT_CLAUSES;MEM;MEM_APPEND;PAIR_EQ;ALL
                          ;PAIRWISE;on_polyseg;BUTLAST_APPEND;APPEND_EQ_NIL
                          ;GSYM ALL_MEM;APPEND_NIL;FORALL_PAIR_THM]
            THEN MESON_TAC []]]
  ;take ["Y"]
  ;per cases
    [[suppose "between Q Y P" at [9]
     ;take ["Q";"R :: Rs ^ [Q]";"P:point"]
     ;hence "between Q Y P
             /\ !Z. between X Z Y
                    ==> ~on_polyseg (CONS Q (CONS P (R :: (Rs ^ [Q])))) Z"
       from [8;9] by [BET_SYM]
     ;unfolding from [this] by [rotation_of;BET_SYM]
     ;take ["P";"Q";"Qs";"[]:point list"]
     ;qed from [4;6] by [CONS_11;GSYM APPEND_ASSOC;APPEND]]
    ;[suppose "between P Y R" at [9]
     ;take ["P";"Rs ^ [Q;P]";"R"]
     ;have "!Z. between Y Z X
                ==> ~on_polyseg (CONS P (CONS R (Rs ^ [Q; P]))) Z"
       from [6;8]
       by [REWRITE_RULE [APPEND;APPEND_NIL;GSYM APPEND_ASSOC]
              (SPECL [`P:point`;`Q:point`;`Qs:point list`;`[]:point list`]
                 rotate_polyseg)
          ;APPEND;BET_SYM]
     ;unfolding (* Needed to unfold ^ and ::, otherwise qed won't rewrite the
                   goal to T. *)
     ;qed from [4;6;9] by [rotation_of;APPEND]]]
    from [8]];;

(* If a point has line of sight to the first wall of a simple polygon, then it
   has a path to a point with line of sight to any other wall. *)
let polygon_move_to_infix = theorem
  "!Qs P1 P2 Ps Q1 Q2 Rs hand X.
   simple_polygon 'a (CONS P1 (CONS P2 Ps))
   /\ CONS P1 (CONS P2 Ps) = APPEND Qs (CONS Q1 (CONS Q2 Rs))
   /\ on_plane X 'a
   /\ between P1 hand P2
   /\ ~on_polyseg (CONS P1 (CONS P2 Ps)) X
   /\ ~(?Y. between X Y hand
   /\ on_polyseg (CONS P1 (CONS P2 Ps)) Y)
   ==> ?hand' X'.
         seg_connected 'a (on_polyseg (CONS P1 (CONS P2 Ps))) X X'
         /\ between Q1 hand' Q2
         /\ ~on_polyseg (CONS P1 (CONS P2 Ps)) X'
         /\ ~(?Y. between X' Y hand'
                  /\ on_polyseg (CONS P1 (CONS P2 Ps)) Y)"
  [MATCH_MP_TAC list_INDUCT THEN CONJUNCTS_TAC parts
      [[thus thesis by [seg_connected_refl;APPEND;CONS_11]]
      ;[tactics [X_GEN_TAC `h:point` THEN X_GEN_TAC `t:point list`
                    THEN DISCH_THEN (LABEL_TAC "0")]
       ;fix ["P1:point";"P2:point";"Ps:point list"]
       ;fix ["Q1:point";"Q2:point"]
       ;fix ["Rs:point list";"hand:point";"X:point"]
       ;assume "simple_polygon 'a (CONS P1 (CONS P2 Ps))" at [1]
       ;so consider ["P3:point";"Ps':point list"]
         st "Ps = CONS P3 (APPEND Ps' [P1])" at [2] proof
         [have "~(Ps = [])" proof
             [otherwise assume "Ps = []"
             ;qed from [1] by [ARITH_RULE `~(3 <= SUC (SUC 0))`
                              ;LENGTH;simple_polygon;LE_SUC;LE]
               using (MESON_TAC o mutual_rewrite)]
         ;so consider ["P3:point";"Ps':point list"]
           st "Ps = CONS P3 Ps'" by [list_CASES] at [2]
         ;have "~(Ps' = [])" proof
           [otherwise assume "Ps' = []"
           ;qed from [1;2] by [ARITH_RULE `~(3 < SUC (SUC (SUC 0)))`
                              ;LENGTH;simple_polygon_lt_3]]
         ;so consider ["PL:point";"Ps'':point list"]
           st "Ps' = APPEND Ps'' [PL]" from [2] by [list_CASES_APPEND] at [3]
         ;hence "PL = P1" by [simple_polygon;HD;LAST;LAST_APPEND
                             ;NOT_CONS_NIL;APPEND_EQ_NIL]
           from [1;2] using (MESON_TAC o mutual_rewrite)
         ;qed from [2;3]]
       ;assume "on_plane X 'a" at [3]
       ;assume "between P1 hand P2" at [4]
       ;assume "~on_polyseg (CONS P1 (CONS P2 (CONS P3 (APPEND Ps' [P1])))) X"
        at [5] from [2]
       ;assume "~(?Y. between X Y hand
                      /\ on_polyseg (CONS P1 (CONS P2 (CONS P3
                                       (APPEND Ps' [P1])))) Y)" at [6] from [2]
       ;consider ["hand':point";"X':point"]
         st "seg_connected 'a
                   (on_polyseg (CONS P1 (CONS P2 (CONS P3 (APPEND Ps' [P1])))))
                   X X'
             /\ between P2 hand' P3
             /\ ~on_polyseg (CONS P1 (CONS P2 (CONS P3 (APPEND Ps' [P1])))) X'
             /\ ~(?Y. between X' Y hand'
                          /\ on_polyseg (CONS P1 (CONS P2 (CONS P3
                                             (APPEND Ps' [P1])))) Y)"
         at [7;8;9;10] proof
         [tactics
             [MATCH_MP_TAC polygon_move THEN EXISTS_TAC `hand:point`
                 THEN REMOVE_THEN "1" MP_TAC THEN ASM_REWRITE_TAC []
                 THEN SIMP_TAC [simple_polygon;on_polyseg;MEM;MEM_APPEND
                               ;BUTLAST;BUTLAST_APPEND;APPEND;APPEND_EQ_NIL
                               ;NOT_CONS_NIL;PAIRWISE;ALL;PAIRWISE;GSYM ALL_MEM
                               ;ADJACENT_CONS;PAIR_EQ;FORALL_PAIR_THM]
                 THEN MESON_TAC []]]
       ;assume "CONS P1 (CONS P2 (CONS P3 (APPEND Ps' [P1])))
                = APPEND (CONS h t) (CONS Q1 (CONS Q2 Rs))" at [11]
         from [2]
       ;consider ["hand'':point";"X'':point"]
         st "seg_connected 'a
                (on_polyseg
                   (CONS P2 (CONS P3 (APPEND (APPEND Ps' [P1]) [P2])))) X' X'' 
             /\ between Q1 hand'' Q2
             /\ ~on_polyseg
                    (CONS P2 (CONS P3 (APPEND (APPEND Ps' [P1]) [P2]))) X'' 
             /\ ~(?Y. between X'' Y hand'' 
                    /\ on_polyseg
                         (CONS P2 (CONS P3 (APPEND (APPEND Ps' [P1]) [P2]))) Y)"
         proof
         [tactics
             [FIRST_ASSUM MATCH_MP_TAC
                 THEN EXISTS_TAC `APPEND Rs [P2:point]`
                 THEN EXISTS_TAC `hand':point`
                 THEN REWRITE_TAC
                 [GSYM (REWRITE_RULE [APPEND_NIL;APPEND]
                          (SPECL [`P1:point`;`P2:point`;`[]:point list`
                                 ;`CONS P3 Ps':point list`] rotate_polyseg))
                 ;GSYM (REWRITE_RULE [APPEND_NIL;APPEND]
                          (SPECL [`P1:point`;`P2:point`;`[]:point list`
                                 ;`CONS P3 Ps':point list`]
                             rotate_simple_polygon))]
                 THEN FULL_REWRITE_TAC []
                 THEN POP_ASSUM MP_TAC
                 THEN REWRITE_TAC [APPEND;CONS_11;IMP_CONJ]
                 THEN SIMP_TAC
                 [MESON [APPEND]
                     `CONS P2 (CONS P3 (APPEND (APPEND Ps' [P1]) [P2]))
                   = APPEND (CONS P2 (CONS P3 (APPEND Ps' [P1]))) [P2]`]
                 THEN REWRITE_TAC [GSYM APPEND_ASSOC;APPEND]
                 THEN ASM_MESON_TAC [seg_connected;MEM;MEM_LAST]]]
       ;qed from [2;7]
         by [REWRITE_RULE [APPEND_NIL;APPEND]
                (SPECL
                   [`P1:point`;`P2:point`;`[]:point list`
                   ;`CONS P3 Ps':point list`] rotate_polyseg)
            ;seg_connected_trans]]]];;

let ROTATE_EQ = prove
  (`!P Ps 'a. simple_polygon 'a (CONS P Ps)
             ==> (rotation_of (CONS P Ps) (CONS P Qs) <=> Ps = Qs)`,
   REPEAT GEN_TAC THEN REWRITE_TAC [rotation_of]
     THEN DISCH_TAC THEN EQ_TAC THENL
     [STRIP_TAC THENL
         [REPEAT (POP_ASSUM MP_TAC) THEN REWRITE_TAC [GSYM APPEND_ASSOC]
             THEN REWRITE_TAC [APPEND;CONS_11] THEN DISCH_TAC
             THEN REWRITE_TAC [IMP_CONJ] THEN REPEAT (DISCH_THEN SUBST_ALL_TAC) 
             THEN POP_ASSUM MP_TAC
             THEN SIMP_TAC  [simple_polygon;PAIRWISE;BUTLAST;APPEND_EQ_NIL
                            ;NOT_CONS_NIL;BUTLAST_APPEND;ALL_APPEND;ALL]
         ;FULL_REWRITE_TAC [CONS_11]]
     ;SIMP_TAC []]);;

let ROT_VERTEX_TO_FRONT = prove
  (`!'a P Ps. simple_polygon 'a Ps
              ==> (MEM P Ps <=> ?Qs. rotation_of Ps (CONS P Qs))`,
   REPEAT STRIP_TAC THEN EQ_TAC THENL
     [REWRITE_TAC [MEM_IS_INFIX;APPEND] THEN STRIP_TAC
         THEN REPEAT (POP_ASSUM MP_TAC)
         THEN REWRITE_TAC [TAUT `p ==> q ==> r <=> q ==> p ==> r`]
         THEN STRUCT_CASES_TAC (ISPEC `ys:point list` list_CASES) THENL
         [STRUCT_CASES_TAC (ISPEC `zs:point list` list_CASES_APPEND) THENL
             [SIMP_TAC [simple_polygon;APPEND;LENGTH]
                 THEN CONV_TAC (REDEPTH_CONV num_CONV)
                 THEN REWRITE_TAC [LE;LE_SUC;NOT_SUC]
             ;STRUCT_CASES_TAC (ISPEC `pre:point list` list_CASES) THENL
               [SIMP_TAC [simple_polygon;APPEND;LENGTH]
                   THEN CONV_TAC (REDEPTH_CONV num_CONV)
                   THEN REWRITE_TAC [LE;LE_SUC;NOT_SUC]
               ;REWRITE_TAC [APPEND]
                 THEN MESON_TAC [rotation_of]]]
         ;STRUCT_CASES_TAC (ISPEC `zs:point list` list_CASES_APPEND) THENL
           [SIMP_TAC [APPEND;simple_polygon;HD;LAST;LAST_APPEND;NOT_CONS_NIL
                     ;APPEND_EQ_NIL] THEN MESON_TAC [rotation_of]
           ;SIMP_TAC [APPEND;simple_polygon;HD;LAST;LAST_APPEND;NOT_CONS_NIL
                     ;APPEND_EQ_NIL]
             THEN REWRITE_TAC [rotation_of] THEN REPEAT DISCH_TAC
             THEN EXISTS_TAC `APPEND (pre:point list) (CONS h (APPEND t [P]))`
             THEN EXISTS_TAC `h:point` THEN EXISTS_TAC `P:point`
             THEN EXISTS_TAC `t:point list` THEN EXISTS_TAC `pre:point list`
             THEN ASM_REWRITE_TAC [APPEND] THEN REWRITE_TAC [GSYM APPEND_ASSOC]
             THEN REWRITE_TAC [APPEND]]]
     ;REWRITE_TAC [rotation_of] THEN REPEAT STRIP_TAC
       THEN FULL_REWRITE_TAC [GSYM APPEND_ASSOC]
       THEN FULL_REWRITE_TAC [APPEND;CONS_11;MEM;MEM_APPEND]]);;

let ROT_ADJACENT_TO_FRONT = prove
  (`!P Ps 'a. simple_polygon 'a Ps
              ==> (MEM (P,Q) (ADJACENT Ps)
                  <=> ?Qs. rotation_of Ps (CONS P (CONS Q Qs)))`,
   REWRITE_TAC [MEM_ADJACENT_IS_INFIX] THEN REPEAT STRIP_TAC
     THEN EQ_TAC THENL
     [STRIP_TAC THEN REPEAT (POP_ASSUM MP_TAC)
         THEN STRUCT_CASES_TAC (ISPEC `ys:point list` list_CASES) THENL
         [REWRITE_TAC [APPEND] THEN MESON_TAC [rotation_of]
         ;STRUCT_CASES_TAC (ISPEC `zs:point list` list_CASES_APPEND) THENL
           [ONCE_REWRITE_TAC [TAUT `p ==> q ==> r <=> q ==> p ==> r`]
               THEN DISCH_THEN SUBST1_TAC THEN DISCH_TAC
               THEN SUBGOAL_THEN `h:point = Q` SUBST_ALL_TAC
               THENL [POP_ASSUM MP_TAC
                         THEN SIMP_TAC [simple_polygon;APPEND;HD;LAST
                                       ;LAST_APPEND;APPEND_EQ_NIL;NOT_CONS_NIL]
                     ;ALL_TAC]
               THEN EXISTS_TAC `APPEND t [P:point]`
               THEN REWRITE_TAC [rotation_of] THEN EXISTS_TAC `Q:point`
               THEN EXISTS_TAC `P:point` THEN EXISTS_TAC `t:point list`
               THEN EXISTS_TAC `[]:point list`
               THEN REWRITE_TAC [APPEND_NIL;APPEND]
               THEN REWRITE_TAC [GSYM APPEND_ASSOC] THEN REWRITE_TAC [APPEND]
           ;ONCE_REWRITE_TAC [TAUT `p ==> q ==> r <=> q ==> p ==> r`]
             THEN DISCH_THEN SUBST1_TAC THEN DISCH_TAC
                 THEN SUBGOAL_THEN `h:point = last` SUBST_ALL_TAC THENL
                   [POP_ASSUM MP_TAC
                       THEN SIMP_TAC [simple_polygon;APPEND;HD;LAST;LAST_APPEND
                                     ;APPEND_EQ_NIL;NOT_CONS_NIL]
                   ;ALL_TAC]
                   THEN EXISTS_TAC
                   `APPEND pre (CONS last (APPEND t [P])):point list`
                   THEN REWRITE_TAC [rotation_of] THEN EXISTS_TAC `last:point`
                   THEN EXISTS_TAC `P:point` THEN EXISTS_TAC `t:point list`
                   THEN EXISTS_TAC `CONS Q pre:point list`
                   THEN REWRITE_TAC [APPEND]
                   THEN REWRITE_TAC [GSYM APPEND_ASSOC]
                   THEN REWRITE_TAC [APPEND]]]
     ;REWRITE_TAC [rotation_of] THEN STRIP_TAC THENL
       [REPEAT (POP_ASSUM MP_TAC)
           THEN STRUCT_CASES_TAC (ISPEC `Ps'':point list` list_CASES) THENL
           [REWRITE_TAC [APPEND;APPEND_NIL;CONS_11] THEN REPEAT DISCH_TAC
               THEN FULL_REWRITE_TAC []
               THEN EXISTS_TAC `CONS P' Ps':point list`
               THEN EXISTS_TAC `[]:point list`
               THEN REWRITE_TAC [GSYM APPEND_ASSOC]
               THEN REWRITE_TAC [APPEND]
           ;SIMP_TAC [APPEND;CONS_11] THEN REPEAT DISCH_TAC
             THEN EXISTS_TAC `CONS P' Ps':point list`
             THEN EXISTS_TAC `APPEND t [P']:point list`
             THEN REWRITE_TAC [APPEND] THEN REWRITE_TAC [GSYM APPEND_ASSOC]
             THEN REWRITE_TAC [APPEND]]
       ;EXISTS_TAC `[]:point list` THEN EXISTS_TAC `Qs:point list`
         THEN ASM_REWRITE_TAC [APPEND]]]);;

let ROTATE_MEM_EQ = prove
  (`!Ps Qs x. rotation_of Ps Qs ==> (MEM x Ps <=> MEM x Qs)`,
   REWRITE_TAC [rotation_of] THEN REPEAT STRIP_TAC
     THEN ASM_REWRITE_TAC [MEM;MEM_APPEND] THEN MESON_TAC []);;

let ROTATE_MEM_ADJACENT_EQ =
  let lemma = REWRITE_RULE []
    (prove
       (`[P] ^ Ps ^ [Q] ^ Qs ^ [P] = ([P] ^ Ps) ^ (CONS Q (Qs ^ [P]))`,
        REWRITE_TAC [GSYM APPEND_ASSOC]
          THEN REWRITE_TAC [APPEND])) in
  prove
    (`!Ps Qs x. rotation_of Ps Qs ==> (MEM x (ADJACENT Ps) <=> MEM x (ADJACENT Qs))`,
     REWRITE_TAC [rotation_of] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [lemma]
       THEN ONCE_REWRITE_TAC [ADJACENT_MIDDLE]
       THEN REWRITE_TAC [MEM_APPEND;APPEND;DISJ_ACI]);;

let simple_polygon_rotation = prove
  (`!Ps Qs 'a. simple_polygon 'a Ps /\ rotation_of Ps Qs
               ==> simple_polygon 'a Qs`,
   REWRITE_TAC [rotation_of]
     THEN MESON_TAC [REWRITE_RULE [] rotate_simple_polygon]);;

let polyseg_rotation = prove
  (`!Ps Qs 'a. rotation_of Ps Qs
               ==> on_polyseg Ps = on_polyseg Qs`,
   REWRITE_TAC [rotation_of]
     THEN MESON_TAC [REWRITE_RULE [] rotate_polyseg]);;

let ROTATE_EQ2 = prove
  (`!P Ps Qs 'a. simple_polygon 'a Ps
                ==> HD Ps = HD Qs
                ==> (rotation_of Ps Qs <=> Ps = Qs)`,
   REPEAT GEN_TAC THEN STRUCT_CASES_TAC (ISPEC `Ps:point list` list_CASES)
     THENL [REWRITE_TAC [simple_polygon;LENGTH] THEN ARITH_TAC;ALL_TAC]
     THEN STRUCT_CASES_TAC (ISPEC `Qs:point list` list_CASES)
     THENL [ASM_REWRITE_TAC [rotation_of;EQ_SYM_EQ;APPEND_EQ_NIL;NOT_CONS_NIL]
           ;ALL_TAC]
     THEN REWRITE_TAC [HD] THEN DISCH_TAC THEN DISCH_THEN SUBST_ALL_TAC
     THEN REWRITE_TAC [CONS_11] THEN ASM_MESON_TAC [ROTATE_EQ]);;

let simple_polygon_rotate_eq = REWRITE_RULE []
  (prove
     (`!p q xs ys.
         simple_polygon 'a ([p] ^ xs ^ [q] ^ ys ^ [p])
         ==> [p] ^ xs ^ [q] ^ ys ^ [p] = [p] ^ ws ^ [q] ^ zs ^ [p]
         ==> xs = ws /\ ys = zs`,
      REPEAT GEN_TAC THEN REWRITE_TAC [GSYM APPEND_ASSOC]
        THEN REWRITE_TAC [APPEND;CONS_11]
        THEN REWRITE_TAC [GSYM (CONJUNCT2 APPEND)]
        THEN REWRITE_TAC [APPEND_ASSOC] THEN SIMP_TAC [APPEND_EQ_2;LENGTH]
        THEN REWRITE_TAC [simple_polygon]
        THEN SIMP_TAC [BUTLAST_APPEND;NOT_CONS_NIL;APPEND_EQ_NIL
                      ;BUTLAST;APPEND_NIL;PAIRWISE;PAIRWISE_APPEND;ALL;MEM]
        THEN DISCH_TAC THEN MATCH_MP_TAC PAIRWISE_INFIX_EQ
        THEN SIMP_TAC [PAIRWISE;PAIRWISE_APPEND;ALL;MEM]
        THEN FULL_REWRITE_TAC [GSYM ALL_MEM]));;

(* This was a surprisingly challenging proof, requiring a fair bit of pen and
   paper reasoning, which is frustrating given how close we are to the
   end. Note that it could be moved into the theory of lists, since the
   assumption that Ps is a simple polygon can be weakened to saying that the
   elements of Ps are pairwise distinct. *)
let rotation_of_trans = theorem
  "simple_polygon 'a Ps
   ==> rotation_of Ps Qs /\ rotation_of Qs Rs ==> rotation_of Ps Rs"
  [assume "simple_polygon 'a Ps" at [0]
  ;assume "rotation_of Ps Qs /\ rotation_of Qs Rs" at [1;2]
  ;hence "simple_polygon 'a Qs" from [0;1]
     at [3] by [simple_polygon_rotation]
  ;assume "~(Ps = Qs) /\ ~(Qs = Rs)" at [4] from [1;2]
  ;so consider ["P:point";"Q:point";"xs:point list";"ys:point list"]
       st "Ps = [P] ^ xs ^ [Q] ^ ys ^ [P]
           /\ Qs = [Q] ^ ys ^ [P] ^ xs ^ [Q]" at [5;6]
       from [1] by [rotation_of]
  ;consider ["Q2:point";"R:point";"ws:point list";"zs:point list"]
     st "Qs = [Q2] ^ ws ^ [R] ^ zs ^ [Q2]
         /\ Rs = [R] ^ zs ^ [Q2] ^ ws ^ [R]"
     at [7;8] from [2;4] by [rotation_of]
  ;have "Q:point = Q2" at [9] proof
    [tactics [USE_THEN "6" MP_TAC;USE_THEN "7" MP_TAC
             ;REWRITE_TAC [GSYM APPEND_ASSOC]
             ;SIMP_TAC [CONS_11;APPEND]]]
  ;per cases
    [[suppose "P = R" at [10]
     ;hence "ys = ws /\ xs = zs" from [3;6;7;9;10]
       by [simple_polygon_rotate_eq]
       using (MESON_TAC o mutual_rewrite)
     ;qed from [5;8;9;10] by [rotation_of]]
    ;[suppose "~(P = R)" at [10]
     ;hence "MEM P Qs" at [11] from [6] by [MEM;MEM_APPEND]
     ;have "~(P = Q)" from [0;5]
       by [BUTLAST_APPEND;BUTLAST;NOT_CONS_NIL;APPEND_EQ_NIL
          ;PAIRWISE_APPEND;PAIRWISE;ALL;ALL_APPEND;MEM;MEM_APPEND
          ;simple_polygon]
       using (MESON_TAC o mutual_simp)
     ;hence "MEM P ws \/ MEM P zs"
       from [7;9;10;11] by [MEM;MEM_APPEND]
       using (MESON_TAC o mutual_rewrite) at [12]
     ;per cases
       [[suppose "MEM P ws"
        ;so consider ["ws':point list";"ws'':point list"]
          st "ws = APPEND ws' (CONS P ws'')" by [MEM_IS_INFIX]
          at [13]
        ;hence "Qs = [Q] ^ ws' ^ [P] ^ (ws'' ^ [R] ^ zs) ^ [Q]" proof
          [tactics
              [USE_THEN "7" MP_TAC;USE_THEN "9" MP_TAC
              ;POP_ASSUM MP_TAC;SIMP_TAC [GSYM APPEND_ASSOC]
              ;REWRITE_TAC [APPEND]]]
        ;hence "ys = ws' /\ xs = ws'' ^ [R] ^ zs" 
          from [3;6] by [simple_polygon_rotate_eq]
          using (MESON_TAC o mutual_rewrite)
        ;unfolding by [rotation_of]
        ;take ["P";"R";"ws''";"zs ^ [Q] ^ ws'"]
        ;unfolding from [5;8;9;13;this]
        ;tactics
          [REWRITE_TAC [GSYM APPEND_ASSOC]
          ;REWRITE_TAC [APPEND]]]
       ;[suppose "MEM P zs"
        ;so consider ["zs':point list";"zs'':point list"]
          st "zs = APPEND zs' (CONS P zs'')" by [MEM_IS_INFIX]
          at [13]
        ;hence "Qs = [Q] ^ (ws ^ [R] ^ zs') ^ [P] ^ zs'' ^ [Q]" proof
          [tactics
              [USE_THEN "7" MP_TAC;USE_THEN "9" MP_TAC
              ;POP_ASSUM MP_TAC;SIMP_TAC [GSYM APPEND_ASSOC]
              ;REWRITE_TAC [APPEND]]]
        ;hence "ys = ws ^ [R] ^ zs' /\ xs = zs''"
          from [3;6] by [simple_polygon_rotate_eq]
          using (MESON_TAC o mutual_rewrite)
        ;unfolding by [rotation_of]
        ;take ["P";"R";"zs'' ^ [Q] ^ ws";"zs'"]
        ;unfolding from [5;8;9;13;this]
        ;tactics
          [REWRITE_TAC [GSYM APPEND_ASSOC]
          ;REWRITE_TAC [APPEND]]]]
       from [this]]]];;

let rotation_of_sym = prove
  (` rotation_of Ps Qs <=> rotation_of Qs Ps`,
   MESON_TAC [rotation_of]);;

(* All points in the plane not on a simple polygon have line of sight to a
   wall. *)
let sight_to_wall = theorem
  "!'a Ps X. simple_polygon 'a Ps
       /\ on_plane X 'a /\ ~on_polyseg Ps X
       ==> ?P Q hand. MEM (P,Q) (ADJACENT Ps)
                      /\ between P hand Q
                      /\ ~(?Y. between hand Y X /\ on_polyseg Ps Y)" 
  [fix ["'a:plane";"Ps:point list";"X:point"]
  ;assume "simple_polygon 'a Ps" at [0]
  ;consider ["P:point";"Ps':point list"] st "Ps = CONS P Ps'" at [1] proof
     [hence "~(Ps = [])" by [simple_polygon;ARITH_RULE `~(3 <= 0)`;LENGTH]
     ;qed by [list_CASES]]
  ;hence "on_polyseg Ps P" from [1] by [MEM;on_polyseg] at [2]
  ;assume "~on_polyseg Ps X" at [3]
  ;so consider ["hand:point"] st
     "on_polyseg Ps hand /\ (between X hand P \/ P = hand)
      /\ ~(?Y. between X Y hand /\ on_polyseg Ps Y)"
     from [2;3] by [ray_cast] using K (MATCH_MP_TAC ray_cast)
     at [4;5;6]
  ;so assume "MEM hand Ps" at [7] from [4] by [on_polyseg;BET_SYM]
  ;so consider ["Qs:point list"]
     st "rotation_of Ps (CONS hand Qs)"
     from [0] by [ROT_VERTEX_TO_FRONT] at [8]
  ;hence "simple_polygon 'a (CONS hand Qs)"
     from [0] by [simple_polygon_rotation] at [9]
  ;assume "on_plane X 'a"
  ;so consider ["hand':point";"Q:point";"Rs:point list";"R:point"]
     st "rotation_of (CONS hand Qs) (CONS Q (CONS R Rs))
         /\ between Q hand' R
         /\ !Y. between hand' Y X ==> ~on_polyseg (CONS Q (CONS R Rs)) Y"
     from [3;6;8;9] by [polyseg_rotation;BET_SYM]
     using K (MATCH_MP_TAC (REWRITE_RULE [] rotate_to_wall))
     at [10;11;12]
  ;have "MEM P (CONS Q (CONS R Rs))"
     from [1;8;10] by [MEM;ROTATE_MEM_EQ]
  ;so consider ["Ss:point list"]
     st "rotation_of (CONS Q (CONS R Rs)) (CONS P Ss)"
     from [9;10] by [simple_polygon_rotation;ROT_VERTEX_TO_FRONT]
     at [13]
  ;hence "rotation_of (CONS P Ps') (CONS P Ss)"
     from [0;1;8;10] by [rotation_of_sym;rotation_of_trans
                        ;simple_polygon_rotation]
  ;hence "Ps' = Ss" from [0;1] by [ROTATE_EQ] at [14]
  ;hence "rotation_of Ps (CONS Q (CONS R Rs))"
     from [1;13] by [rotation_of_sym] at [15]
  ;hence "MEM (Q,R) (ADJACENT Ps)"
     by [MEM;ROTATE_MEM_ADJACENT_EQ;ADJACENT_CLAUSES]
  ;take ["Q";"R";"hand'"]
  ;qed from [11;12;15] by [polyseg_rotation]];;

let simple_polygon_EXISTS = prove
  (`!'a Ps. simple_polygon 'a Ps
            ==> ?P1 P2 Ps'. Ps = CONS P1 (CONS P2 (APPEND Ps' [P1]))`,
   REPEAT GEN_TAC THEN STRUCT_CASES_TAC (ISPEC `Ps:point list` list_CASES) 
     THENL [REWRITE_TAC [simple_polygon;LENGTH] THEN ARITH_TAC;ALL_TAC]
     THEN STRUCT_CASES_TAC (ISPEC `t:point list` list_CASES)
     THENL [REWRITE_TAC [simple_polygon;LENGTH] THEN ARITH_TAC;ALL_TAC]
     THEN STRUCT_CASES_TAC (ISPEC `t':point list` list_CASES_APPEND)
     THENL [REWRITE_TAC
               [CONS_11;APPEND_EQ_NIL;EQ_SYM_EQ;NOT_CONS_NIL
               ;simple_polygon;LENGTH] THEN ARITH_TAC
           ;ALL_TAC]
     THEN SIMP_TAC [CONS_11;APPEND_EQ_2;LENGTH]
     THEN REWRITE_TAC [simple_polygon]
     THEN SIMP_TAC [LAST;LAST_APPEND;NOT_CONS_NIL;APPEND_EQ_NIL;HD]
     THEN MESON_TAC []);;

(* If a point in the plane has line of sight to a wall, then there is a path
   to a point with line of sight to the first wall. *)
let move_to_front = theorem
  "!'a Ps X P Q hand.
   simple_polygon 'a Ps
   /\ on_plane X 'a /\ ~on_polyseg Ps X
   /\ MEM (P,Q) (ADJACENT Ps) /\ between P hand Q
   /\ ~(?Y. between hand Y X /\ on_polyseg Ps Y)
   ==> ?hand' X'. seg_connected 'a (on_polyseg Ps) X X'
                  /\ between (HD Ps) hand' (HD (TL Ps))
                  /\ ~on_polyseg Ps X'
                  /\ ~(?Y. between hand' Y X' /\ on_polyseg Ps Y)"
  [fix ["'a:plane";"Ps:point list";"X:point";"P:point";"Q:point";"hand:point"]
  ;assume "simple_polygon 'a Ps" at [0]
  ;so consider ["P1:point";"P2:point";"Ps':point list"]
     st "Ps = CONS P1 (CONS P2 (APPEND Ps' [P1]))" at [1]
     by [simple_polygon_EXISTS]
  ;assume "on_plane X 'a" at [2]
  ;assume "~on_polyseg Ps X" at [3]
  ;assume "MEM (P,Q) (ADJACENT Ps)"
  ;so consider ["Qs:point list";"Rs:point list"]
     st "Ps = APPEND Qs (CONS P (CONS Q Rs))"
     by [MEM_ADJACENT_IS_INFIX] at [4]
  ;per cases
    [[suppose "Qs = []"
     ;hence "P = P1 /\ Q = P2" from [1;4] by [CONS_11;APPEND]
     ;qed from [1;2;3] by [seg_connected_refl;HD;TL]]
    ;[suppose "~(Qs = [])"
     ;so consider ["P1':point";"Qs':point list"] 
       st "Qs = CONS P1' Qs'" by [list_CASES]
     ;hence "Qs = CONS P1 Qs'" by [APPEND;CONS_11] from [1;4] at [5]
     ;have "Ps = [P1] ^ Qs' ^ [P] ^ (BUTLAST (CONS Q Rs)) ^ [P1]" proof
       [per cases
           [[suppose "Rs = []"
            ;tactics [REWRITE_TAC [GSYM APPEND_ASSOC]]
            ;qed from [0;4;5]
              by [APPEND;BUTLAST;CONS_11;APPEND_EQ_2;LENGTH
                 ;simple_polygon;HD;LAST;LAST_APPEND;NOT_CONS_NIL
                 ;APPEND_EQ_NIL;HD_APPEND]
              using ((SIMP_TAC THEN' MESON_TAC) o mutual_simp)]
           ;[suppose "~(Rs = [])"
            ;so consider ["P1'':point";"Rs':point list"]
              st "Rs = APPEND Rs' [P1'']" by [list_CASES_APPEND]
            ;tactics [REWRITE_TAC [GSYM APPEND_ASSOC]
                     ;USE_THEN "0" MP_TAC;USE_THEN "4" MP_TAC
                     ;USE_THEN "5" MP_TAC;POP_ASSUM MP_TAC
                     ;SIMP_TAC [BUTLAST;APPEND;APPEND_EQ_NIL;NOT_CONS_NIL
                               ;BUTLAST_APPEND;APPEND_NIL;simple_polygon
                               ;HD;LAST;APPEND_EQ_NIL;NOT_CONS_NIL;LAST_APPEND]]]]]
     ;hence "rotation_of Ps ([P] ^ BUTLAST (CONS Q Rs) ^ [P1] ^ Qs' ^ [P])"
       by [rotation_of] at [6]
     ;consider ["Ss:point list"] 
       st "rotation_of Ps (CONS P (CONS Q Ss))" at [7] proof
       [so assume "Rs = []" at [7] by [BUTLAST;APPEND]
           using (MESON_TAC o mutual_rewrite)
         (* Just need to deal with the degenerate case. *)
       ;hence "LAST Ps = LAST (APPEND Qs [P;Q])" from [4]
       ;hence "P1 = Q" from [1]
         by [simple_polygon;HD;LAST;LAST_APPEND;NOT_CONS_NIL;APPEND_EQ_NIL]
         using (MESON_TAC o mutual_simp)
       ;qed from [6;7] by [BUTLAST;APPEND]
         using (MESON_TAC o mutual_rewrite)]
     ;have "MEM (P1,P2) (ADJACENT Ps)" from [1] by [ADJACENT_CLAUSES;MEM]
     ;hence "MEM (P1,P2) (ADJACENT (CONS P (CONS Q Ss)))"
       from [7] by [ROTATE_MEM_ADJACENT_EQ]
     ;so consider ["ws:point list";"zs:point list"]
       st "CONS P (CONS Q Ss) = APPEND ws (CONS P1 (CONS P2 zs))"
       by [MEM_ADJACENT_IS_INFIX] at [8]
     ;assume "between P hand Q /\ ~(?Y. between hand Y X /\ on_polyseg Ps Y)"
       at [9]
     ;so consider ["hand':point";"X':point"]
       st "seg_connected 'a (on_polyseg (CONS P (CONS Q Ss))) X X'
           /\ between P1 hand' P2
           /\ ~on_polyseg (CONS P (CONS Q Ss)) X'
           /\ ~(?Y. between X' Y hand'
                    /\ on_polyseg (CONS P (CONS Q Ss)) Y)"
       from [0;2;3;7;8] by [BET_SYM]
       by [polyseg_rotation;simple_polygon_rotation]
       using K (MATCH_MP_TAC polygon_move_to_infix)
     ;take ["hand'";"X'"]
     ;qed from [1;7] by [polyseg_rotation;HD;TL;BET_SYM]]]];;

(* Putting the last few proofs together: for any point in the plane not on the
   simple polygon, there is a path to a point with line of sight to the first
   wall. *)
let any_to_front = prove
  (`!'a Ps X. simple_polygon 'a Ps 
              /\ on_plane X 'a /\ ~on_polyseg Ps X
              ==> ?hand' X'.
                     seg_connected 'a (on_polyseg Ps) X X' 
                     /\ between (HD Ps) hand' (HD (TL Ps))
                     /\ ~on_polyseg Ps X'
                     /\ ~(?Y. between hand' Y X' /\ on_polyseg Ps Y)`,
   REPEAT GEN_TAC THEN DISCH_TAC
     THEN FIRST_ASSUM (REPEAT_TCL CHOOSE_THEN ASSUME_TAC
                         o MATCH_MP sight_to_wall)
     THEN MATCH_MP_TAC move_to_front
     THEN ASM_MESON_TAC []);;

(* Of any three points on the plane of a simple polygon and not on the simple
   polygon, there is a path between two of them. In other words, a simple
   polygon separates its plane into at most 2 regions. *)
let jordan_poly2 = theorem
  "!'a Ps P Q R.
     simple_polygon 'a Ps
     /\ on_plane P 'a /\ on_plane Q 'a /\ on_plane R 'a
     /\ ~on_polyseg Ps P /\ ~on_polyseg Ps Q /\ ~on_polyseg Ps R
     ==> seg_connected 'a (on_polyseg Ps) P Q
         \/ seg_connected 'a (on_polyseg Ps) P R
         \/ seg_connected 'a (on_polyseg Ps) Q R"
  [fix ["'a:plane";"Ps:point list";"P:point";"Q:point";"R:point"]
  ;assume "simple_polygon 'a Ps" at [0]
  ;consider ["P1:point";"P2:point";"Ps':point list"]
     st "Ps = CONS P1 (CONS P2 Ps') /\ ~(P1 = P2)" at [1] proof
     [so consider ["P1:point";"P2:point";"Ps':point list"]
         st "Ps = CONS P1 (CONS P2 Ps') /\ ~(Ps' = [])"
         at [1] by [simple_polygon_EXISTS;APPEND_EQ_NIL;NOT_CONS_NIL]
     ;hence "~(P1 = P2)"
       by [BUTLAST;NOT_CONS_NIL;PAIRWISE;ALL;simple_polygon] from [0]
       using (MESON_TAC o mutual_simp)
     ;qed from [1]]
  ;assume "on_plane P 'a /\ on_plane Q 'a /\ on_plane R 'a" at [2]
  ;assume "~on_polyseg Ps P /\ ~on_polyseg Ps Q /\ ~on_polyseg Ps R" at [3]
  ;consider ["handP:point";"P':point"]
     st "seg_connected 'a (on_polyseg Ps) P P'
         /\ between (HD Ps) handP (HD (TL Ps))
         /\ ~on_polyseg Ps P'
         /\ ~(?X. between handP X P' /\ on_polyseg Ps X)"
     by [any_to_front] from [0;2;3] at [4]
  ;consider ["handQ:point";"Q':point"]
     st "seg_connected 'a (on_polyseg Ps) Q Q'
         /\ between (HD Ps) handQ (HD (TL Ps))
         /\ ~on_polyseg Ps Q'
         /\ ~(?X. between handQ X Q' /\ on_polyseg Ps X)"
     by [any_to_front] from [0;2;3] at [5]
  ;consider ["handR:point";"R':point"]
     st "seg_connected 'a (on_polyseg Ps) R R'
         /\ between (HD Ps) handR (HD (TL Ps))
         /\ ~on_polyseg Ps R'
         /\ ~(?X. between handR X R' /\ on_polyseg Ps X)"
     by [any_to_front] from [0;2;3] at [6]
  ;hence "between P1 handP P2 /\ between P1 handQ P2 /\ between P1 handR P2"
     from [1;4;5;6] by [HD;TL] at [7]
  ;consider ["a:line"] st "on_line P1 a /\ on_line P2 a" at [8] by [g11_weak]
  ;have "on_plane P1 'a /\ on_plane P2 'a /\ !P. MEM P Ps' ==> on_plane P 'a"
     from [0;1] by [simple_polygon;MEM] at [9]
  ;hence "!X. on_line X a ==> on_plane X 'a" from [1;8] by [g16]
  ;so consider ["hp:half_plane";"hq:half_plane"]
     st "~(hp = hq)
         /\ a = line_of_half_plane hp /\ a = line_of_half_plane hq
         /\ !P. on_plane P 'a
                <=> on_line P a \/ on_half_plane hp P \/ on_half_plane hq P"
     using K (MATCH_MP_TAC half_plane_cover) at [10]
  ;have "~on_line P' a /\ ~on_line Q' a /\ ~on_line R' a" at [11] proof
    [have "~(P = handP) /\ ~(Q = handQ) /\ ~(R = handR)" at [11] proof
        [have "on_polyseg Ps handP
               /\ on_polyseg Ps handQ /\ on_polyseg Ps handR"
            from [1;7] by [MEM;ADJACENT_CLAUSES;on_polyseg]
            using (MESON_TAC o mutual_rewrite)
        ;qed from [3]]
    ;have "!Y. between P1 Y P2 ==> on_polyseg Ps Y"
      from [1] by [MEM;ADJACENT_CLAUSES;on_polyseg]
    ;qed by [hand_triangle] from [4;5;6;7;8;11] by [BET_SYM]]
  ;have "on_plane P' 'a /\ on_plane Q' 'a /\ on_plane R' 'a"
     from [4;5;6] by [seg_connected;HD;MEM;MEM_LAST] at [12]
  ;assume "~(P' = Q') /\ ~(P' = R') /\ ~(Q' = R')" from [4;5;6]
     by [seg_connected_sym;seg_connected_trans]
  ;so consider ["X:point";"Y:point";"hx:half_plane"]
     st "X IN {P',Q',R'} /\ Y IN {P',Q',R'} /\ hx IN {hp,hq}
         /\ ~(X = Y)
         /\ on_half_plane hx X /\ on_half_plane hx Y"
     from [10;11;12] by [IN_INSERT;NOT_IN_EMPTY]
     using (MESON_TAC o mutual_rewrite) at [13]
  ;so consider ["hand:point"]
     st "hand IN {handP,handQ,handR}
         /\ ~(?Z. between X Z hand /\ on_polyseg Ps Z)"
     from [4;5;6] by [IN_INSERT;NOT_IN_EMPTY;BET_SYM]
     using (MESON_TAC o mutual_rewrite) at [14]
  ;consider ["hand':point"]
     st "hand' IN {handP,handQ,handR} 
         /\ ~(?Z. between Y Z hand' /\ on_polyseg Ps Z)"
     from [4;5;6;13] by [IN_INSERT;NOT_IN_EMPTY;BET_SYM]
     using (MESON_TAC o mutual_rewrite) at [15]
  ;have "on_plane X 'a /\ on_plane Y 'a"
     from [12;13] by [IN_INSERT;NOT_IN_EMPTY]
     using (MESON_TAC o mutual_rewrite) at [16]
  ;have "between P1 hand P2 /\ between P1 hand' P2"
     from [7;14;15] by [IN_INSERT;NOT_IN_EMPTY]
     using (MESON_TAC o mutual_rewrite) at [17]
  ;have "~on_polyseg Ps X /\ ~on_polyseg Ps Y"
     from [4;5;6;13] by [IN_INSERT;NOT_IN_EMPTY]
     using (MESON_TAC o mutual_rewrite) at [18]
  ;have "on_line P1 (line_of_half_plane hx)
         /\ on_line P2 (line_of_half_plane hx)"
     from [8;10;13] by [IN_INSERT;NOT_IN_EMPTY]
     using (MESON_TAC o mutual_rewrite) at [19]
  ;have "~(?Z. between P1 Z P2 /\ on_polyseg (CONS P2 Ps') Z)"
     from [0;1] by [simple_polygon;ADJACENT_CLAUSES;MEM;PAIR_EQ
                   ;on_polyseg;PAIRWISE;GSYM ALL_MEM;FORALL_PAIR_THM] 
     using ((REWRITE_TAC THEN' MESON_TAC) o mutual_rewrite)
  ;hence "seg_connected 'a (on_polyseg (CONS P1 (CONS P2 Ps'))) X Y"
     from [1;9;13;14;15;16;17;18;19]
     using K (MATCH_MP_TAC same_side_wall_connected)
  ;tactics
    [REMOVE_THEN "13" MP_TAC
        THEN REWRITE_TAC [IN_INSERT;NOT_IN_EMPTY] THEN STRIP_TAC
        THEN ASM_MESON_TAC [seg_connected_sym;seg_connected_trans]]];;

(* If all vertices of a polygon lie in a half-plane, then the polygon lies in that half-plane *)
let vertices_on_half_plane = theorem 
  "!Ps. (!P. MEM P Ps ==> on_half_plane hp P) ==> !P. on_polyseg Ps P ==> on_half_plane hp P"
  [fix ["Ps:point list"]
  ;unfolding by [on_polyseg]
  ;assume "!P. MEM P Ps ==> on_half_plane hp P" at [0]
  ;fix ["P:point"]
  ;so assume "?x y. MEM (x,y) (ADJACENT Ps) /\ between x P y"
  ;so consider ["Q:point";"R:point"] st "MEM (Q,R) (ADJACENT Ps) /\ between Q P R" at [1;2]
  ;hence "on_half_plane hp Q /\ on_half_plane hp R" from [0;1] by [ADJACENT_MEM2]
  ;qed from [2] by [bet_on_half_plane2]];;

let line_of_half_plane_on_plane = theorem
  "!'a hp. (!P. on_half_plane hp P ==> on_plane P 'a)
   ==> !P. on_line P (line_of_half_plane hp) ==> on_plane P 'a"
  [fix ["'a:plane";"hp:half_plane"]
  ;consider ["P:point"] st "on_half_plane hp P" at [0] by [half_plane_not_empty]
  ;consider ["Q:point";"R:point"] st
     "~(Q=R) /\ on_line Q (line_of_half_plane hp) /\ on_line R (line_of_half_plane hp)"
     at [1] by [g13a]
  ;so consider ["X:point";"Y:point"] st "between Q P X /\ between R P Y"
     by [g22;half_plane_not_on_line] from [0] at [2]
  ;hence "on_half_plane hp X /\ on_half_plane hp Y" by [bet_on_half_plane] from [0;1]
  ;so assume "on_plane P 'a /\ on_plane X 'a /\ on_plane Y 'a" from [0]
  ;hence "on_plane Q 'a /\ on_plane R 'a" by [g16;g21] from [2]
  ;qed from [1] by [g16]];;

let bet_not_on_half_plane = theorem
  "!hp P Q R. 
   (!P. on_half_plane hp P ==> on_plane P 'a) 
   /\ on_half_plane hp P /\ on_plane Q 'a /\ ~on_half_plane hp Q /\ between P Q R
   ==> ~(on_half_plane hp R) /\ ~on_line R (line_of_half_plane hp)"
  [fix ["hp:half_plane";"P:point";"Q:point";"R:point"]
  ;assume "(!P. on_half_plane hp P ==> on_plane P 'a)" at [0]
  ;assume "on_half_plane hp P" at [1]
  ;assume "on_plane Q 'a /\ ~on_half_plane hp Q" at [2]
  ;assume "between P Q R" at [3]
  ;per cases 
    [[suppose "on_line Q (line_of_half_plane hp)" at [4]
     ;hence "~(on_half_plane hp R)"
       from [0;1;2;3] by [on_half_plane_not_bet] at [5]
     ;otherwise assume "on_line R (line_of_half_plane hp)"
     ;hence "on_line P (line_of_half_plane hp)" 
       from [3;4] by [g12;g21]
     ;qed from [1] by [half_plane_not_on_line]]
    ;[suppose "~on_line Q (line_of_half_plane hp)" at [4]
     ;so consider ["S:point"] 
       st "on_line S (line_of_half_plane hp)
           /\ between P S Q"
       from [0;1;2] by [on_half_plane_not_bet] at [5]
     ;hence "between P S R" at [6] from [3]
       using ORDER_TAC `{P:point,Q,R,S}`
     ;hence "~on_half_plane hp R"
       from [0;1;5] by [on_half_plane_not_bet]
     ;otherwise assume "on_line R (line_of_half_plane hp)"
     ;hence "on_line P (line_of_half_plane hp)" 
       from [5;6] by [g12;g21]
     ;qed from [1] by [half_plane_not_on_line]]]];;

g `!'a Ps. (!P. MEM P Ps ==> on_plane P 'a)
           ==> ?hp. !P. (on_half_plane hp P ==> on_plane P 'a)
	                /\ (MEM P Ps ==> on_half_plane hp P)`;;
f (fix ["'a:plane"]);;
e (LIST_INDUCT_TAC2 THEN TRY (POP_ASSUM (LABEL_TAC "0")));;
  f (unfolding by [MEM]);;
  f (consider ["A:point";"B:point";"C:point"] st
       "on_plane A 'a /\ on_plane B 'a /\ on_plane C 'a
        /\ ~(?a. on_line A a /\ on_line B a /\ on_line C a)"
       by [plane_three] at [0]);;
  f (so consider ["hp:half_plane"] 
       st "on_line A (line_of_half_plane hp)
           /\ on_line B (line_of_half_plane hp)
           /\ on_half_plane hp C"
       by [unique_half_plane]);;
  f (qed from [0] by [half_plane_on_plane;g11_weak;g16]);;

  f (assume "on_plane x 'a" at [0] by [MEM]);;
  f (so consider ["y:point"]
       st "~(x = y) /\ on_plane y 'a" at [1] by [plane_three;g11_weak]);;
  f (so consider ["z:point"]
       st "on_plane z 'a /\ ~(?a. on_line x a /\ on_line y a /\ on_line z a)"
       from [0] by [plane_triangle] at [2]);;
  f (so consider ["hp:half_plane"] 
       st "on_line y (line_of_half_plane hp)
           /\ on_line z (line_of_half_plane hp)
           /\ on_half_plane hp x"
       by [unique_half_plane] at [3]);;
  f (hence "!P. on_line P (line_of_half_plane hp) ==> on_plane P 'a" from [1;2] by [g11_weak;g16]);;
  f (unfolding by [MEM]);;
  f (qed from [0;1;2;3] by [half_plane_on_plane]);;

  (* HERE *)

  f (assume "on_plane x 'a /\ on_plane y 'a
             /\ !P. MEM P ys ==> on_plane P 'a" at [1] by [MEM]);;
  f (so consider ["hp:half_plane"]
       st "(!P. (on_half_plane hp P ==> on_plane P 'a))
           /\ on_half_plane hp y
           /\ (!P. MEM P ys ==> on_half_plane hp P)" 
       from [0] by [MEM] at [2;3;4]);;
  f (assume "~on_half_plane hp x" at [5]
       from [2;3;4] using (K (REWRITE_TAC [MEM]) THEN' MESON_TAC));;
  f (so consider ["X:point"] st "between y x X" by [g22] from [3;5] at [6]);;
  f (hence "on_plane X 'a" from [1] by [g16;g21] at [7]);;
  f (case "ys = []");;
    f (tactics [FULL_REWRITE_TAC [MEM]]);;
    f (consider ["Z:point"] st 
	 "~(?a. on_line X a /\ on_line x a /\ on_line Z a) /\ on_plane Z 'a"
	 from [1;6;7] by [BET_NEQS;plane_triangle] at [8]);;
    f (obviously by_ncols 
	 (so consider ["hq:half_plane"] 
	    st "on_line X (line_of_half_plane hq) /\ on_line Z (line_of_half_plane hq) 
             /\ on_half_plane hq x") from [6] by [unique_half_plane] at [9]);;
    f (have "!P. on_line P (line_of_half_plane hq) ==> on_plane P 'a"
	 by [g11_weak;g16] from [7;8;9]);;
    f (hence "!P. on_half_plane hq P ==> on_plane P 'a"
	 from [1;9] by [half_plane_on_plane] at [10]);;
    f (have "on_half_plane hq y"
	 from [6;9] by [BET_SYM;bet_on_half_plane]);;
    f (qed from [9;10]);;
  f (case "~(ys = [])");;
    f (so consider ["y':point";"ys':point list"]
	 st "ys = CONS y' ys'" by [list_CASES] at [8]);;
    f (have "~on_half_plane hp X /\ ~on_line X (line_of_half_plane hp)"
	 by [bet_not_on_half_plane;g21] at [9] from [1;2;3;5;6]);;
    f (set "f Y = @Z. on_line Z (line_of_half_plane hp)
                      /\ between Y Z X");;
    f (have "!Y. MEM Y (CONS y ys) ==> on_line (f Y) (line_of_half_plane hp)
                                       /\ between Y (f Y) X");;
      f (fix ["Y:point"]);;
      f (assume "MEM Y (CONS y ys)");;
      f (hence "on_half_plane hp Y" by [MEM] from [3;4]);;
      f (qed by [on_half_plane_not_bet] from [2;7;9]);;
  f (consider ["g:num->point"] st
       "ORDERING g (IMAGE f (set_of_list (CONS y ys)))" proof
       [tactics [MATCH_MP_TAC theorem6
		    THEN SIMP_TAC [FINITE_IMAGE;FINITE_SET_OF_LIST]
		    THEN REWRITE_TAC [IMAGE;IN_SET_OF_LIST;IN_ELIM_THM;COLLINEAR]]
       ;qed]);;
  f (
  f (hence "~on_half_plane hp X" at [7]);;
    f (otherwise assume "on_half_plane hp X");;
    f (qed from [3;5;6] by [bet_on_half_plane2]);;
  f (have "~on_line X (line_of_half_plane hp)" at [8]);;
    f (otherwise assume "on_line X (line_of_half_plane hp)" at [8]);;
    f (case "on_line x (line_of_half_plane hp)");;
      f (hence "on_line y (line_of_half_plane hp)" from [6;8] by [g12;g21]);;
      f (qed by [half_plane_not_on_line] from [3]);; 
    f (assume "~(y = y')"

    f (case "~on_line x (line_of_half_plane hp)" at [9]);;
      f (so consider ["R:point"] 
	   st "on_line R (line_of_half_plane hp) /\ between y R x"
	   by [on_half_plane_not_bet] from [1;2;3;5]);;


 from [4] by [g12;g21]);;
  f (have "on_plane X 'a");;
    f (consider ["a:line"] st "on_line y a /\ on_line x a /\ on_line X a"
	 from [4] by [g21]);;
    f (qed from [1;4] by [MEM;BET_NEQS;g16]);;
