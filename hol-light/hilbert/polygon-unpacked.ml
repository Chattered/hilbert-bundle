(* I'm keeping this in just to show how I worked in practice. This is how I
   worked interactively. Notice how I'm using "case" and "finished". Packaging
   this up into a non-interactive form is a pretty straightforward process of
   inserting brackets and semi-colons. *)

h "!'a A B C was_inside P Q.
   crossings (A,B,C) was_inside P Q = 1
   /\ crossings (A,C,B) was_inside P Q = 0
   /\ crossings (B,C,A) was_inside P Q = 0
   ==> on_plane A 'a /\ on_plane B 'a /\ on_plane C 'a
       /\ on_plane P 'a /\ on_plane Q 'a
       /\ ~(?a. on_line A a /\ on_line B a /\ on_line C a)
       /\ ~on_polyseg [P;Q] A /\ ~on_polyseg [P;Q] B /\ ~on_polyseg [P;Q] C
       /\ ~on_triangle (A,B,C) Q
       ==> (in_triangle (A,B,C) P \/ on_triangle (A,B,C) P /\ was_inside
            <=> ~(in_triangle (A,B,C) Q))";;
f (fix ["'a:plane";"A:point";"B:point";"C:point";"was_inside:bool";"P:point";"Q:point"]);;
f (assume "on_plane A 'a /\ on_plane B 'a /\ on_plane C 'a
           /\ on_plane P 'a /\ on_plane Q 'a" at [0]);;
f (assume "~(?a. on_line A a /\ on_line B a /\ on_line C a)" at [1]);;
f (assume "~on_polyseg [P; Q] A /\ ~on_polyseg [P; Q] B /\ ~on_polyseg [P; Q] C" at [2]);;
f (tactics [REWRITE_TAC [crossings]
               THEN CONV_TAC (TOP_SWEEP_CONV (REWR_CONV COND_RAND))
               THEN CONV_TAC (TOP_SWEEP_CONV (REWR_CONV COND_RATOR))
               THEN REWRITE_TAC [FST;ARITH_RULE `~(1=0)`;tri_syms]]);;
f (case "?R. between P R Q /\ between A R B");;
  f (so consider ["R:point"] st "between P R Q /\ between A R B" at [3]);;
  f (case "in_triangle (A,B,C) P" at [4]);;
    f (hence "out_triangle (A,B,C) Q" from [3]
         by [on_triangle;on_triangle_bet_out_triangle]);;
    f (qed by [out_triangle] from [4] using K (DISCH_THEN (K ALL_TAC)));;
  f (case "out_triangle (A,B,C) P" at [4]);;
    f (case "?a. on_line C a /\ on_line P a /\ on_line R a" at [5]);;
      f (have "~between C P R" at [6] from [1;3;4] by [in_triangle2;out_triangle]);;
      f (obviously (by_neqs o Id.conjuncts)
           (have "~(C = R)" at [7] from [1;3]));;
      f (have "~(C = P) /\ ~(C = Q) /\ ~between P C Q"
           from [2] by [on_polyseg_pair;on_triangle]);;
      f (hence "between R Q C" from [3;5;6;7] using ORDER_TAC `{C:point,P,Q,R}`);;
      f (hence "in_triangle (A,B,C) Q" from [1;3] by [in_triangle2;BET_SYM]);;
      f (qed from [4] by [out_triangle] using K (DISCH_THEN (K ALL_TAC)));;
    f (case "~(?a. on_line C a /\ on_line P a /\ on_line R a)" at [5]);;
      f (have "~(?a. on_line A a /\ on_line P a /\ on_line Q a)" at [6]);;
        f (otherwise assume "?a. on_line A a /\ on_line P a /\ on_line Q a"
             at [6]);;
        f (have "~(A=P) /\ ~(A=Q) /\ ~(B=P) /\ ~(B=Q)
                 /\ ~between P A Q /\ ~between P B Q
                 /\ ~(between A P B)"
             from [2;4] by [on_triangle;on_polyseg_pair;out_triangle]);;
        f (qed from [3;6] using ORDER_TAC `{A:point,B,P,Q,R}`);;
      f (have "~(?a. on_line B a /\ on_line P a /\ on_line Q a)" at [7]);;
        f (otherwise assume "?a. on_line B a /\ on_line P a /\ on_line Q a"
             at [6]);;
        f (have "~(A=P) /\ ~(A=Q) /\ ~(B=P) /\ ~(B=Q)
                 /\ ~between P A Q /\ ~between P B Q
                 /\ ~(between A P B)"
             from [2;4] by [on_triangle;on_polyseg_pair;out_triangle]);;
        f (qed from [3;6] using ORDER_TAC `{A:point,B,P,Q,R}`);;
      f (clearly (by_pasch o Di.conjuncts)
           (so consider ["S:point"] st
              "(?a. on_line S a /\ on_line P a /\ on_line R a)
               /\ (between A S C \/ between B S C)"
              from [0;1;3;5] at [8;9]));;
      f (have "~between A P C /\ ~between B P C"
           from [4] by [out_triangle;on_triangle]);;
      f (so assume "~(?R. between P R Q /\ between A R C)
                 /\ ~(?R. between P R Q /\ between B R C)");;
      f (hence "~between P S Q" at [10] from [9]);;
      f (assume "~on_triangle (A,B,C) Q");;
      f (hence "~(P = S) /\ ~(Q = S)" 
           from [4;9] by [out_triangle;on_triangle] at [11]);;
      f (have "~between R P S");;
        f (otherwise assume "between R P S");;
        f (hence "in_triangle (A,B,C) P" from [1;3;9] by [in_triangle1;BET_SYM;tri_syms]);;
        f (qed by [out_triangle] from [4]);;
      f (hence "between R Q S" from [3;8;9;10;11]
           using ORDER_TAC `{P:point,R,Q,S}`);;
      f (hence "in_triangle (A,B,C) Q" by [in_triangle1;BET_SYM;tri_syms]
           from [1;3;9]);;
      f (qed from [4] by [out_triangle] using K (DISCH_THEN (K ALL_TAC)));;
    f finished;;
  f (case "on_triangle (A,B,C) P" at [4]);;
    f (case "between A P B" at [5]);;
      f (have "~between P A Q /\ ~between P B Q /\ ~(A = Q) /\ ~(B = Q)"
           from [2] by [on_polyseg_pair;on_triangle;BET_SYM]);;
      f (hence "between A Q B" using ORDER_TAC `{A:point,B,P,Q,R}`
           from [3;5]);;
      f (qed by [on_triangle]);;
    f (case "between A P C \/ between B P C" at [5]);;
      f (hence "out_triangle (A,B,C) Q" by [out_triangle1;BET_SYM;tri_syms]
           at [6] from [1;3;5]);;
      f (hence "~between A Q C /\ ~between B Q C" at [7] by [on_triangle;out_triangle]);;
      f (have "?R. between P R Q /\ in_triangle (A,B,C) R");;
        f (consider ["X:point"] st "between P X R" at [8] from [3] by [BET_NEQS;three]);;
        f (hence "between P X Q" using ORDER_TAC `{P:point,Q,R,X}`
             at [9] from [3]);;
        f (hence "in_triangle (A,B,C) X" by [in_triangle1] from [1;3;5;8]
             by [tri_syms;BET_SYM;in_triangle1]);;
        f (qed from [9]);;
      f (so assume "was_inside" from [5;7]);;
      f (qed from [4;6] by [out_triangle] using K (DISCH_THEN (K ALL_TAC)));;
    f (finished by [on_triangle;on_polyseg_pair] from [2;4]);;
  f (finished by [out_triangle]);;
f (case "~(?R. between P R Q /\ between A R B)" at [3]);;
  f (so assume "between A P B" at [4]);;
  f (case "?R. between P R Q /\ in_triangle (A,B,C) R");;
    f (so consider ["R:point"]
         st "between P R Q /\ in_triangle (A,B,C) R" at [5]);;
    f (have "~between A P C /\ ~between B P C" at [6]);;
      f (otherwise assume "between A P C \/ between B P C");;
      f (obviously (by_cols o Di.split) (qed from [1;4]));;
    f (so assume "~(?R. between P R Q /\ between A R C)
                  /\ ~(?R. between P R Q /\ between B R C)" at [7]);;
    f (assume "~between A Q B" at [8]);;
    f (assume "~on_triangle (A,B,C) Q");;
    f (have "in_triangle (A,B,C) Q");;
      f (otherwise assume "out_triangle (A,B,C) Q" from [this] by [out_triangle]);;
      f (so consider ["S:point"] st
           "between R S Q /\ on_triangle (A,B,C) S"
           at [9;10] from [0;5] by [in_triangle_simple_closed;out_triangle]);;
      f (have "between P S Q" at [11] from [5;9] using
           ORDER_TAC `{P:point,Q,R,S}`);;
      f (have "~between A S B");;
        f (otherwise assume "between A S B" at [12] by [on_polyseg_pair]);;
        f (have "~between P A Q /\ ~between P B Q" from [2]
             by [on_polyseg_pair;on_triangle]);;
        f (hence "A = Q \/ B = Q" from [4;8;11;12] using ORDER_TAC `{A:point,B,P,Q}`);;
        f (qed by [on_triangle;on_polyseg_pair] from [2]);;
      f (hence "between A S C \/ between B S C"
           by [on_triangle;on_polyseg_pair;BET_SYM] from [2;10;11]);;
      f (qed from [7;11]);;
    f (unfolding from [this;3;6]);;
    f (qed from [4;5] by [on_triangle;in_triangle_not_on_triangle]);;
  f (case "~(?R. between P R Q /\ in_triangle (A,B,C) R)" at [5]);;
    f (otherwise assume "in_triangle (A,B,C) Q" at [6] from [this;3;4] by [on_triangle]);;
    f (so consider ["R:point"] st "between P R Q"
         from [4;5] by [on_triangle;in_triangle_not_on_triangle;three]);;
    f (qed from [4;5;6] by [on_triangle_bet_in_triangle;on_triangle]);;
  f finished;;
f finished;;

h "!'a A B C was_inside P Q.
   on_plane A 'a /\ on_plane B 'a /\ on_plane C 'a
   /\ on_plane P 'a /\ on_plane Q 'a
   /\ ~(?a. on_line A a /\ on_line B a /\ on_line C a)
   /\ ~on_polyseg [P;Q] A /\ ~on_polyseg [P;Q] B /\ ~on_polyseg [P;Q] C
   /\ crossings (A,B,C) was_inside P Q = 0
   /\ crossings (A,C,B) was_inside P Q = 0
   /\ crossings (B,C,A) was_inside P Q = 0
   /\ ~on_triangle (A,B,C) Q
   ==> (in_triangle (A,B,C) P \/ on_triangle (A,B,C) P /\ was_inside
        <=> in_triangle (A,B,C) Q)";;
f (fix ["'a:plane";"A:point";"B:point";"C:point";"was_inside:bool";"P:point";"Q:point"]);;
f (assume "on_plane A 'a /\ on_plane B 'a /\ on_plane C 'a
           /\ on_plane P 'a /\ on_plane Q 'a" at [0]);;
f (assume "~(?a. on_line A a /\ on_line B a /\ on_line C a)" at [1]);;
f (assume "~on_polyseg [P; Q] A /\ ~on_polyseg [P; Q] B /\ ~on_polyseg [P; Q] C" at [2]);;
f (assume "~on_triangle (A,B,C) Q" at [3]);;
f (case "between A P B");;
  f (qed from [0;1;2;3] by [lemma1]);;
f (case "between A P C");;
  f (tactics [POP_ASSUM (ASSUME_TAC o SPECL [`'a:plane`;`B:point`] o MATCH_MP lemma1)]);;
  f (qed from [0;1;2;3] using (MESON_TAC o mutual_rewrite) by [tri_syms;crossings_sym]);;
f (case "between B P C");;
  f (tactics [POP_ASSUM (ASSUME_TAC o SPECL [`'a:plane`;`A:point`] o MATCH_MP lemma1)]);;
  f (qed from [0;1;2;3] using (MESON_TAC o mutual_rewrite) by [tri_syms;crossings_sym]);;
f (case "~on_triangle (A,B,C) P" at [4]);;
  f (tactics [REWRITE_TAC [crossings]
                 THEN CONV_TAC (TOP_SWEEP_CONV (REWR_CONV COND_RAND))
                 THEN CONV_TAC (TOP_SWEEP_CONV (REWR_CONV COND_RATOR))
                 THEN REWRITE_TAC [FST;ARITH_RULE `~(1=0)`;tri_syms]]);;
  f (have "~between A Q B /\ ~between A Q C /\ ~between B Q C"
       from [3] by [on_triangle]);;
  f (so assume "~(?R. between P R Q
                   /\ (between A R B \/ between A R C \/ between B R C))");;
  f (hence "~(?R. between P R Q /\ on_triangle (A,B,C) R)"
       at [5] from [2] by [on_polyseg_pair;on_triangle]);;
  f (hence "in_triangle (A,B,C) P <=> in_triangle (A,B,C) Q"
       from [0;3;4] by [in_triangle_simple_closed;BET_SYM]);;
  f (qed from [4] using K (DISCH_THEN (K ALL_TAC)));;
f (finished from [2] by [on_polyseg_pair;on_triangle]);;
