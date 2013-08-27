(* Additions to the incidence discoverer, which abstracts concrete incidence
   claims. *)

module Discovery =
struct
  include Discovery
  let rule4 rl ants1 ants2 ants3 ants4 =
    Discovery.mp (Discovery.rule3 rl ants1 ants2 ants3) ants4
end

module Incidence_discovery =
struct
  include Incidence_discovery

  let betcol =
    prove (`!A B C. between A B C
            ==> ?a. on_line A a /\ on_line B a /\ on_line C a`,
           MESON_TAC [g21]);;

  let betneqs =
    prove (`!A B C. between A B C
            ==> ~(A = B) /\ ~(A = C) /\ ~(B = C)`,
           MESON_TAC [g21]);;

  let add_bets b =
    Discovery.merge_all
      [b
      ;rewrite [CONJ_ACI] (rule1 betcol b)
      ;rewrite [EQ_SYM_EQ] (conjuncts (rule1 betneqs b))]

  let intro_ncol = prove
    (`~(A = B) ==> on_line A a ==> on_line B a ==> ~on_line C a
     ==> ~(?a. on_line A a /\ on_line B a /\ on_line C a)`,
     MESON_TAC [g12]);;

  let tc cmp x y =
    try
      cmp x y
    with _ -> false

  let add_ncols b =
    Discovery.maxima (tc Id.compare_set)
      (Discovery.plus (Id.rewrite [CONJ_ACI] (rule4 intro_ncol b b b b)) 
         (Discovery.conjuncts b))

  let intro_col = prove
    (`on_line A a ==> on_line B a ==> on_line C a
     ==> (?a. on_line A a /\ on_line B a /\ on_line C a)`,
     MESON_TAC [])

  let add_cols b =
    Discovery.maxima (tc Id.compare_set)
      (Discovery.plus (Id.rewrite [CONJ_ACI] (Id.rule3 intro_col b b b)) 
         (Discovery.conjuncts b))

  let inferred = inferred o add_bets o add_ncols o add add_cols
end
