module Pasch(Di : DISCOVERY) =
struct
  let swapbet = prove (`!A B C. between A B C <=> between C B A`, MESON_TAC [g21]);;

  (* We first prove a version of Pasch in terms of the existence of three planar
     triangles -- thanks to Laura Meikle for spotting that we only need three! *)
  let pasch = theorem
    ("!A B C D E. " ^
        "~(?a. on_line A a /\ on_line B a /\ on_line C a)" ^
        "/\ ~(?a. on_line A a /\ on_line D a /\ on_line E a)" ^
        "/\ ~(?a. on_line C a /\ on_line D a /\ on_line E a)" ^
        "/\ (?'a. on_plane A 'a /\ on_plane B 'a /\ on_plane C 'a " ^
        "         /\ on_plane D 'a /\ on_plane E 'a)" ^
        "==> between A D B" ^
        "==> ?Fa. (?a. on_line D a /\ on_line E a /\ on_line Fa a)" ^
                "              /\ (between A Fa C \/ between B Fa C)")
    [fix ["A:point";"B:point";"C:point";"D:point";"E:point"]
    ;assume "between A D B" at [0]
    ;assume "~(?a. on_line A a /\ on_line B a /\ on_line C a)" at [1]
    ;assume "~(?a. on_line A a /\ on_line D a /\ on_line E a)" at [2]
    ;clearly by_neqs (have "~(D = E)" from [2] at [3])
    ;so consider ["DE:line"] st
      "on_line D DE /\ on_line E DE" at [4] from [0] by [g11;g12]
    ;hence "~on_line A DE" at [5] from [2]
    ;hence "~on_line B DE" at [6] from [0;4] by [g12;g21]
    ;assume "~(?a. on_line C a /\ on_line D a /\ on_line E a)"
    ;hence "~on_line C DE" at [7] from [4]
    ;hence "?a. on_line A a /\ on_line B a /\ on_line D a" from [0] by [g21]
    ;assume ("?'a. on_plane A 'a /\ on_plane B 'a /\ on_plane C 'a " ^
                "   /\ on_plane D 'a /\ on_plane E 'a")
    ;so consider ["'a:plane"] st
        ("on_plane A 'a /\ on_plane B 'a /\ on_plane C 'a " ^
            "/\ on_plane D 'a /\ on_plane E 'a") at [8]
    ;hence "!P. on_line P DE ==> on_plane P 'a" at [9] by [g16] from [3;4]
    ;have "?P. on_line P DE /\ between A P B" from [0;4]
    ;hence "?Fa. on_line Fa DE /\ (between A Fa C \/ between B Fa C)"
      from [1;5;6;7;8;9] using
      (fun thms -> MESON_TAC
        [REWRITE_RULE thms
            (SPECL [`A:point`;`B:point`;`C:point`;`DE:line`;`'a:plane`] g24)])
    ;qed from [3;4] by [g12]];;

    let pasch' = prove
    (`!A B D C E.
        between A D B 
     ==> ~(?a. on_line A a /\ on_line B a /\ on_line C a) 
     ==> ~(?a. on_line A a /\ on_line D a /\ on_line E a)
     ==> ~(?a. on_line C a /\ on_line D a /\ on_line E a)
     ==> (?'a. on_plane A 'a /\
               on_plane B 'a /\
               on_plane C 'a /\
               on_plane D 'a /\
               on_plane E 'a)
     ==> (?Fa. (?a. on_line D a /\ on_line E a /\ on_line Fa a) /\
               (between A Fa C \/ between B Fa C))`,
     REPEAT GEN_TAC THEN MP_TAC
       (SPECL [`A:point`;`B:point`;`C:point`
              ;`D:point`;`E:point`] pasch)
          THEN MESON_TAC [])

  let is_bet thm = fst (strip_comb (concl thm)) = `between`
    
  let dest_bet thm =
    let [a;b;c] = Bl.sort (snd (strip_comb (concl thm))) in
    a,b,c

  let new_point xs (a,b,c) =
    match Bl.find_all (not o C mem xs) [a;b;c] with
        [x] -> x

  let BET_SYM = prove
    (`between A B C <=> between C B A`,
     MESON_TAC [g21])
     
  let paschs bets base =
    let p (_,thm) (_,thm') =
      aconv (concl thm) (concl thm') in
    let conv = LAND_CONV (REWRITE_CONV [CONJ_ACI]) in
    Di.unique (fun thm thm' ->
      aconv (concl thm) (concl thm'))
      (unique p
         (bets >>= (fun bet -> 
           let a,b,d = dest_bet bet in
           base.Id.ncols >>= (fun ncol ->
             try
               let c = new_point [a;b;d] (Incidence.dest_ncol ncol) in
               let pasch' = SPECL [c] (MATCH_MP pasch' bet) in
               let pasch' =
                 MATCH_MP (CONV_RULE
                             (BINDER_CONV conv) pasch') ncol in
               base.Id.ncols >>= (fun ncol ->
                 try
                   let e =
                     new_point [a;b;c;d] (Incidence.dest_ncol ncol) in
                   lift1 (fun thm -> Bl.sort [a;b;c;d;e], thm)
                     (rewrite [CONJ_ACI;BET_SYM]
                        (rule1 (CONV_RULE conv (SPECL [e] pasch'))
                           base.Id.ncols))
                 with _ -> zero ())
             with _ -> zero ())))
           >>= (fun (pts,pasch') ->
             rule1 pasch' base.Id.ncols >>= (fun pasch' ->
               base.Id.planes >>= (fun plane ->
                 try
                   return (MATCH_MP pasch'
                             (Incidence.col_subset pts plane))
                 with _ -> zero ()))))

  let by_pasch b =
    let base = Id.inferred b in
    let bets = Id.filter is_bet (Id.split b) in
    paschs bets base
      
  let col_ncol_bot =
    let f col ncol =
      let a,b,c = Incidence.dest_ncol ncol in
      MP (NOT_ELIM ncol) (Incidence.col_subset [a;b;c] col) in
    lift2t f

  let contr =
    let f thm thm' = MP (NOT_ELIM thm) thm' in
    lift2t f
      
  let bots bets base =
    let bet_nbet = prove
      (`between A B C ==> ~between B A C /\ ~between A C B`,
       MESON_TAC [g21;g23]) in
    let all =
      plus
        base.Id.all
        (lift2 (fun eq thm -> PURE_ONCE_REWRITE_RULE [eq] thm)
           base.Id.eqs base.Id.all) in
    let bets =
      plus
        bets
        (lift2 (fun eq thm -> PURE_ONCE_REWRITE_RULE [eq] thm)
           base.Id.eqs bets) in
    plus
      (contr all (plus all (conjuncts (rule1 bet_nbet bets))))
      (col_ncol_bot base.Id.cols base.Id.ncols)

  let run_pasch bets base =
    function [] -> zero ()
      | v::vs ->
        paschs bets base >>=
          (fun p ->
            let x,ex = dest_exists (concl p) in
            let p' = ASSUME (vsubst [v,x] ex) in
            let bots =
              bots bets
                (Id.inferred
                   (plus
                      (Id.maxima (to_one base.Id.all))
                      (Id.split p')))

            in
            return (REWRITE_RULE [Ll.hd bots] p'))
      
end
