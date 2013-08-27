(* ========================================================================= *)
(* ML inference rules for incidence.                                         *)
(*                                                                           *)
(*                                   Phil Scott                              *)
(*                                                                           *)
(*               Centre for Intelligent Systems and their Applications       *)
(*                             University of Edinburgh                       *)
(* ========================================================================= *)

(* My existential reasoning is pretty murky. Lots of messing around having
   to ensure that variables do not appear free in the wrong places when we
   use CHOOSE. This is an excellent argument to move over to the set
   representation ASAP. *)

(* Note that all theorems should be initially given so that points appear in
   increasing term order. *)

module Incidence =
struct
  open OUnit
  open OUnitDiff
  open Set
  
  module Ptseq =
    ListSimpleMake(struct
                     type t = term
                     let compare = compare
                     let pp_printer f pt =
                       Format.fprintf f "@[%s@]" (string_of_term pt)
                     let pp_print_sep f () = Format.fprintf f ";"
                   end)

  module Thmseq =
    ListSimpleMake(struct
                     type t = thm
                     let compare thm1 thm2 =
                       compare (concl thm1) (concl thm2)
                     let pp_printer f thm =
                       Format.fprintf f "@[%s@]"
                         (string_of_term (concl thm))
                     let pp_print_sep f () = Format.fprintf f ";"
                   end)
  open Set
  
  (* Destructors *)
  let dest_neq_tm tm = dest_eq (dest_neg tm)

  let dest_col_tm tm =
    let _,conj  = dest_exists tm in
    let conjs = striplist dest_conj conj in
      map (rand o rator) conjs

  let dest_ncol_tm tm =
    match dest_col_tm (dest_neg tm) with
        [p;q;r] -> p,q,r
      | _       -> failwith "Non-collinear theorem should have 3 conjuncts."

  let dest_plane_tm tm =
    let _,conj  = dest_exists tm in
    let conjs = striplist dest_conj conj in
      map (rand o rator) conjs

  let dest_neq, dest_col, dest_ncol, dest_plane
    = dest_neq_tm o concl, dest_col_tm o concl
    , dest_ncol_tm o concl, dest_plane_tm o concl
          
  (* Filters *)
  let is_neq thm =
    let p thm =
      let x,y = dest_neq thm in
        type_of x = `:point` in
      and_can p thm          

  let is_col = and_can
    (fun thm ->
      let tm = concl thm in
      let on_line tm =
        let _ = dest_binop `on_line` tm in true in
      let x,ex = dest_exists tm in
      all_can on_line (conjuncts ex))
        
  let is_ncol = and_can (is_col o ASSUME o dest_neg o concl)

  let is_plane = and_can
    (fun thm ->
      let tm = concl thm in
      let on_line tm =
        let _ = dest_binop `on_plane` tm in true in
      let x,ex = dest_exists tm in
      all_can on_line (conjuncts ex))

  let sort_on_concl =
    Bl.sort (fun thm thm' -> compare (concl thm) (concl thm'))

  let union_on_concl =
    Set.union ~cmp:(fun thm thm' -> compare (concl thm) (concl thm'))
      
  (* Given a theorem of nested conjunctions, return a list of conjuncts
     satisfying a predicate. *)
  let rec find_conjs p cjs =
    let cjs_term = concl cjs in
      if is_conj cjs_term then
        find_conjs p (CONJUNCT1 cjs) @ find_conjs p (CONJUNCT2 cjs)
      else if p cjs_term then [cjs] else []

  let mk_conjs = end_itlist CONJ

  let hyp_frees thm = Bl.flatten (Bl.map frees (hyp thm))
    
  (* Renames the existentially bound variable to avoid the supplied list
     and all frees in the hypotheses. *)
  let freshen_exists avoid thm =
    let x,ex = dest_exists (concl thm) in
    let x'   = variant (avoid @ hyp_frees thm) x in
    let ex   = vsubst [x',x] ex in
      CHOOSE (x',thm) (SIMPLE_EXISTS x' (ASSUME ex))

  (* Lemmas which justify the rules. *)

  let line =
    prove (`!A B. ?a. on_line A a /\ on_line B a`,
           REPEAT GEN_TAC THEN ASM_CASES_TAC `A:point = B`
        THEN ASM_MESON_TAC [g11;g13a])

  let ncolneq =
    prove (`!A B C. ~(?a. on_line A a /\ on_line B a /\ on_line C a)
             ==> ~(A = B) /\ ~(A = C) /\ ~(B = C)`,
           MESON_TAC [line])           

  let colplane =
    theorem "!a. ?'a. !P. on_line P a ==> on_plane P 'a"
      [fix ["a:line"];
       consider ["A:point";"B:point"] at [0] st
         "~(A = B) /\ on_line A a /\ on_line B a" by [g13a];
       so consider ["C:point"] st
         "~on_line C a" by [g13b];
       hence "!b. ~(on_line A b /\ on_line B b /\ on_line C b)"
         from [0] by [g12];
       so consider ["'a:plane"] st
         "on_plane A 'a /\ on_plane B 'a" by [g14a];
       qed from [0] by [g16]
      ]

  let plane3 =
    prove (`!A B C. ?a. on_plane A a /\ on_plane B a /\ on_plane C a`,
          MESON_TAC [colplane;g14a])

  let colcolplane =
    theorem ("!a b. (?P. on_line P a /\ on_line P b) ==> " ^
      "?'a. (!P. on_line P a ==> on_plane P 'a)" ^
             "/\ (!P. on_line P b ==> on_plane P 'a)")
      [fix ["a:line";"b:line"];
       assume "~(a:line = b)" at [0] by [colplane];
       assume "?P. on_line P a /\ on_line P b";
       so consider ["P:point"] at [1] st "on_line P a /\ on_line P b";
       so consider ["Q:point";"R:point"] at [2] st
         "on_line Q a /\ on_line R b /\ ~(P = Q) /\ ~(P = R)"
         by [g13a] from [0];
       hence "~on_line Q b /\ ~on_line R a" from [0;1] by [g12];
       hence "!c. ~(on_line P c /\ on_line Q c /\ on_line R c)"
         by [g12] from [0;1;2];
       so consider ["'a:plane"] st
         "on_plane P 'a /\ on_plane Q 'a /\ on_plane R 'a" by [g14a];
       qed from [1;2] by [g16]
      ]

  let g15' =
    prove (`!A B C 'a 'b.
             ~(?a. on_line A a /\ on_line B a /\ on_line C a)
           ==> on_plane A 'a /\
             on_plane B 'a /\
             on_plane C 'a /\
             on_plane A 'b /\
             on_plane B 'b /\
             on_plane C 'b 
             ==> 'a = 'b`,
           MESON_TAC [g15])

  (* Combine collinearity theorems with respect to an inequation. *)
  let colcol col col' neq =
    let x,y = dest_neq neq in
    let incident_point tm =
      let p = rand (rator tm) in
        p = x or p = y in
    let avoid =
      frees (concl neq) @ hyp_frees neq in
    let col   = freshen_exists avoid col in
    let l,lex = dest_exists (concl col) in
    let col'  = freshen_exists (l::hyp_frees col @ avoid) col' in
    let m,mex = dest_exists (concl col') in
    let incidents =
      sort_on_concl (find_conjs incident_point (ASSUME mex))
      @ sort_on_concl (find_conjs incident_point (ASSUME lex)) in
    let eq =
      try
        MATCH_MP
          (MATCH_MP g12 neq)
          (mk_conjs incidents)
      with _ -> failwith "colcol" in
    let line_union =
      SIMPLE_EXISTS l
        (mk_conjs
           (union_on_concl (CONJUNCTS (ASSUME lex))
              (CONJUNCTS (SUBS [eq] (ASSUME mex))))) in
      CHOOSE (m,col')
        (CHOOSE (l,col) line_union)

  let col_subset pts col =
    let incident_point tm =
      let p = rand (rator tm) in
        mem p pts in
    let l, col_cjs = dest_exists (concl col) in
    let subset = 
      SIMPLE_EXISTS l
        (mk_conjs (sort_on_concl
                     (find_conjs incident_point (ASSUME col_cjs)))) in
      CHOOSE (l, col) subset
        
  let contr thm nthm =
    MATCH_MP (NOT_ELIM nthm) thm

  (* Infer a new triangle *) 
  let colncolncol col_thm ncol_thm =
    let colset = dest_col col_thm in
    let x,y,z  = dest_ncol ncol_thm in
    let prov (p,q,r) col_thm ncol_thm neq_thm =
      let mki p = mk_binop `on_line` p `l:line` in
      let refute = mk_exists
        (`l:line`,mk_conj (mki p, mk_conj (mki q, mki r))) in
      let col =
        col_subset [x;y;z]
          (colcol col_thm (ASSUME refute) neq_thm) in
        NOT_INTRO (DISCH refute (contr col ncol_thm)) in
      match partition (C mem colset) [x;y;z] with
          [p;q],[r] ->
            (fun neq_thm ->
               let x,y = dest_neq neq_thm in
                 if is_subset [x;y] colset then
                   let [r';x';y'] = insert r [x;y] in
                     prov (r',x',y') col_thm ncol_thm neq_thm
                 else failwith "colncolncol")
        | _ -> failwith "colncolncol"

  (* Infer inequality from collinear set and non-collinear set *)
  let colncolneq col_thm ncol_thm =
    let colset = dest_col col_thm in
    let x,y,z = dest_ncol ncol_thm in
    let sort_conjs exthm =
      let x,ex   = dest_exists (concl exthm) in
      let sorted = mk_conjs (sort_on_concl (CONJUNCTS (ASSUME ex))) in
        CHOOSE (x,exthm) (SIMPLE_EXISTS x sorted) in
    let prov (x,y) z w col ncol =
      let refute = mk_eq (w,z) in
      let neq =
        NOT_INTRO
          (DISCH refute
             (contr
                (sort_conjs (SUBS [ASSUME refute]
                               (col_subset (insert w [x;y]) col)))
                ncol)) in
        PURE_REWRITE_RULE [EQ_SYM_EQ] neq in
    match partition (C mem colset) [x;y;z] with
        [x;y], [z] ->
          let f w =
            if z < w then
              prov (x,y) z w col_thm ncol_thm
            else prov (x,y) z w col_thm ncol_thm in
            map f (filter (not o C mem [x;y]) colset)
      | _ -> []

  (* Infer point-equality from intersecting lines.*)
  let coleq col_thm col_thm' =
    let colset  = dest_col col_thm in
    let colset' = dest_col col_thm' in
    let prov x y ncolset col col' ncol =
      let eq = mk_eq (x,y) in
      let col =
        col_subset ncolset
          (colcol col col' (ASSUME (mk_neg eq))) in
        CCONTR eq (contr col ncol) in
    let union = union colset colset' in
    let intersection = intersect colset colset' in
      if length union <= length colset or length intersection < 2 or
        length union < 3 then failwith "coleq"
      else
       fun ncol_thm ->
         let ncolset = let x,y,z = dest_ncol ncol_thm in [x;y;z] in
           if subset ncolset union then
             map_sym (fun x y -> prov x y ncolset
                        col_thm col_thm' ncol_thm)
               (Bl.unique (Bl.sort compare intersection))
           else []

  (* Infer plane from noncollinear theorem *)
  let ncolplane ncol =
    let x,y,z = dest_ncol ncol in
      SPECL [x;y;z] plane3
             
  (* Infer plane from collinear theorem *)
  let colplane col =
    let l,lex       = dest_exists (concl col) in
    let colplane    = SPEC l colplane in
    let p,colplane' = dest_exists (concl colplane) in
    let cjs =
      mk_conjs (map (MATCH_MP (ASSUME colplane'))
                  (CONJUNCTS (ASSUME lex))) in
    CHOOSE (l,col) (CHOOSE (p,colplane) (SIMPLE_EXISTS p cjs))
             
  (* Infer plane from line in a plane *)
  let colplaneplane col plane =
    let colset = dest_col col in
    let planeset = dest_plane plane in
    let prov (x,y) col plane neq =
      let incident_point tm =
        let p = rand (rator tm) in
          p = x or p = y in
      let avoid =
        frees (concl neq) @ hyp_frees neq in
      let col   = freshen_exists avoid col in
      let l,lex = dest_exists (concl col) in
      let plane = freshen_exists (avoid @ hyp_frees col) plane in
      let p,pex = dest_exists (concl plane) in
      let incidents =
        Bl.unique
           (sort_on_concl (find_conjs incident_point (ASSUME pex))
            @ sort_on_concl (find_conjs incident_point (ASSUME lex))) in
      let union = MATCH_MP (MATCH_MP g16 neq) (mk_conjs incidents) in
      let plane' =
        SIMPLE_EXISTS p
          (mk_conjs
             (union_on_concl
                (map (MATCH_MP union) (CONJUNCTS (ASSUME lex)))
                (CONJUNCTS (ASSUME pex)))) in
          CHOOSE (p,plane) (CHOOSE (l,col) plane') in
    let union = union colset planeset in
    let intersection = intersect colset planeset in
    if length intersection < 2 or length union <= length colset then
      raise (Failure "colplaneplane")
    else
      fun neq ->
        let x,y = dest_neq neq in
        if subset [x;y] intersection then
          prov (x,y) col plane neq
        else raise (Failure "colplaneplane")
            
  (* Infer plane from intersecting lines *)
  let colcolplane col col' =
    let colset, colset' = dest_col col, dest_col col' in
    match intersect colset colset' with
        p :: _ -> 
          let col    = freshen_exists [] col in
          let l, lex = dest_exists (concl col) in
          let col'   = freshen_exists (l :: hyp_frees col) col' in
          let m, mex = dest_exists (concl col') in
          let incident_point tm = p = rand (rator tm) in
          let line_plane =
            MATCH_MP colcolplane
              (SIMPLE_EXISTS p
                 (CONJ
                    (hd (find_conjs incident_point (ASSUME lex)))
                    (hd (find_conjs incident_point (ASSUME mex))))) in
          let p,pex = dest_exists (concl line_plane) in
          let plane =
            mk_conjs
              (union_on_concl
                 (map (MATCH_MP (CONJUNCT1 (ASSUME pex)))
                    (CONJUNCTS (ASSUME lex)))
                 (map (MATCH_MP (CONJUNCT2 (ASSUME pex)))
                    (CONJUNCTS (ASSUME mex)))) in
          CHOOSE (m,col')
            (CHOOSE (l,col)
               (CHOOSE (p,line_plane)
                  (SIMPLE_EXISTS p plane)))
      | _ -> raise (Failure "colcolplane")

  (* Infer plane from planes with non-collinear intersection *)
  let planeplane plane plane' =
    let planeset, planeset' = dest_plane plane, dest_plane plane' in
    let prov pts ncol plane plane' =
      let incident_point tm =
        let p = rand (rator tm) in
        mem p pts in
      let avoid   =
        frees (concl ncol) @ hyp_frees ncol in
      let plane   = freshen_exists avoid plane in
      let p,pex   = dest_exists (concl plane) in
      let plane'  = freshen_exists (p::avoid @ hyp_frees plane) plane' in
      let p',pex' = dest_exists (concl plane') in
      let incidents =
        Bl.unique
          (sort_on_concl (find_conjs incident_point (ASSUME pex'))
           @ sort_on_concl (find_conjs incident_point (ASSUME pex))) in
      let eq = MATCH_MP (MATCH_MP g15' ncol) (mk_conjs incidents) in
      let plane_union =
        SIMPLE_EXISTS p
          (mk_conjs
             (union_on_concl
                (CONJUNCTS (ASSUME pex))
                 (CONJUNCTS (SUBS [eq] (ASSUME pex'))))) in
        CHOOSE (p',plane')
          (CHOOSE (p,plane) plane_union) in
    let intersection = intersect planeset planeset' in
    if length intersection < 3 then
      raise (Failure "planeplane")
    else
      fun ncol ->
        let x,y,z = dest_ncol ncol in
        if subset [x;y;z] intersection then
          prov [x;y;z] ncol plane plane'
        else raise (Failure "planeplane")

  let col1 = ASSUME
    `?a. on_line A a /\ on_line D a /\ on_line H a`
  let col2 = ASSUME
    `?z. on_line B z /\ on_line D z /\ on_line G z /\ on_line H z`
  let col3 = ASSUME
    `?line. on_line B line /\ on_line C line /\ on_line D line
    /\ on_line G line`
  let col4 = ASSUME
    `?b. on_line B b /\ on_line C b /\ on_line G b`
    
  let ncol1 = ASSUME
    `~(?d. on_line C d /\ on_line D d /\ on_line G d)`
  let ncol2 = ASSUME
    `~(?d. on_line C d /\ on_line E d /\ on_line G d)`
  let ncol3 = ASSUME
    `~(?line. on_line A line /\ on_line H line /\ on_line Z line)`
  let neq1 = ASSUME `~(D:point=H)`
  let neq2 = ASSUME `~(B:point=G)`
  let neq3 = ASSUME `~(B:point=H)`
  let neq4 = ASSUME `~(A:point=H)`
  let neq5 = ASSUME `~(A:point=B)`

  let plane1 = ASSUME
    `?plane. on_plane A plane /\ on_plane B plane /\ on_plane C plane 
    /\ on_plane Fa plane /\ on_plane H plane /\ on_plane Z plane`
  let plane2 = ASSUME
    `?a. on_plane A a /\ on_plane E a /\ on_plane H a /\ on_plane Z a`

  let suite =
    let assert_equal_pt xs ys =
      Ptseq.assert_equal (Ptseq.of_list xs) (Ptseq.of_list ys) in
    let assert_equal_thms xs ys =
      Thmseq.assert_equal (Thmseq.of_list xs) (Thmseq.of_list ys) in
    let dest_ncol thm = let x,y,z = dest_ncol thm in [x;y;z] in
    "Suite" >:::
      ["colcol" >:::
         ["test1" >::
             (fun () -> assert_equal_pt
               [`A:point`;`B:point`;`D:point`;`G:point`;`H:point`]
               (dest_col (colcol col1 col2 neq1)))
         ;"test2" >::
           (fun () -> assert_equal_pt
             [`B:point`;`C:point`;`D:point`;`G:point`;`H:point`]
             (dest_col (colcol col2 col3 neq2)))
         ;"test3" >::
           (fun () -> assert_equal_pt
             [`A:point`;`D:point`;`H:point`]
             (dest_col (colcol col1 col1 neq1)))
         ;"test4" >::
           (fun () -> assert_raises (Failure "colcol")
             (fun () -> colcol col1 col2 neq2))
         ;"test5" >::
           (fun () -> assert_raises (Failure "colcol")
             (fun () -> colcol col1 col3 neq1))
         ]
      ;"colncolncol" >:::
         ["test1" >::
             (fun () -> assert_equal_pt
               [`B:point`;`C:point`;`H:point`]
               (dest_ncol (colncolncol col2 ncol1 neq3)))
         ;"test2" >::
           (fun () -> assert_equal_pt
             [`A:point`;`B:point`;`Z:point`]
             (dest_ncol (colncolncol (colcol col1 col2 neq1) ncol3 neq5)))
         ;"test3" >::
           (fun () -> assert_equal_pt
             [`B:point`;`H:point`;`Z:point`]
             (dest_ncol (colncolncol (colcol col1 col2 neq1) ncol3 neq3)))
         ;"test4" >::
           (fun () -> assert_equal_pt
             [`A:point`;`H:point`;`Z:point`]
             (dest_ncol (colncolncol (colcol col1 col2 neq1) ncol3 neq4)))
         ;"test5" >::
           (fun () -> assert_raises (Failure "colncolncol")
             (fun () -> colncolncol col2 ncol1 neq4))
         ;"test6" >::
           (fun () -> assert_raises (Failure "colncolncol")
             (fun () -> colncolncol col1 ncol2 neq1))
         ]
      ;"colncolneq" >:::
        ["test1" >::
            (fun () -> assert_equal_thms
              (CONJUNCTS (ASSUME `~(B:point = C) /\ ~(C = H)`))
              (colncolneq col2 ncol1))
        ;"test2" >::
          (fun () -> assert_equal_thms
            (CONJUNCTS (ASSUME `~(B:point = E) /\ ~(D = E)`))
            (colncolneq col3 ncol2))
        ;"test3" >::
          (fun () -> assert_equal_thms [] (colncolneq col1 ncol1))
        ]
      ;"coleq" >:::
        ["test1" >::
            (fun () -> assert_equal_thms
              (CONJUNCTS (ASSUME `B:point = D /\ B = G /\ D = G`))
          (coleq col2 col3 ncol1))
        ;"test2" >::
          (fun () -> assert_raises (Failure "coleq")
            (fun () -> coleq col1 col3 ncol1))
        ]
      ;"ncolplane" >:::
        ["test1" >::
            (fun () -> assert_equal_pt
              [`C:point`;`D:point`;`G:point`] (dest_plane (ncolplane ncol1)))
        ;"test2" >::
          (fun () -> assert_equal_pt
            [`C:point`;`E:point`;`G:point`] (dest_plane (ncolplane ncol2)))
        ;"test3" >::
          (fun () -> assert_equal_pt
            [`B:point`;`H:point`;`Z:point`]
            (dest_ncol (colncolncol (colcol col1 col2 neq1) ncol3 neq3)))
        ]
      ;"colplane" >:::
        ["test1" >::
            (fun () -> assert_equal_pt
              [`A:point`;`D:point`;`H:point`]
              (dest_plane (colplane col1)))
        ;"test2" >::
            (fun () -> assert_equal_pt
              [`B:point`;`D:point`;`G:point`;`H:point`]
              (dest_plane (colplane col2)))
        ;"test3" >::
            (fun () -> assert_equal_pt
              [`B:point`;`C:point`;`D:point`;`G:point`;`H:point`]
              (dest_plane (colplane (colcol col2 col3 neq2))))
        ]
      ;"colcolplane" >:::
        ["test1" >::
            (fun () -> assert_equal_pt
              [`A:point`;`B:point`;`C:point`;`D:point`;`G:point`;`H:point`]
              (dest_plane (colcolplane col1 col3)))
        ;"test2" >::
          (fun () -> assert_equal_pt
            [`A:point`;`B:point`;`C:point`;`D:point`;`G:point`;`H:point`]
            (dest_plane (colcolplane (colcol col1 col2 neq1)
                           (colcol col2 col3 neq2))))
        ;"test3" >::
          (fun () -> assert_equal_pt
            [`A:point`;`D:point`;`H:point`]
            (dest_plane (colcolplane col1 col1)))
        ;"test4" >:: 
          (fun () -> assert_raises (Failure "colcolplane")
            (fun () -> colcolplane col1 col4))
        ]
      ;"planeplane" >:::
        ["test1" >::
            (fun () -> assert_equal_pt
              [`A:point`;`B:point`;`C:point`;`D:point`;`Fa:point`;`G:point`;`H:point`
              ;`Z:point`]
              (dest_plane (planeplane (colplane (colcol col2 col3 neq2)) plane1
                             (colncolncol col2 ncol1 neq3))))
        ;"test2" >::
          (fun () -> assert_equal_pt
            [`A:point`;`B:point`;`C:point`;`D:point`;`E:point`;`Fa:point`;`G:point`
            ;`H:point`;`Z:point`]
            (dest_plane (planeplane (planeplane (colplane (colcol col2 col3
                                                             neq2)) plane1
                                       (colncolncol col2 ncol1 neq3))
                           plane2 ncol3)))
        ;"test3" >::
          (fun () -> assert_equal_pt
            [`C:point`;`D:point`;`G:point`]
            (dest_plane (planeplane (ncolplane ncol1) (ncolplane ncol1)
                           ncol1)))
        ;"test4" >::
          (fun () -> assert_raises (Failure "planeplane")
            (fun () -> dest_plane (planeplane col2 col3 ncol1)))
        ]
      ]
    
end
