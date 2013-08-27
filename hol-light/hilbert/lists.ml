(* ========================================================================= *)
(* Additional list definitions and theorems.                                 *)
(* TODO: The useful bits of this theory file need to be extracted and merged *)
(* with Petros' library.                                                     *)
(*                                                                           *)
(*                                   Phil Scott                              *)
(*                                                                           *)
(*               Centre for Intelligent Systems and their Applications       *)
(*                             University of Edinburgh                       *)
(* ========================================================================= *)

(* I reserve "cases" for Mizar Light. *)
let type_cases ty = if ty = "num" then num_CASES else
  let _,ith,_ = assoc ty (!inductive_type_store) in prove_cases_thm ith;;

let NOT_EMPTY_EXISTS = prove
  (`!xs:a list. ~(xs = []) <=> ?h t. xs = CONS h t`,
   MESON_TAC [list_CASES;NOT_CONS_NIL]);;

let ONE_ONE_INDUCT = prove
  (`!f:a->b g P. (!x. g (f x) = x) /\ (!x. P (g x)) ==> !x. P x`,
    MESON_TAC []);;

let LIST_INDUCT_APPEND = prove
  (`!P. P [] /\ (!x xs:a list. P xs ==> P (APPEND xs [x]))
      ==> !xs. P xs`,
   GEN_TAC THEN DISCH_TAC
     THEN MATCH_MP_TAC (ISPECL [`REVERSE:a list -> a list`]
                          ONE_ONE_INDUCT)
     THEN EXISTS_TAC `REVERSE:a list -> a list`
     THEN REWRITE_TAC [REVERSE_REVERSE] THEN LIST_INDUCT_TAC
     THEN ASM_SIMP_TAC [REVERSE]);;

let LIST_INDUCT_APPEND_TAC =
  MATCH_MP_TAC LIST_INDUCT_APPEND THEN CONJ_TAC
    THENL [ALL_TAC;GEN_TAC THEN GEN_TAC THEN DISCH_TAC];; 

let LIST_INDUCT2 = prove
  (`!P. P [] 
   /\ (!x:a. P [x]
       /\ (!y ys. P (CONS y ys) ==> P (CONS x (CONS y ys))))
   ==> !xs. P xs`,
   GEN_TAC THEN DISCH_TAC THEN LIST_INDUCT_TAC
     THEN ASM_REWRITE_TAC [] THEN POP_ASSUM MP_TAC
     THEN SPEC_TAC (`t:a list`,`t:a list`) THEN LIST_INDUCT_TAC
     THEN ASM_REWRITE_TAC []);;
  
let LIST_INDUCT_TAC2 =
  MATCH_MP_TAC LIST_INDUCT2 THEN CONJ_TAC
    THENL [ALL_TAC;GEN_TAC THEN CONJ_TAC
      THENL [ALL_TAC;GEN_TAC THEN GEN_TAC THEN DISCH_TAC]];;

let LIST_INDUCT_TAC3 =
  let LIST_INDUCT3 = prove
    (`!P. P []
          /\ (!x:a. P [x]
              /\ (!y:a. P [x;y]
                  /\ (!z xs. P (CONS y (CONS z xs)) ==> P (CONS x (CONS y (CONS z xs))))))
          ==> !xs. P xs`,
     GEN_TAC THEN DISCH_TAC THEN LIST_INDUCT_TAC
       THEN ASM_REWRITE_TAC [] THEN POP_ASSUM MP_TAC
       THEN SPEC_TAC (`t:a list`,`t:a list`) THEN LIST_INDUCT_TAC2
       THEN ASM_REWRITE_TAC []) in
  MATCH_MP_TAC LIST_INDUCT3 THEN CONJ_TAC
    THENL [ALL_TAC;GEN_TAC THEN CONJ_TAC
      THENL [ALL_TAC;GEN_TAC THEN CONJ_TAC
        THENL [ALL_TAC;GEN_TAC THEN GEN_TAC THEN DISCH_TAC]]];;

let APPEND_EQ = prove
  (`!xs:a list ys us vs. LENGTH xs = LENGTH us
      ==> ((APPEND xs ys = APPEND us vs) <=> xs = us /\ ys = vs)`,
   LIST_INDUCT_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC
     THEN (REWRITE_TAC [APPEND]
             THEN REWRITE_TAC [LENGTH;NOT_SUC] THEN
             REWRITE_TAC [EQ_SYM_EQ;NOT_SUC] THEN NO_TAC
             ORELSE ASM_SIMP_TAC [APPEND;CONS_11;LENGTH;SUC_INJ;CONJ_ACI]));;

let EL_EQ = prove
  (`!xs:a list ys. LENGTH xs = LENGTH ys
            ==> ((!n. n < LENGTH xs ==> EL n xs = EL n ys) <=> xs = ys)`,
   LIST_INDUCT_APPEND_TAC THEN LIST_INDUCT_APPEND_TAC
     THEN SIMP_TAC [LENGTH;LT;EQ_SYM_EQ;LENGTH_EQ_NIL
                   ;APPEND_EQ_NIL;NOT_CONS_NIL]
     THEN REWRITE_TAC [LENGTH_APPEND;LENGTH;ADD_SUC;ADD_0;SUC_INJ;LT]
     THEN REWRITE_TAC [TAUT `p \/ q ==> r <=> (p ==> r) /\ (q ==> r)`]
     THEN SIMP_TAC [EL_APPEND;APPEND_EQ;CONS_11;LT;APPEND_EQ;CONS_11]
     THEN REWRITE_TAC [LT_REFL;SUB_REFL;EL;HD;FORALL_AND_THM]
     THEN CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [EQ_SYM_EQ]))
     THEN ASM_SIMP_TAC [] THEN MESON_TAC []);;

let EL_EQ_IMP = prove
  (`!xs:a list ys.
      LENGTH xs = LENGTH ys /\ (!n. n < LENGTH xs ==> EL n xs = EL n ys)
        ==> xs = ys`, MESON_TAC [EL_EQ]);;

(* Well-defined versions of HD and TL. *)
let HEAD = new_recursive_definition list_RECURSION
  `HEAD [] = []
   /\ HEAD (CONS x xs) = [x]`;;

let TAIL = new_recursive_definition list_RECURSION
  `TAIL [] = []
  /\ TAIL (CONS (x:a) xs) = xs`;;

let ADJACENT = new_definition
  `ADJACENT (xs:a list) = ZIP (BUTLAST xs) (TAIL xs)`;;

let BREAK_ACC = new_recursive_definition list_RECURSION
  `BREAK_ACC p [] acc    = (REVERSE acc,[])
   /\ BREAK_ACC p (CONS x xs) acc = 
        if p x then (REVERSE acc, CONS x xs)
        else BREAK_ACC p xs (CONS x acc)`;;

let IS_PREFIX_OF = define 
  `(!ys. IS_PREFIX_OF [] ys <=> T)
   /\ (!x xs. IS_PREFIX_OF (CONS x xs) [] <=> F)
   /\ (!x y xs ys. IS_PREFIX_OF (CONS x xs) (CONS y ys)
          <=> x = y /\ IS_PREFIX_OF xs ys)`;;

let TAKE = define
  `TAKE 0 (xs:a list)          = []
   /\ TAKE n []                = []     
   /\ TAKE (SUC n) (CONS x xs) = CONS x (TAKE n xs)`;;

let DROP = define
  `DROP 0 (xs:a list)          = xs
   /\ DROP n []                = [] 
   /\ DROP (SUC n) (CONS x xs) = DROP n xs`;;

let BREAK = define
  `BREAK p xs = BREAK_ACC p xs []`;;

let LENGTH_TAIL = prove
  (`!xs : a list. LENGTH (TAIL xs) = PRE (LENGTH xs)`,
   LIST_INDUCT_TAC THEN REWRITE_TAC [LENGTH;TAIL] THEN ARITH_TAC);;

let EL_TAIL = prove
  (`!n xs. SUC n < LENGTH xs ==> EL n (TAIL xs) = EL (SUC n) xs`,
   GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC [LENGTH;TAIL;LT;EL;TL]);;

let TAIL_APPEND = prove
  (`!(xs : a list) ys. ~(xs = [])
     ==> TAIL (APPEND xs ys) = APPEND (TAIL xs) ys`,
   LIST_INDUCT_TAC THEN REWRITE_TAC [APPEND;TAIL]);;

let LENGTH_REVERSE = prove
  (`!xs:a list. LENGTH (REVERSE xs) = LENGTH xs`,
   LIST_INDUCT_TAC THEN ASM_REWRITE_TAC
     [LENGTH;REVERSE;LENGTH_APPEND] THEN ARITH_TAC);;

let REVERSE_EQ_NIL = prove
  (`!xs : a list. REVERSE xs = [] <=> xs = []`,
   REWRITE_TAC [GSYM LENGTH_EQ_NIL;LENGTH_REVERSE]);;

let TAIL_REVERSE = prove
  (`!xs : a list. TAIL (REVERSE xs) = REVERSE (BUTLAST xs)`,
   LIST_INDUCT_TAC THEN REWRITE_TAC [REVERSE;TAIL;BUTLAST]
     THEN ASM_CASES_TAC `t : a list = []`
      THENL [ASM_REWRITE_TAC [REVERSE;TAIL;BUTLAST;APPEND]
            ;ASM_SIMP_TAC [REVERSE_EQ_NIL;REVERSE
                          ;TAIL_APPEND;BUTLAST]]);;

let REVERSE_EQ = 
  let APPEND_11_LEMMA = prove
    (`!xs ys x:a y. APPEND xs [x] = APPEND ys [y] <=> xs = ys /\ x = y`,
     LIST_INDUCT_TAC THEN LIST_INDUCT_TAC
       THEN REWRITE_TAC [APPEND;CONS_11;APPEND_EQ_NIL;NOT_CONS_NIL]
       THEN REWRITE_TAC [EQ_SYM_EQ;APPEND;CONS_11;APPEND_EQ_NIL;NOT_CONS_NIL]
       THEN ASM_MESON_TAC []) in
  prove
    (`!xs:a list ys. REVERSE xs = REVERSE ys <=> xs = ys`,
     LIST_INDUCT_TAC THEN LIST_INDUCT_TAC
       THEN REPEAT
       (ASM_REWRITE_TAC [REVERSE;REVERSE_EQ_NIL;NOT_CONS_NIL;APPEND_EQ_NIL
                        ;APPEND_11_LEMMA;CONS_11;CONJ_ACI]
          THEN REWRITE_TAC [EQ_SYM_EQ]));;

let APPEND_EQ_2 = prove
  (`!xs:a list ys vs us. LENGTH ys = LENGTH vs
      ==> ((APPEND xs ys = APPEND us vs) <=> xs = us /\ ys = vs)`,
   let REV_INDUCT = REWRITE_RULE [REVERSE_REVERSE]
     (ISPECL [`REVERSE:a list -> a list`;`REVERSE:a list -> a list`]
        ONE_ONE_INDUCT) in
   REPEAT (MATCH_MP_TAC REV_INDUCT THEN GEN_TAC)
     THEN REWRITE_TAC [GSYM REVERSE_APPEND;LENGTH_REVERSE;REVERSE_EQ]
     THEN MESON_TAC [APPEND_EQ]);;

let HD_REVERSE = prove
  (`!xs : a list. ~(xs = []) ==> HD (REVERSE xs) = LAST xs`,
      LIST_INDUCT_TAC
      THEN REWRITE_TAC [REVERSE;HD_APPEND;LAST;REVERSE_EQ_NIL;HD]
      THEN ASM_MESON_TAC []);;

let LAST_REVERSE = prove
  (`!xs : a list. ~(xs = []) ==> LAST (REVERSE xs) = HD xs`,
   LIST_INDUCT_TAC THEN
     REWRITE_TAC [REVERSE;HD_APPEND;LAST;REVERSE_EQ_NIL
                 ;HD;NOT_CONS_NIL;LAST_APPEND]);;

let BUTLAST_APPEND = prove
  (`!(xs : a list) ys. ~(ys = [])
     ==> BUTLAST (APPEND xs ys) = APPEND xs (BUTLAST ys)`,
   LIST_INDUCT_TAC THEN REWRITE_TAC [APPEND;BUTLAST]
     THEN SIMP_TAC [APPEND_EQ_NIL;BUTLAST]
     THEN ASM_MESON_TAC []);;

let BUTLAST_LENGTH = prove
  (`!xs : a list. LENGTH (BUTLAST xs) = PRE (LENGTH xs)`,
   LIST_INDUCT_TAC THEN REWRITE_TAC [LENGTH;TAIL]
     THENL [REWRITE_TAC [BUTLAST;LENGTH] THEN ARITH_TAC
           ;REWRITE_TAC [BUTLAST] THEN COND_CASES_TAC
             THENL [ASM_REWRITE_TAC [LENGTH] THEN ARITH_TAC
                   ;ASM_SIMP_TAC [LENGTH_EQ_NIL;LENGTH
                                 ;ARITH_RULE `~(n = 0)
                                   ==> SUC (PRE n) = PRE (SUC n)`]]]);;

let BUTLAST_REVERSE = prove
  (`!xs : a list. BUTLAST (REVERSE xs) = REVERSE (TAIL xs)`,
   LIST_INDUCT_TAC THEN ASM_REWRITE_TAC [REVERSE;TAIL;BUTLAST]
     THEN REWRITE_TAC [REVERSE] THEN ASM_CASES_TAC `t : a list = []`
      THENL [ASM_REWRITE_TAC [REVERSE;APPEND;BUTLAST;TAIL]
            ;ASM_SIMP_TAC [NOT_CONS_NIL;BUTLAST_APPEND;TAIL]
              THEN REWRITE_TAC [BUTLAST;APPEND_NIL]]);;

let MEM_BUTLAST = prove
  (`!x:a xs. ~(xs = []) ==> (MEM x xs <=> LAST xs = x \/ MEM x (BUTLAST xs))`,
   GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC []
     THEN ASM_CASES_TAC `t:a list = []`
      THEN ASM_SIMP_TAC [NOT_CONS_NIL;LAST;BUTLAST;MEM;EQ_SYM_EQ;DISJ_ACI]);;

let MEM_HD = prove
  (`!xs:a list. ~(xs = []) ==> MEM (HD xs) xs`,
   SIMP_TAC [MEM_EXISTS_EL;EL] 
     THEN REPEAT STRIP_TAC THEN EXISTS_TAC `0`
     THEN REWRITE_TAC [EL]
     THEN ASM_MESON_TAC [LENGTH_EQ_NIL;ARITH_RULE `~(n = 0) <=> 0 < n`]);;

let MEM_LAST = prove
  (`!xs:a list. ~(xs = []) ==> MEM (LAST xs) xs`,
   SIMP_TAC [MEM_EXISTS_EL;LAST_EL]
     THEN ASM_MESON_TAC [ARITH_RULE `~(x = 0) ==> x - 1 < x`;LENGTH_EQ_NIL]);;

let MEM_REVERSE =
  prove (`!p xs : a list. MEM p (REVERSE xs) <=> MEM p xs`,
         GEN_TAC THEN LIST_INDUCT_TAC THEN
           REWRITE_TAC [REVERSE;MEM_APPEND]
           THEN ASM_MESON_TAC [MEM]);;

let ALL_REVERSE =
  prove (`ALL p (REVERSE xs) <=> ALL p xs`,
            MESON_TAC [MEM_REVERSE;ALL_MEM]);;

let EX_REVERSE =
  prove (`EX p (REVERSE xs) <=> EX p xs`,
         MESON_TAC [MEM_REVERSE;EX_MEM]);;

let ZIP_APPEND =
  prove (`!(xs : a list) ys us vs.
            LENGTH xs = LENGTH us /\ LENGTH ys = LENGTH vs
                      ==> ZIP (APPEND xs ys) (APPEND us vs)
                          = APPEND (ZIP xs us) (ZIP ys vs)`,
         LIST_INDUCT_TAC THEN 
           SIMP_TAC [LENGTH;EQ_SYM_EQ;LENGTH_EQ_NIL;ZIP_DEF;APPEND]
           THEN GEN_TAC THEN LIST_INDUCT_TAC
           THEN SIMP_TAC [LENGTH;EQ_SYM_EQ;LENGTH_EQ_NIL;ZIP_DEF
                         ;APPEND;NOT_SUC]
           THEN REWRITE_TAC [ZIP;APPEND;LENGTH;SUC_INJ;HD;TL]
           THEN ASM_MESON_TAC []);;

let ZIP_REVERSE =
  prove (`!(xs : a list) (ys : a list).
            LENGTH xs = LENGTH ys ==>
            REVERSE (ZIP xs ys) = ZIP (REVERSE xs) (REVERSE ys)`,
         LIST_INDUCT_TAC THEN REWRITE_TAC [LENGTH;REVERSE;ZIP_DEF]
           THEN LIST_INDUCT_TAC THEN REWRITE_TAC [LENGTH;NOT_SUC]
           THEN REWRITE_TAC [ZIP_DEF;HD;TL;REVERSE;LENGTH]
           THEN SIMP_TAC [ZIP;ZIP_APPEND
                         ;LENGTH_REVERSE;SUC_INJ;LENGTH]
           THEN ASM_MESON_TAC []);;

let MEM_REVERSE =
  prove (`!xs x : a. MEM x (REVERSE xs) <=> MEM x xs`,
         LIST_INDUCT_TAC THEN REWRITE_TAC [MEM;REVERSE;MEM_APPEND]
           THEN ASM_MESON_TAC []);;

let ZIP_SWAP = prove
  (`!(xs : a list) ys. LENGTH xs = LENGTH ys
      ==> ZIP xs ys = MAP (\(x,y). (y,x)) (ZIP ys xs)`,
  LIST_INDUCT_TAC THEN SIMP_TAC [LENGTH_EQ_NIL;LENGTH
                                ;EQ_SYM_EQ;ZIP;MAP]
    THEN LIST_INDUCT_TAC THEN REWRITE_TAC [LENGTH;NOT_SUC;ZIP;MAP]
    THEN ASM_MESON_TAC [LENGTH;SUC_INJ]);;

let APPEND_HEAD_TAIL = prove
  (`!(xs : a list). ~(xs = []) ==> APPEND [HD xs] (TAIL xs) = xs`,
   LIST_INDUCT_TAC THEN REWRITE_TAC [APPEND;HD;TAIL]);;

let ADJACENT_APPEND = prove
  (`!xs : (a list) ys. ~(xs = []) /\ ~(ys = []) ==>
      ADJACENT (APPEND xs ys)
      = APPEND (ADJACENT xs) (APPEND [LAST xs,HD ys] (ADJACENT ys))`,
   REWRITE_TAC [ADJACENT] THEN SIMP_TAC [BUTLAST_APPEND;TAIL_APPEND]
     THEN REPEAT GEN_TAC THEN DISCH_TAC
     THEN MP_TAC (ISPECL [`xs:a list`] (GSYM APPEND_BUTLAST_LAST))
     THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (fun thm ->
       CONV_TAC (LAND_CONV (LAND_CONV (SUBS_CONV [thm]))))
     THEN MP_TAC (ISPECL [`ys:a list`] (GSYM APPEND_HEAD_TAIL))
     THEN ASM_REWRITE_TAC [] THEN DISCH_THEN (fun thm ->
       CONV_TAC (LAND_CONV (RAND_CONV (SUBS_CONV [thm]))))
     THEN REWRITE_TAC [HD;GSYM APPEND_ASSOC]
     THEN SIMP_TAC
     [LENGTH;LENGTH_APPEND;LENGTH_TAIL;BUTLAST_LENGTH;ZIP_APPEND
     ;ARITH_RULE `SUC 0 + PRE (SUC x) = SUC x`]
     THEN ASM_MESON_TAC [ZIP]);;

let ADJACENT_CONS = prove
  (`!x:a y t. ADJACENT (CONS x (CONS y t))
                = CONS (x,y) (ADJACENT (CONS y t))`,
   REWRITE_TAC [ADJACENT;BUTLAST;TAIL;NOT_CONS_NIL]
     THEN REPEAT GEN_TAC THEN ASM_CASES_TAC `t = [] : a list`
     THEN ASM_REWRITE_TAC [ZIP]);;

(* Should I have just defined it this way? *)
let ADJACENT_CLAUSES = prove
  (`!x y t. ADJACENT [] = []
            /\ ADJACENT [x] = []
            /\ ADJACENT (CONS x (CONS y t)) 
               = CONS (x,y) (ADJACENT (CONS y t))`,
   REWRITE_TAC [ADJACENT_CONS;CONS_11]
     THEN REWRITE_TAC [ADJACENT;BUTLAST;TAIL;ZIP]);;

let ADJACENT_MEM2 = prove
  (`!xs x:a y. MEM (x,y) (ADJACENT xs) ==> MEM x xs /\ MEM y xs`,
   LIST_INDUCT_TAC
     THEN DISJ_CASES_TAC (ISPECL [`t:a list`] list_CASES)
     THEN TRY (ASM_REWRITE_TAC [ADJACENT;ZIP;TAIL;BUTLAST;MEM] THEN NO_TAC)
     THEN POP_ASSUM (REPEAT_TCL CHOOSE_THEN ASSUME_TAC)
     THEN ASM_REWRITE_TAC [MEM;PAIR_EQ;ADJACENT_CONS]
     THEN ASM_MESON_TAC [MEM]);;

let EL_IS_PREFIX_OF = prove
  (`!xs:a list ys n. IS_PREFIX_OF xs ys /\ n < LENGTH xs
       ==> (EL n xs = EL n ys)`,
   REPEAT LIST_INDUCT_TAC THEN REWRITE_TAC [LENGTH;IS_PREFIX_OF]
     THEN (REWRITE_TAC [LT] THEN NO_TAC
             ORELSE INDUCT_TAC THEN SIMP_TAC [LT_SUC;EL;HD;TL]
             THEN ASM_MESON_TAC []));;

let LENGTH_IS_PREFIX_OF = prove
  (`!xs ys. IS_PREFIX_OF xs ys ==> LENGTH xs <= LENGTH ys`,
   REPEAT LIST_INDUCT_TAC THEN REWRITE_TAC [LENGTH;LE_REFL;LE_0]
     THEN REWRITE_TAC [IS_PREFIX_OF;LENGTH;LE_SUC]
     THEN ASM_MESON_TAC []);;

let IS_PREFIX_OF_APPEND = prove
  (`!xs:a list ys. IS_PREFIX_OF xs (APPEND xs ys)`,
   LIST_INDUCT_TAC THEN ASM_SIMP_TAC [APPEND;IS_PREFIX_OF]);;

let IS_PREFIX_OF_EXISTS_APPEND = prove
  (`!xs ys zs. IS_PREFIX_OF xs ys <=> ?zs. APPEND xs zs = ys`,
   LIST_INDUCT_TAC THEN LIST_INDUCT_TAC
     THEN REWRITE_TAC [APPEND;IS_PREFIX_OF;NOT_CONS_NIL;IS_PREFIX_OF
                      ;EXISTS_REFL;CONS_11]
     THEN ASM_MESON_TAC []);;

let IS_PREFIX_OF_ADJACENT = prove
  (`!(xs:a list) ys. IS_PREFIX_OF xs ys
       ==> IS_PREFIX_OF (ADJACENT xs) (ADJACENT ys)`,
   REPEAT (LIST_INDUCT_TAC2 THENL
     [REWRITE_TAC [ADJACENT;ZIP;BUTLAST;TAIL;IS_PREFIX_OF]
     ;REWRITE_TAC [ADJACENT;ZIP;BUTLAST;TAIL;IS_PREFIX_OF]
     ;ALL_TAC]
     THEN REWRITE_TAC [ADJACENT_CONS] THEN ASM_SIMP_TAC [IS_PREFIX_OF]));;

let TAKE_ADJACENT = prove
  (`!xs:a list n. TAKE n (ADJACENT xs) = ADJACENT (TAKE (SUC n) xs)`,
   LIST_INDUCT_TAC2 THEN INDUCT_TAC
     THEN ASM_REWRITE_TAC [ADJACENT_CONS;TAKE;CONS_11]
     THEN REWRITE_TAC [TAKE;ADJACENT;BUTLAST;TAIL;ZIP]);;

let DROP_ADJACENT = prove
  (`!xs:a list n. DROP n (ADJACENT xs) = ADJACENT (DROP n xs)`,
   LIST_INDUCT_TAC2 THEN INDUCT_TAC THEN
     ASM_REWRITE_TAC [ADJACENT_CONS;DROP]
     THEN REWRITE_TAC [ADJACENT;BUTLAST;DROP;TAIL;ZIP]);;

let MEM_IS_PREFIX_OF = prove
  (`!xs:a list ys. IS_PREFIX_OF xs ys ==> (!x. MEM x xs ==> MEM x ys)`,
   REPEAT (LIST_INDUCT_TAC THEN REWRITE_TAC [MEM;IS_PREFIX_OF])
     THEN ASM_MESON_TAC []);;

let MEM_ZIP_SWAP = prove
  (`!xs:a list ys:b list x y.
      LENGTH xs = LENGTH ys
      ==> (MEM (x,y) (ZIP xs ys) <=> MEM (y,x) (ZIP ys xs))`,
   REPEAT GEN_TAC THEN ASSUME_ANT
     THEN POP_ASSUM ((fun thm ->
       CONV_TAC (RAND_CONV (LAND_CONV (ONCE_REWRITE_CONV
                                         [thm])))) o MATCH_MP ZIP_SWAP)
     THEN REWRITE_TAC [MEM_MAP;EXISTS_PAIR_THM;PAIR_EQ]
     THEN MESON_TAC []);;

let MEM_ADJACENT_REVERSE = prove
  (`!xs x y. MEM (y,x) (ADJACENT (REVERSE xs)) <=> MEM (x,y) (ADJACENT xs)`,
   SIMP_TAC
     [LENGTH_TAIL;BUTLAST_LENGTH;ADJACENT;TAIL_REVERSE;BUTLAST_REVERSE;
      GSYM ZIP_REVERSE;MEM_REVERSE;MEM_ZIP_SWAP;BUTLAST_LENGTH;LENGTH_TAIL]);;

let APPEND_CONS_NOT_NIL = prove
  (`!xs:a list ys y. ~(APPEND xs (CONS y ys) = [])`,
   REPEAT GEN_TAC
     THEN DISCH_THEN (MP_TAC o AP_TERM `LENGTH : a list -> num`)
     THEN REWRITE_TAC [LENGTH;LENGTH_APPEND] THEN ARITH_TAC);;

let HEAD_TAIL = prove
  (`!xs. APPEND (HEAD xs) (TAIL xs) = xs`,
   LIST_INDUCT_TAC THEN REWRITE_TAC [HEAD;TAIL;APPEND]);;

let BREAK_ACC_APPEND = prove
  (`!p (xs:a list) y ys. FST (BREAK_ACC p xs (APPEND ys [y]))
     = CONS y (FST (BREAK_ACC p xs ys))
     /\ SND (BREAK_ACC p xs (APPEND ys [y]))
     = SND (BREAK_ACC p xs ys)`,
   GEN_TAC THEN LIST_INDUCT_TAC
     THEN REWRITE_TAC [BREAK_ACC;REVERSE_APPEND;REVERSE;APPEND]
     THEN ASM_CASES_TAC `(p (h:a)):bool`
     THEN ASM_REWRITE_TAC [GSYM (CONJUNCT2 APPEND)]);;

let BREAK_ACC_CONS =
  GENL [`p:a->bool`; `xs:a list`; `y:a`]
    (REWRITE_RULE [APPEND]
       (SPECL [`p:a -> bool`;`xs:a list`;`y:a`;`[]:a list`] BREAK_ACC_APPEND));;

let BREAK_CONS = prove
  (`!p x:a xs. FST (BREAK p (CONS x xs)) =
      (if p x then [] else CONS x (FST (BREAK p xs)))
      /\ SND (BREAK p (CONS x xs)) =
         if p x then CONS x xs else SND (BREAK p xs)`,
        REPEAT GEN_TAC THEN
          MP_TAC (SPECL [`p:a->bool`;`xs:a list`;`x:a`;`[]:a list`]
                    BREAK_ACC_APPEND)
          THEN SIMP_TAC [APPEND;REVERSE;BREAK;BREAK_ACC;COND_RAND;COND_ID]);;

let BREAK_APPEND = prove
  (`!p:a->bool xs.
      (EX p xs ==> FST (BREAK p (APPEND xs ys)) = FST (BREAK p xs))
      /\ (EX p xs ==>
            SND (BREAK p (APPEND xs ys)) = APPEND (SND (BREAK p xs)) ys)`,
   GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC [APPEND;BREAK_CONS]
     THEN ASM_MESON_TAC [EX;APPEND]);;

let BREAK_FST_ALL = prove
  (`!p (xs:a list). ALL (\x. ~(p x)) (FST (BREAK p xs))`,
   GEN_TAC THEN REWRITE_TAC [BREAK] THEN LIST_INDUCT_TAC
     THEN ASM_REWRITE_TAC [BREAK_ACC;REVERSE;BREAK_ACC_CONS;COND_RAND;ALL]
     THEN MESON_TAC []);;

let BREAK_SND_EX = prove
  (`!p (xs:a list). EX p xs ==> ~(SND (BREAK p xs) = []) /\ p (HD (SND (BREAK p xs)))`,
   GEN_TAC THEN REWRITE_TAC [BREAK] THEN LIST_INDUCT_TAC
     THEN ASM_REWRITE_TAC [EX;BREAK_ACC_CONS;BREAK_ACC
                          ;REVERSE;COND_RAND;HD;EX]
     THEN ASM_MESON_TAC [NOT_CONS_NIL]);;

let APPEND_BREAK = prove
  (`!p (xs:a list). APPEND (FST (BREAK p xs)) (SND (BREAK p xs)) = xs`,
   GEN_TAC THEN REWRITE_TAC [BREAK] THEN LIST_INDUCT_TAC
     THEN REWRITE_TAC [BREAK_ACC;REVERSE;APPEND]
     THEN ASM_REWRITE_TAC [BREAK_ACC;COND_RAND]
     THEN COND_CASES_TAC
     THEN ASM_REWRITE_TAC [APPEND;REVERSE;BREAK_ACC_CONS]);;

let APPEND_HD_TL = prove
  (`!xs. ~(xs:a list = []) ==> CONS (HD xs) (TL xs) = xs`,
   LIST_INDUCT_TAC THEN REWRITE_TAC [NOT_CONS_NIL;HD;TL]);;

let ALL_SUBSET = prove
  (`!P xs:a list. ALL P xs <=> set_of_list xs SUBSET P`,
   GEN_TAC THEN LIST_INDUCT_TAC
     THEN ASM_REWRITE_TAC [ALL;set_of_list;IN;INSERT_SUBSET;EMPTY_SUBSET]);;

let LENGTH_EQ_CONV =
  let length_eq_1 = prove
    (`LENGTH xs = SUC 0 <=> ?x. xs = [x]`,
     MESON_TAC [LENGTH_EQ_CONS;LENGTH_EQ_NIL]) in
  let exists_length_eq_1 = prove
     (`(?xs. P xs /\ LENGTH xs = SUC 0) <=> ?x. P [x]`,
      MESON_TAC [LENGTH_EQ_CONS;LENGTH_EQ_NIL]) in
  let exists_length_eq_suc = prove
    (`(?xs. P xs /\ LENGTH xs = SUC n)
      <=> ?x xs. P (CONS x xs) /\ LENGTH xs = n`,
     MESON_TAC [LENGTH_EQ_CONS;LENGTH_EQ_NIL]) in
  let rec exists_CONV tm =
    BINDER_CONV (BINDER_CONV (RAND_CONV (TRY_CONV (RAND_CONV num_CONV)))
                   THENC (REWR_CONV exists_length_eq_1
                            ORELSEC (REWR_CONV exists_length_eq_suc
                                       THENC exists_CONV))) tm in
  REWR_CONV LENGTH_EQ_NIL
    ORELSEC (TRY_CONV (RAND_CONV num_CONV)
               THENC (REWR_CONV length_eq_1
                        ORELSEC (REWR_CONV LENGTH_EQ_CONS
                                   THENC exists_CONV)));;

let TAKE_APPEND = prove
  (`!xs:a list ys. TAKE (LENGTH xs) (APPEND xs ys) = xs`,
   LIST_INDUCT_TAC THEN
     ASM_REWRITE_TAC [LENGTH;APPEND;TAKE]);;

let DROP_APPEND = prove
  (`!xs:a list ys. DROP (LENGTH xs) (APPEND xs ys) = ys`,
   LIST_INDUCT_TAC THEN
     ASM_REWRITE_TAC [LENGTH;APPEND;DROP]);;

let APPEND_TAKE = prove
  (`!n xs:a list ys. APPEND xs (TAKE n ys)
   = TAKE (LENGTH xs + n) (APPEND xs ys)`,
   GEN_TAC THEN LIST_INDUCT_TAC
     THEN ASM_REWRITE_TAC [APPEND;LENGTH;TAKE;ADD;APPEND;CONS_11]);;

let TAKE_LEFT_APPEND = 
  GSYM (REWRITE_RULE [TAKE;ADD_0;APPEND_NIL] (SPECL [`0`] APPEND_TAKE));;

let TAKE_DROP = prove
  (`!n (xs:a list). APPEND (TAKE n xs) (DROP n xs) = xs`,
   ONCE_REWRITE_TAC [SWAP_FORALL_THM]
     THEN LIST_INDUCT_TAC THEN REWRITE_TAC [TAKE;DROP;APPEND]
     THEN INDUCT_TAC
     THEN ASM_REWRITE_TAC [TAKE;DROP;HEAD;TAIL;APPEND;CONS_11]);;

let LENGTH_TAKE = prove
  (`!xs:a list n. LENGTH (TAKE n xs) = MIN n (LENGTH xs)`,
   LIST_INDUCT_TAC
     THENL [SIMP_TAC [TAKE;LENGTH;MIN;LE;COND_ID]
           ;INDUCT_TAC THEN ASM_REWRITE_TAC [LENGTH;TAKE;APPEND;HEAD;TAIL
                                            ;MIN;LE_0;LE_SUC]
             THEN COND_CASES_TAC THEN REWRITE_TAC []]);;

let LENGTH_DROP = prove
  (`!xs:a list n. LENGTH (DROP n xs) = LENGTH xs - n`,
   LIST_INDUCT_TAC THEN SIMP_TAC [DROP;LENGTH;SUB_0]
     THEN INDUCT_TAC THEN ASM_REWRITE_TAC [LENGTH;DROP;SUB;LE_0;TAIL;DROP]
     THEN ARITH_TAC);;

let LENGTH_ADJACENT = prove
  (`!xs. LENGTH (ADJACENT xs) = PRE (LENGTH xs)`,
   LIST_INDUCT_TAC2
     THEN (ASM_REWRITE_TAC [ADJACENT_CONS;SUC_INJ;PRE;LENGTH]
             THEN REWRITE_TAC [ADJACENT;PRE;BUTLAST;TAIL;ZIP;LENGTH]));;

let EL_ADJACENT = prove
  (`!n (xs:a list). SUC n < LENGTH xs
     ==> EL n (ADJACENT xs) = (EL n xs, EL (SUC n) xs)`,
   INDUCT_TAC THEN LIST_INDUCT_TAC2
     THEN (REWRITE_TAC [LENGTH;LT;NOT_SUC;EL;ADJACENT_CONS;HD;TL;PAIR_EQ]
             THEN NO_TAC
             ORELSE (ONCE_REWRITE_TAC[LENGTH]
                       THEN ONCE_REWRITE_TAC [LT_SUC;EL]
                       THEN ASM_REWRITE_TAC [ADJACENT_CONS;TL;LT;NOT_SUC])));;

let MEM_EL_ADJACENT = prove
  (`!n (xs:a list). SUC n < LENGTH xs
      ==> MEM (EL n xs, EL (SUC n) xs) (ADJACENT xs)`,
   REWRITE_TAC [MEM_EXISTS_EL] THEN REPEAT GEN_TAC THEN DISCH_TAC
     THEN EXISTS_TAC `n:num` THEN ASM_SIMP_TAC [EL_ADJACENT;LENGTH_ADJACENT]
     THEN ASM_ARITH_TAC);;

let ADJACENT_EQ_NIL = prove
  (`!xs:a list. ADJACENT xs = [] <=> xs = [] \/ ?x. xs = [x]`,
   LIST_INDUCT_TAC2 THEN REWRITE_TAC [ADJACENT_CONS]
     THEN REWRITE_TAC [ADJACENT;NOT_CONS_NIL;CONS_11;TAIL;BUTLAST;ZIP]
     THEN MESON_TAC []);;

let ADJACENT_EQ_CONS = prove
  (`!x:a xs ys. SUC 0 < LENGTH xs /\ SUC 0 < LENGTH ys
      /\ ADJACENT xs = ADJACENT ys
      ==> ADJACENT (CONS x xs) = ADJACENT (CONS x ys)`,
   GEN_TAC
     THEN REWRITE_TAC [IMP_CONJ;NOT_EMPTY_EXISTS;LENGTH_EQ_NIL
                      ;ARITH_RULE `SUC 0 < x <=> ~(x = 0) /\ ~(x = SUC 0)`]
     THEN REPEAT GEN_TAC
     THEN REPEAT (STRIP_TAC THEN ASM_REWRITE_TAC
                    [LENGTH;SUC_INJ;NOT_EMPTY_EXISTS;LENGTH_EQ_NIL])
     THEN ASM_REWRITE_TAC [ADJACENT_CONS;CONS_11]
     THEN POP_ASSUM MP_TAC THEN SIMP_TAC [ADJACENT_CONS;CONS_11;PAIR_EQ]);;

let ADJACENT_EQ = prove
  (`!xs:a list ys. SUC 0 < LENGTH xs /\ SUC 0 < LENGTH ys
       ==> (ADJACENT xs = ADJACENT ys <=> xs = ys)`,
   LIST_INDUCT_TAC2 THEN REWRITE_TAC [LENGTH;LT;NOT_SUC]
     THEN GEN_TAC THEN STRUCT_CASES_TAC (ISPEC `ys':a list` list_CASES)
     THENL [REWRITE_TAC [LENGTH;LT;NOT_SUC];ALL_TAC]
     THEN STRUCT_CASES_TAC (ISPEC `t:a list` list_CASES)
     THENL [REWRITE_TAC [LENGTH;LT;NOT_SUC];ALL_TAC]
     THEN REWRITE_TAC [ADJACENT_CONS;CONS_11;PAIR_EQ]
     THEN DISJ_CASES_TAC (ARITH_RULE `LENGTH (CONS (y:a) ys) = 0
                                      \/ LENGTH (CONS y ys) = SUC 0 
                                      \/ SUC 0 < LENGTH (CONS y ys)`)
     THEN TRY (POP_ASSUM DISJ_CASES_TAC)
     THEN DISJ_CASES_TAC (ARITH_RULE `LENGTH (CONS (h':a) t') = 0
                                      \/ LENGTH (CONS h' t') = SUC 0
                                      \/ SUC 0 < LENGTH (CONS h' t')`)
     THEN TRY (POP_ASSUM DISJ_CASES_TAC)
     THEN ASM_SIMP_TAC []
     THEN REWRITE_ASM_TAC [LENGTH;LT;NOT_SUC;SUC_INJ;LENGTH_EQ_NIL
                          ;NOT_CONS_NIL]
     THEN TRY (FIRST_ASSUM CONTR_TAC)
     THEN ASM_SIMP_TAC [ADJACENT_CLAUSES;EQ_SYM_EQ;ADJACENT_EQ_NIL
                       ;NOT_CONS_NIL;CONS_11]
     THEN MESON_TAC []);;
   
let REVERSE_EL = prove
  (`!xs:a list n. n < LENGTH xs
       ==> EL n xs = EL (LENGTH xs - SUC n) (REVERSE xs)`,
   LIST_INDUCT_TAC THENL [REWRITE_TAC [LENGTH] THEN ARITH_TAC;ALL_TAC]
     THEN INDUCT_TAC THENL [ONCE_REWRITE_TAC [GSYM LENGTH_REVERSE]
                               THEN REWRITE_TAC [LENGTH_EQ_NIL;LT_NZ]
                               THEN SIMP_TAC [REWRITE_RULE [ONE] (GSYM LAST_EL)] 
                               THEN REWRITE_TAC [REVERSE;EL;LAST_APPEND
                                                ;NOT_CONS_NIL;HD]
                               THEN REWRITE_TAC [LAST];ALL_TAC]
     THEN REWRITE_TAC [LENGTH;LT_SUC;SUB_SUC;EL;TL;REVERSE
                      ;EL_APPEND;LENGTH_REVERSE]
     THEN ASM_SIMP_TAC [] THEN ARITH_TAC);;

(* It's easier to see what's going on with arithmetic, but the inductive
   proof is given below. *)
let DROP_EL = prove
  (`!xs:a list m n. n < LENGTH xs - m
     ==> EL n (DROP m xs) = EL (m + n) xs`,
   REPEAT GEN_TAC THEN DISCH_TAC
     THEN MP_TAC (ISPECL [`m+n`;`TAKE m (xs:a list)`;`DROP m (xs:a list)`]
                    EL_APPEND)
     THEN ASM_SIMP_TAC [TAKE_DROP;LENGTH_TAKE;MIN]
     THEN SUBGOAL_THEN `m <= LENGTH (xs:a list)` ASSUME_TAC
     THENL [ASM_ARITH_TAC;ALL_TAC] THEN
     ASM_REWRITE_TAC [ARITH_RULE `(m + n) - m = n /\ ~(m + n < m)`]);;

(* let EL_0_DROP = prove *)
(*   (`!xs:a list n. n < LENGTH xs ==> EL 0 (DROP n xs) = EL n xs`, *)
(*    LIST_INDUCT_TAC THEN REWRITE_TAC [LENGTH] THEN INDUCT_TAC *)
(*      THEN REWRITE_TAC [ARITH_RULE `~(n < 0)`;DROP]  *)
(*      THEN CONV_TAC (RAND_CONV (RAND_CONV (REWRITE_CONV [EL;TL]))) *)
(*      THEN ASM_REWRITE_TAC [DROP;LENGTH;LT_SUC]);; *)

(* let EL_DROP = prove *)
(*   (`!xs:a list m n. m + n < LENGTH xs *)
(*         ==> EL n (DROP m xs) = EL (m + n) xs`, *)
(*    LIST_INDUCT_TAC THEN REWRITE_TAC [LENGTH] THEN ARITH_TAC *)
(*      THEN INDUCT_TAC THEN REWRITE_TAC [DROP;ARITH_RULE `0+x=x`] *)
(*      THEN INDUCT_TAC THEN REWRITE_TAC [ADD_0;LENGTH;LT_SUC] *)
(*      THEN CONV_TAC (RAND_CONV (RAND_CONV (REWRITE_CONV [EL;TL]))) *)
(*      THEN ASM_REWRITE_TAC [ADD;LENGTH;LT_SUC;DROP;EL_0_DROP]);; *)

let TAKE_EL = prove
  (`!xs:a list m n. n < MIN m (LENGTH xs) ==> EL n (TAKE m xs) = EL n xs`,
   LIST_INDUCT_TAC THEN REWRITE_TAC [LENGTH] THENL [ARITH_TAC;ALL_TAC]
     THEN INDUCT_TAC THEN REWRITE_TAC [MIN] THENL [ARITH_TAC;ALL_TAC]
     THEN INDUCT_TAC THEN REWRITE_TAC [EL;TAKE;HD;TL] THEN DISCH_TAC
     THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC);;

let DROP_EQ_NIL = prove
  (`!xs:a list n. LENGTH xs <= n <=> DROP n xs = []`,
   LIST_INDUCT_TAC THEN REWRITE_TAC [DROP;LE_0;LENGTH]
     THEN INDUCT_TAC THENL [REWRITE_TAC [LE;LENGTH_EQ_NIL;DROP;NOT_CONS_NIL]
                               THEN ARITH_TAC
                           ;REWRITE_TAC [LENGTH;LE_SUC;DROP]
                             THEN FIRST_ASSUM MATCH_ACCEPT_TAC]);;

let TAKE_ID = prove
  (`!xs:a list n. LENGTH xs <= n <=> TAKE n xs = xs`,
      LIST_INDUCT_TAC THEN REWRITE_TAC [TAKE;LE_0;LENGTH]
        THEN INDUCT_TAC
        THEN REWRITE_TAC [LENGTH;TAKE;LENGTH_EQ_NIL;NOT_CONS_NIL]
        THEN REWRITE_TAC [LENGTH;LE_SUC;TAKE;CONS_11]
        THEN TRY (FIRST_ASSUM MATCH_ACCEPT_TAC)
        THEN ARITH_TAC);;

let MEM_TAKE = prove
  (`!n x:a xs. MEM x (TAKE n xs) ==> MEM x xs`,
   REWRITE_TAC [MEM_EXISTS_EL;LENGTH_TAKE] THEN REPEAT STRIP_TAC
     THEN ASM_SIMP_TAC [TAKE_EL] THEN EXISTS_TAC `i:num` THEN ASM_ARITH_TAC);; 

let MEM_DROP = prove
  (`!n x:a xs. MEM x (DROP n xs) ==> MEM x xs`,
   REWRITE_TAC [MEM_EXISTS_EL;LENGTH_DROP] THEN REPEAT STRIP_TAC
     THEN ASM_SIMP_TAC [DROP_EL] THEN EXISTS_TAC `n+i` THEN ASM_ARITH_TAC);;

let SPLIT_AT_CONV n tm =
  SYM (ISPECL [tm;mk_small_numeral n] TAKE_DROP);;

(* Conversion to church numeral. *)
let ITER = new_recursive_definition num_RECURSION
  `ITER 0 f x:a = x
   /\ ITER (SUC n) f x = f (ITER n f x)`;;

let ITER_INJ = prove
  (`!n. ITER n SUC 0 = n`, INDUCT_TAC THEN ASM_REWRITE_TAC [ITER]);;

let ITER_ADD = prove
  (`!n m f x:'a. ITER (n + m) f x = ITER n f (ITER m f x)`,
   INDUCT_TAC THEN ASM_REWRITE_TAC [ADD;ITER]);;
      
let ITER_SUC = prove
  (`!n f x:a. ITER (SUC n) f x = ITER n f (f x)`,
   ONCE_REWRITE_TAC [ARITH_RULE `SUC n = n + SUC 0`]
     THEN REWRITE_TAC [ITER_ADD;ITER]);;

let ITER_IND = prove
  (`!n P f (x:a). P x /\ (!x. P x ==> P (f x)) ==> P (ITER n f x)`,
   INDUCT_TAC THEN ASM_MESON_TAC [ITER]);;

(* Lift a recursively defined function f to an iteration theorem. *)
let INDUCT_ITER = prove
  (`!f (g:a->a). f 0 = b /\ (!n. f (SUC n) = g (f n))
              ==> !n. ITER n g b = f n`,
   REPEAT GEN_TAC THEN DISCH_TAC THEN INDUCT_TAC
     THEN ASM_REWRITE_TAC [ITER]);;

let ITER_MAP = prove
  (`!(f:a->b) n x g h. (!y. f (g y) = h (f y))
              ==> f (ITER n g x) = ITER n h (f x)`,
   GEN_TAC THEN INDUCT_TAC THEN ASM_SIMP_TAC [ITER]);;

let ITER_MAP2 = prove
  (`!(f:a->a) g n.
      (!x. f x = g x) ==> ITER n f x = ITER n g x`,
   GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN ASM_SIMP_TAC [ITER]);;

let MAXIMUM = prove
  (`!ns b n:num. MEM n ns ==> n <= ITLIST MAX ns b`,
   LIST_INDUCT_TAC THEN REWRITE_TAC [MEM;ITLIST;MAX] THEN REPEAT STRIP_TAC
     THENL [ASM_ARITH_TAC
           ;FIRST_ASSUM
             (fun thm -> POP_ASSUM (MP_TAC o SPECL [`b:num`] o MATCH_MP thm))
             THEN ARITH_TAC]);;

let PAIRWISE_APPEND = prove
  (`!P xs ys. PAIRWISE P (APPEND xs ys) <=>
       PAIRWISE P xs /\ (!x. MEM x xs ==> ALL (P x) ys) /\ PAIRWISE P ys`,
   GEN_TAC THEN LIST_INDUCT_TAC
     THEN ASM_SIMP_TAC [APPEND;MEM;PAIRWISE;ALL_APPEND]
     THEN GEN_TAC THEN EQ_TAC
     THEN ASM_SIMP_TAC [APPEND;MEM;PAIRWISE;ALL_APPEND]
     THEN MESON_TAC []);;

let ALL_DISTINCT_CARD = prove
  (`!xs:a list. PAIRWISE (\x y. ~(x = y)) xs
                <=> CARD (set_of_list xs) = LENGTH xs`,
   LIST_INDUCT_TAC THEN REWRITE_TAC [PAIRWISE;set_of_list;LENGTH;CARD_CLAUSES]
     THEN EQ_TAC
     THENL [SIMP_TAC
               [PAIRWISE;FINITE_SET_OF_LIST;CARD_CLAUSES;set_of_list;IN_SET_OF_LIST]
               THEN DISCH_TAC THEN SUBGOAL_THEN `~MEM (h:a) t` ASSUME_TAC
               THENL [ASM_MESON_TAC [ALL_MEM]
                     ;ASM_REWRITE_TAC [LENGTH;SUC_INJ] THEN ASM_MESON_TAC []]
           ;REWRITE_TAC [PAIRWISE] THEN ASM_CASES_TAC `MEM (h:a) t`
             THEN ASM_SIMP_TAC [FINITE_SET_OF_LIST;CARD_CLAUSES;set_of_list
                               ;IN_SET_OF_LIST;LENGTH;SUC_INJ;PAIRWISE]
             THENL [MP_TAC (ISPECL [`t:a list`] CARD_SET_OF_LIST_LE)
                       THEN ARITH_TAC
                   ;ASM_MESON_TAC [ALL_MEM]]]);;

let CHOOSE_PREFIX = prove
  (`!n xs:a list. n <= LENGTH xs ==> ?ys zs. xs = APPEND ys zs /\ LENGTH ys = n`,
   INDUCT_TAC THENL
     [REWRITE_TAC [LENGTH_EQ_NIL;EQ_SYM_EQ] THEN MESON_TAC [APPEND];ALL_TAC]
     THEN LIST_INDUCT_TAC THEN REWRITE_TAC [LENGTH;NOT_SUC;LE;LENGTH;LE_SUC]
     THEN FIRST_ASSUM (fun thm -> DISCH_THEN (MP_TAC o MATCH_MP thm))
     THEN STRIP_TAC THEN EXISTS_TAC `CONS (h:a) ys`
     THEN EXISTS_TAC `zs:a list`
     THEN ASM_REWRITE_TAC [APPEND;CONS_11;LENGTH;SUC_INJ]);;

let CHOOSE_SUFFIX = prove
  (`!n xs:a list. n <= LENGTH xs
       ==> ?ys zs. xs = APPEND ys zs /\ LENGTH zs = n`,
   GEN_TAC THEN MATCH_MP_TAC (ISPECL [`REVERSE:a list -> a list`]
                                ONE_ONE_INDUCT)
     THEN EXISTS_TAC `REVERSE:a list->a list`
     THEN REWRITE_TAC [REVERSE_REVERSE;LENGTH_REVERSE]
     THEN GEN_TAC THEN DISCH_THEN (REPEAT_TCL CHOOSE_THEN ASSUME_TAC o MATCH_MP
                                     CHOOSE_PREFIX)
     THEN EXISTS_TAC `REVERSE zs:a list`
     THEN EXISTS_TAC `REVERSE ys:a list`
     THEN ASM_REWRITE_TAC [REVERSE_APPEND;LENGTH_REVERSE]);;

let BREAK_LAST = new_definition
  `BREAK_LAST p xs = let ys,zs = BREAK p (REVERSE xs) in
                     REVERSE zs,REVERSE ys`;;

let LAMBDA_PAIRED = prove
  (`!f:a->b->c p. (\(x,y). f x y) p = f (FST p) (SND p)`,
  GEN_TAC THEN MATCH_MP_TAC pair_INDUCT THEN REWRITE_TAC []);;

let APPEND_BREAK_LAST = prove
  (`!p (xs:a list).
      APPEND (FST (BREAK_LAST p xs)) (SND (BREAK_LAST p xs)) = xs`,
   REWRITE_TAC [BREAK_LAST;LET_DEF;LET_END_DEF;LAMBDA_PAIRED
               ;GSYM REVERSE_APPEND;APPEND_BREAK;REVERSE_REVERSE]);;

let BREAK_LAST_SND_ALL = prove
  (`!p (xs:a list). ALL (\x. ~p x) (SND (BREAK_LAST p xs))`,
   REWRITE_TAC
  [BREAK_LAST;LET_DEF;LET_END_DEF;LAMBDA_PAIRED;ALL_REVERSE;BREAK_FST_ALL]);;

let BREAK_LAST_FST_EX = prove
  (`!p (xs:a list). EX p xs ==> ~(FST (BREAK_LAST p xs) = [])
                    /\ p (LAST (FST (BREAK_LAST p xs)))`,
   REWRITE_TAC [BREAK_LAST;LET_DEF;LET_END_DEF;LAMBDA_PAIRED;REVERSE_EQ_NIL]
     THEN ONCE_REWRITE_TAC [GSYM EX_REVERSE]
     THEN SIMP_TAC [BREAK_SND_EX;LAST_REVERSE]);;

let list_CASES_APPEND = prove
  (`!xs:a list. xs = [] \/ ?pre last. xs = APPEND pre [last]`,
   MATCH_MP_TAC (ISPECL [`REVERSE:a list -> a list`]
                          ONE_ONE_INDUCT)
     THEN EXISTS_TAC `REVERSE:a list -> a list`
     THEN REWRITE_TAC [REVERSE_REVERSE] THEN LIST_INDUCT_TAC
       THEN REWRITE_TAC [REVERSE] THEN SIMP_TAC [APPEND_EQ_2;LENGTH;CONS_11]
       THEN MESON_TAC []);;

let MEM_IS_INFIX = prove
  (`!x:a xs. MEM x xs <=> ?ys zs. xs = APPEND ys (CONS x zs)`,
   REPEAT GEN_TAC THEN EQ_TAC
     THENL [SPEC_TAC (`xs:a list`,`xs:a list`)
               THEN LIST_INDUCT_TAC
               THEN REWRITE_TAC [MEM;EQ_SYM_EQ;APPEND_EQ_NIL;NOT_CONS_NIL]
               THEN STRIP_TAC
               THENL [MAP_EVERY EXISTS_TAC [`[]:a list`;`t:a list`]
                         THEN ASM_REWRITE_TAC [APPEND]
                     ;FIRST_X_ASSUM (FIRST_X_MATCH
                                     (REPEAT_TCL CHOOSE_THEN ASSUME_TAC))
                       THEN MAP_EVERY EXISTS_TAC
                       [`CONS h ys:a list`;`zs:a list`]
                       THEN ASM_REWRITE_TAC [APPEND]]
           ;DISCH_THEN (REPEAT_TCL CHOOSE_THEN ASSUME_TAC)
             THEN ASM_REWRITE_TAC [MEM_APPEND;MEM]]);;

let MEM_ADJACENT_IS_INFIX = prove
  (`!x:a y xs. MEM (x,y) (ADJACENT xs)
       <=> ?ys zs. xs = APPEND ys (CONS x (CONS y zs))`,
   REPEAT GEN_TAC THEN EQ_TAC
     THENL [SPEC_TAC (`xs:a list`,`xs:a list`)
               THEN LIST_INDUCT_TAC2
               THEN REWRITE_TAC [ADJACENT_CLAUSES;MEM;EQ_SYM_EQ;APPEND_EQ_NIL 
                                ;NOT_CONS_NIL;PAIR_EQ]
               THEN STRIP_TAC
               THENL [MAP_EVERY EXISTS_TAC [`[]:a list`;`ys:a list`]
                         THEN ASM_REWRITE_TAC [APPEND]
                     ;FIRST_X_ASSUM (FIRST_X_MATCH
                                       (REPEAT_TCL CHOOSE_THEN ASSUME_TAC))
                       THEN MAP_EVERY EXISTS_TAC
                       [`CONS (x':a) ys'`;`zs:a list`]
                       THEN ASM_REWRITE_TAC [APPEND]]
           ;DISCH_THEN (REPEAT_TCL CHOOSE_THEN ASSUME_TAC)
             THEN ASM_REWRITE_TAC [MEM_APPEND;MEM]
             THEN STRUCT_CASES_TAC (ISPEC `ys:a list` list_CASES)
             THENL [ASM_REWRITE_TAC [ADJACENT_CLAUSES;APPEND;MEM]
                   ;SIMP_TAC [NOT_CONS_NIL;ADJACENT_APPEND;MEM_APPEND;MEM
                             ;ADJACENT_CLAUSES]]]);;

let ADJACENT_MIDDLE = prove
  (`!xs ys m.
      ADJACENT (APPEND xs (CONS (m:a) ys))
      = APPEND (ADJACENT (APPEND xs [m])) (ADJACENT (CONS m ys))`,
   REPEAT GEN_TAC 
   THEN STRUCT_CASES_TAC (ISPEC `xs:a list` list_CASES_APPEND)
     THEN STRUCT_CASES_TAC (ISPEC `ys:a list` list_CASES)
     THEN REWRITE_TAC [APPEND;APPEND_NIL;ADJACENT_CLAUSES]
     THEN SIMP_TAC
       [ADJACENT_APPEND;APPEND_EQ_NIL;NOT_CONS_NIL;LAST;LAST_APPEND;HD;APPEND
       ;ADJACENT_CLAUSES]
     THEN REWRITE_TAC [GSYM APPEND_ASSOC] THEN REWRITE_TAC [APPEND]);;

let MAP_FST_ADJACENT = prove
  (`!Ps. MAP FST (ADJACENT Ps) = BUTLAST Ps`,
   LIST_INDUCT_TAC2
     THEN FULL_REWRITE_TAC [ADJACENT_CLAUSES;MAP;BUTLAST;NOT_CONS_NIL]);;

let PAIRWISE_INFIX_EQ = prove
  (`!xs ws x. PAIRWISE (\x:a y. ~(x = y)) (APPEND xs (CONS x ys))
              ==> APPEND xs (CONS x ys) = APPEND ws (CONS x zs)
              ==> xs = ws /\ ys = zs`,
   LIST_INDUCT_TAC THEN REWRITE_TAC [APPEND]
     THEN GEN_TAC THEN STRUCT_CASES_TAC (ISPEC `ws:a list` list_CASES)
     THEN REWRITE_TAC [APPEND;CONS_11]
     THEN REWRITE_TAC [TAUT `p ==> q ==> r <=> q ==> p ==> r`;IMP_CONJ]
     THEN SIMP_TAC [PAIRWISE;APPEND;CONS_11;ALL;ALL_APPEND]
     THEN ASM_MESON_TAC []);;

let rotation = new_definition
  `rotation xs ys <=> ?n. xs = APPEND (DROP n ys) (TAKE n ys)`;;

let APPEND_DROP = prove
  (`!n xs ys. n <= LENGTH xs ==> APPEND (DROP n xs) ys = DROP n (APPEND xs ys)`,
   INDUCT_TAC THEN REWRITE_TAC [DROP]
     THEN LIST_INDUCT_TAC THEN REWRITE_TAC [LENGTH] THENL
     [ARITH_TAC
     ;ASM_REWRITE_TAC [DROP;APPEND;ARITH_RULE `SUC n <= SUC m <=> n <= m`]]);;

let DROP_LENGTH = prove
  (`!n xs. LENGTH xs <= n ==> DROP n xs = []`,
   INDUCT_TAC THEN (SIMP_TAC [LENGTH_EQ_NIL;DROP;ARITH_RULE `x <= 0 <=> x = 0`]
     THEN LIST_INDUCT_TAC
     THEN ASM_REWRITE_TAC [DROP;APPEND;LENGTH;LE_SUC;DROP]));;

let rotation_LENGTH_EQ = prove
  (`rotation xs ys ==> LENGTH xs = LENGTH ys`,
   REWRITE_TAC [rotation] THEN STRIP_TAC
     THEN ASM_REWRITE_TAC [LENGTH_APPEND;LENGTH_DROP;LENGTH_TAKE]
     THEN ASM_ARITH_TAC);;

let DROP_DROP = prove
  (`!n m xs:a list. DROP (n + m) xs = DROP n (DROP m xs)`,
   INDUCT_TAC THEN REWRITE_TAC [ADD_CLAUSES;DROP]
     THEN INDUCT_TAC THEN ASM_REWRITE_TAC [LENGTH;ADD_CLAUSES;DROP]
     THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC [LENGTH;ADD_CLAUSES;DROP]
     THEN REWRITE_TAC [GSYM ADD] THEN ASM_REWRITE_TAC [DROP;ADD_CLAUSES]);;

let TAKE_TAKE = prove
  (`!n m xs:a list. TAKE (n + m) xs = APPEND (TAKE n xs) (TAKE m (DROP n xs))`,
   INDUCT_TAC THEN REWRITE_TAC [TAKE;ADD_CLAUSES;APPEND;DROP]
     THEN GEN_TAC THEN STRUCT_CASES_TAC (ISPEC `m:num` num_CASES)
     THEN REWRITE_TAC [TAKE;ADD_CLAUSES;DROP;APPEND_NIL]
     THEN GEN_TAC THEN STRUCT_CASES_TAC (ISPEC `xs:a list` list_CASES)
     THEN REWRITE_TAC [TAKE;DROP;APPEND;ADD_CLAUSES;CONS_11;DROP]
     THEN REWRITE_TAC [ARITH_RULE `SUC (n + m) = n + SUC m`]
     THEN ASM_REWRITE_TAC []);;

let DROP_APPEND2 = prove
  (`!n xs ys.
      DROP n (APPEND xs ys) = APPEND (DROP n xs) (DROP (n - LENGTH xs) ys)`,
   INDUCT_TAC THEN REWRITE_TAC [DROP;ARITH_RULE `0 - x = 0`]
     THEN LIST_INDUCT_TAC
     THENL [REWRITE_TAC [ARITH_RULE `~(SUC n < 0)`;LENGTH;SUB;DROP;APPEND]
           ;ASM_REWRITE_TAC [APPEND;DROP;LENGTH;LT_SUC;SUB_SUC]]);;

let TAKE_APPEND2 = prove
  (`!n xs ys.
      TAKE n (APPEND xs ys) = APPEND (TAKE n xs) (TAKE (n - LENGTH xs) ys)`,
   INDUCT_TAC THEN REWRITE_TAC [TAKE;APPEND;ARITH_RULE `0 - x = 0`]
     THEN LIST_INDUCT_TAC
     THENL [REWRITE_TAC [ARITH_RULE `~(SUC n < 0)`;LENGTH;SUB;TAKE;APPEND]
           ;ASM_REWRITE_TAC [APPEND;TAKE;LENGTH;LT_SUC;SUB_SUC]]);;

let rot_of = new_definition
  `rot_of (xs:a list) ys
     <=> ?us vs. xs = APPEND us vs /\ ys = APPEND vs us`;;

let CONS_EQ_EXISTS_CONS = prove
  (`!h:a t xs. xs = CONS h t ==> ?ys. xs = CONS h ys`,
   REPEAT GEN_TAC
     THEN STRUCT_CASES_TAC (ISPEC `t:a list` list_CASES) THEN DISCH_TAC
     THENL [EXISTS_TAC `[]:a list` THEN ASM_REWRITE_TAC []
           ;EXISTS_TAC `CONS (h':a) t'` THEN ASM_REWRITE_TAC []]);;

let APPEND_lemma = prove
  (`!as:a list bs xs ys. APPEND as bs = APPEND xs ys /\ LENGTH as <= LENGTH xs
       ==> ?es. APPEND as bs = APPEND as (APPEND es ys)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC [APPEND;LENGTH]
    THENL [MESON_TAC [];ALL_TAC] THEN REPEAT GEN_TAC
    THEN STRUCT_CASES_TAC (ISPEC `xs:a list` list_CASES)
    THENL [ASM_REWRITE_TAC [LENGTH;ARITH_RULE `~(SUC x <= 0)`];ALL_TAC]
    THEN REWRITE_TAC [APPEND;CONS_11;LENGTH;SUC_INJ;LE_SUC]
    THEN REWRITE_TAC [IMP_CONJ] THEN DISCH_THEN (K ALL_TAC)
    THEN REWRITE_TAC [IMP_IMP]
    THEN POP_ASSUM (fun thm -> DISCH_THEN (CHOOSE_TAC o MATCH_MP thm))
    THEN ASM_MESON_TAC []);;

let rotate_trans_lemma = theorem
  "!as bs cs ds. LENGTH (bs:a list) <= LENGTH cs
    ==> xs = APPEND as bs /\ ys = APPEND bs as /\ ys = APPEND cs ds /\ zs = APPEND ds cs
    ==> ?es fs. xs = APPEND es fs /\ zs = APPEND fs es"
  [fix ["as:a list";"bs:a list";"cs:a list";"ds:a list"]
  ;assume "LENGTH (bs:a list) <= LENGTH cs" at [0]
  ;assume "xs = APPEND as bs /\ ys = APPEND bs as" at [1]
  ;assume "APPEND bs as = APPEND cs ds /\ zs = APPEND ds cs" at [2]
  ;so consider ["es:a list"] st
     "APPEND bs as = APPEND bs (APPEND es ds)"
     by [APPEND_lemma] from [0;1;2] at [3]
  ;take ["es";"APPEND ds bs"]
  ;hence "as = APPEND es ds" by [APPEND_EQ] at [4]
  ;have "cs = APPEND bs es"
     by [APPEND_ASSOC;APPEND_EQ_2] from [2;3]
  ;qed using REWRITE_TAC by [APPEND_ASSOC] from [4]];;

let rot_of_refl = prove
  (`!xs:a list. rot_of xs xs`,
   REWRITE_TAC [rot_of] THEN GEN_TAC
     THEN EXISTS_TAC `[]:a list`
     THEN REWRITE_TAC [APPEND;APPEND_NIL]
     THEN MESON_TAC []);;

let rot_of_sym = prove
  (`!xs:a list ys. rot_of xs ys <=> rot_of ys xs`,
   REWRITE_TAC [rot_of] THEN MESON_TAC []);;

let rot_trans = prove
  (`rot_of (xs:a list) ys /\ rot_of ys zs ==> rot_of xs zs`,
   REWRITE_TAC [rot_of] THEN STRIP_TAC
     THEN DISJ_CASES_TAC
     (SPECL [`LENGTH (vs:a list)`;`LENGTH (us':a list)`] LE_CASES)
     THEN ASM_MESON_TAC [rotate_trans_lemma]);;
