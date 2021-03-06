(* ========================================================================= *)
(* ========================================================================= *)
(* Miz3 interface for tactics proof, allowing readable formal proofs,        *)
(* improving on miz3 mainly by allowing intelligent use of REWRITE_TAC.      *)
(*                                                                           *)
(*                (c) Copyright, Bill Richter 2013                           *)
(*          Distributed under the same license as HOL Light                  *)
(*                                                                           *)
(* We use ideas for readable formal proofs due to John Harrison ("Towards    *)
(* more readable proofs" of the tutorial and Examples/mizar.ml), Freek       *)
(* Wiedijk (Mizarlight/miz2a.ml, miz3/miz3.ml and arxiv.org/pdf/1201.3601    *)
(* "A Synthesis of Procedural and Declarative Styles of Interactive          *)
(* Theorem Proving"), Marco Maggesi (author of tactic constructs             *)
(* INTRO_TAC, DESTRUCT_TAC & HYP), Petros Papapanagiotou (coauthor of        *)
(* Isabelle Light) and Vincent Aravantinos (author of the Q-module           *)
(* https://github.com/aravantv/HOL-Light-Q).  An interactive mode is         *)
(* useful in debugging proofs.  The semantics is obvious, as there is a      *)
(* simple translation to HOL Light tactics proofs.  Many math characters     *)
(* (e.g. ⇒, ⇔, ∧, ∨, ¬, ∀, ∃, and ∅) are allowed as in HOL4 and Isabelle. *)
(*                                                                           *)
(* The construct "case_split" reducing the goal to various cases, each given *)
(* by a "suppose" clause.  The construct "proof" [...] "qed" allows          *)
(* arbitrarily long proofs, which can be arbitrarily nested with other       *)
(* case_split and proof/qed constructs.  THENL is not implemented, except    *)
(* implicitly in case_split, to encourage readable proof, but it would be    *)
(* easy to implement.  The lack of THENL requires adjustments, such as using *)
(* MATCH_MP_TAC num_INDUCTION instead of INDUCT_TAC.                         *)
(*                                                                           *)
(* The Str library defines regexp functions used here to process strings.    *)
(* John Harrison's HOL_BY improves on MESON_TAC for instantiation.           *)

#load "str.cma";;

needs "Examples/holby.ml";;
let hol_by = CONV_TAC o HOL_BY;;

(* parse_qproof uses system.ml quotexpander feature designed for miz3.ml to  *)
(* turn backquoted expression `;[...]` into a string with no newline or      *)
(* backslash problems.  This miz3 emulation readable.ml can not be used      *)
(* simultaneously with miz3, which defines parse_qproof differently.         *)

let parse_qproof s = (String.sub s 1 (String.length s - 1));;

(* exec_thm, taken from miz3.ml, maps a string to its theorem, and defines   *)
(* the predicate is_thm which tests if a string represents a theorem.        *)

let exec_phrase b s =
  let lexbuf = Lexing.from_string s in
  let ok = Toploop.execute_phrase b Format.std_formatter
    (!Toploop.parse_toplevel_phrase lexbuf) in
  Format.pp_print_flush Format.std_formatter ();
  (ok,
   let i = lexbuf.Lexing.lex_curr_pos in
   String.sub lexbuf.Lexing.lex_buffer
     i (lexbuf.Lexing.lex_buffer_len - i));;

let exec_thm_out = ref TRUTH;;

let exec_thm s =
  try
    let ok,rst = exec_phrase false
      ("exec_thm_out := (("^s^") : thm);;") in
    if not ok or rst <> "" then raise Noparse;
    !exec_thm_out
  with _ -> raise Noparse;;

let exec_thmlist_tactic_out = ref REWRITE_TAC;;

let exec_thmlist_tactic s =
  try
    let ok,rst = exec_phrase false
      ("exec_thmlist_tactic_out := (("^s^") : thm list -> tactic);;") in
    if not ok or rst <> "" then raise Noparse;
    !exec_thmlist_tactic_out
  with _ -> raise Noparse;;

let exec_thmtactic_out = ref MATCH_MP_TAC;;

let exec_thmtactic s =
  try
    let ok,rst = exec_phrase false
      ("exec_thmtactic_out := (("^s^") : thm -> tactic);;") in
    if not ok or rst <> "" then raise Noparse;
    !exec_thmtactic_out
  with _ -> raise Noparse;;

let exec_tactic_out = ref ALL_TAC;;

let exec_tactic s =
  try
    let ok,rst = exec_phrase false
      ("exec_tactic_out := (("^s^") : tactic);;") in
    if not ok or rst <> "" then raise Noparse;
    !exec_tactic_out
  with _ -> raise Noparse;;

let is_thm s =
  try let thm = exec_thm s in true
  with _ -> false;;

let is_tactic s =
  try let tactic = exec_tactic s in true
  with _ -> false;;

let is_thmtactic s =
  try let ttac = exec_thmtactic s in true
  with _ -> false;;

let is_thmlist_tactic s =
  try let thmlist_tactic = exec_thmlist_tactic s in true
  with _ -> false;;

(* make_env and parse_env_string, following Mizarlight/miz2a.ml and Vince    *)
(* Aravantinos's https://github.com/aravantv/HOL-Light-Q, turn a string to a *)
(* term with types inferred by the goal and assumption list.                 *)

let (make_env: goal -> (string * pretype) list) =
  fun (asl,w) -> map ((fun (s,ty) -> s,pretype_of_type ty) o dest_var)
                   (freesl (w::(map (concl o snd) asl)));;

let parse_env_string env s = (term_of_preterm o retypecheck env)
  ((fst o parse_preterm o lex o explode) s);;

let (subgoal_THEN: string -> thm_tactic -> tactic) =
  fun stm ttac gl ->
    let t = parse_env_string (make_env gl) stm in
    SUBGOAL_THEN t ttac gl;;

let subgoal_TAC s stm prf gl =
  let t = parse_env_string (make_env gl) stm in
  SUBGOAL_TAC s t [prf] gl;;

let (exists_TAC: string -> tactic) =
  fun stm gl -> let env = make_env gl in
    EXISTS_TAC (parse_env_string env stm) gl;;

let (X_gen_TAC: string -> tactic) =
  fun svar (asl,w as gl) ->
    let vartype = (snd o dest_var o fst o dest_forall) w in
    X_GEN_TAC (mk_var (svar,vartype)) gl;;

let assume lab notalpha tac (asl,w as gl) =
  let t = parse_env_string (make_env gl) notalpha in
  let notalpha_implies_beta = mk_imp(t, mk_conj(t, w)) in
  (SUBGOAL_THEN notalpha_implies_beta (LABEL_TAC lab) THENL
  [INTRO_TAC lab; tac] THEN
  HYP REWRITE_TAC lab [MESON[] `!x y. ~x ==> (~x /\ (x \/ y) <=> y)`]) gl;;

let raa lab st tac = subgoal_THEN (st ^ " ==> F") (LABEL_TAC lab) THENL
  [INTRO_TAC lab; tac];;

let case_split sDestruct sDisjlist tac =
  let rec list_mk_string_disj = function
      [] -> ""
    | s::[] -> "(" ^ s ^ ")"
    | s::ls -> "(" ^ s ^ ") \\/ " ^ list_mk_string_disj ls in
  subgoal_TAC "" (list_mk_string_disj sDisjlist) tac THEN
  FIRST_X_ASSUM (DESTRUCT_TAC sDestruct);;

(* Basically from the HOL Light tutorial "Towards more readable proofs."     *)

let arithmetic = ARITH_TAC;;
let set_RULE = CONV_TAC SET_RULE;;
let real_RING = CONV_TAC REAL_RING;;
let fol = MESON_TAC;;
let TACtoThmTactic tac = fun  ths -> MAP_EVERY MP_TAC ths THEN tac;;
let NUM_RING_thmTAC = TACtoThmTactic (CONV_TAC NUM_RING);;
let ARITH_thmTAC = TACtoThmTactic ARITH_TAC;;
let REAL_ARITH_thmTAC = TACtoThmTactic REAL_ARITH_TAC;;
let set = TACtoThmTactic set_RULE;;
let so = fun tac -> FIRST_ASSUM MP_TAC THEN tac;;

(* Allows HOL4 and Isabelle style math characters, via parse_qproof.         *)

let CleanMathFontsForHOL_Light s =
  let rec clean s loStringPairs =
    match loStringPairs with
      [] -> s
    | (hd :: tl) ->
      let symbol = fst hd and ascii = snd hd in
        let s = Str.global_replace (Str.regexp symbol) ascii s in
        clean s tl in
  clean s ["⇒","==>"; "⇔","<=>"; "∧","/\\ "; "∨","\\/"; "¬","~";
    "∀","!"; "∃","?"; "∈","IN"; "∉","NOTIN";
    "α","alpha"; "β","beta"; "γ","gamma"; "λ","\\ "; "θ","theta"; "μ","mu";
    "⊂","SUBSET"; "∩","INTER"; "∪","UNION"; "∅","{}"; "━","DELETE";
    "≡", "==="; "≅", "cong"; "∡", "angle"; "∥","parallel"];;

(* Regexp functions using the Str library.                                   *)
(*                                                                           *)
(* FindMatch sleft sright s                                                  *)
(* makes regexps of strings sleft sright,searches recursively in string      *)
(* s for matched pairs of substrings matching sleft and sright, and          *)
(* returns the position after the first substring matched by sright          *)
(* which is not matched by an sleft-matching substring.                      *)
(*                                                                           *)
(* FindMatch is used by FindSemicolon to find the position after the next    *)
(* "miz3" semicolon, skipping list semicolons which can occur in terms.      *)
(* FindMatch is used by processByProof, which finds substrings of the sort   *)
(* "proof" body "qed;"                                                       *)
(* in a substring s that begins after the "proof", skipping over             *)
(* "proof" ... "qed;" substrings that occur in body.                         *)
(* FindMatch is used by FindCases to take a string                           *)
(* "suppose" proof_1 "end;" ... "suppose" proof_n "end;"                     *)
(* and return the list [proof_1; proof_2; ... ; proof_n].                    *)

let ws = "[ \t\n]+";;
let ws0 = "[ \t\n]*";;

let StringRegexpEqual r s = Str.string_match r s 0 &&
  s = Str.matched_string s;;

let rec FindMatch sleft sright s =
  let test = Str.regexp ("\("^ sleft ^"\|"^ sright ^"\)") and
  left = (Str.regexp sleft) in
  let rec FindMatchPosition s count =
    if count = 1 then 0 else
      try
        let start = Str.search_forward test s 0 in
        let endpos = Str.match_end() in
        let rest = Str.string_after s endpos and
        increment =
          if StringRegexpEqual left (Str.matched_group 1 s) then -1 else 1 in
        endpos + (FindMatchPosition rest (count + increment))
      with Not_found -> failwith("no matching right bracket operator "^ sright ^" to left bracket operator "^ sleft ^" in "^ s) in
  FindMatchPosition s 0;;

let rec FindSemicolon s =
  try
    let rec FindMatchPosition s pos =
      let start = Str.search_forward (Str.regexp ";\|\[") s pos  in
      if Str.matched_string s = ";" then start
      else
        let rest = Str.string_after s (start + 1) in
        let MatchingSquareBrace = FindMatch "\[" "\]" rest in
        let newpos = start + 1 + MatchingSquareBrace in
        FindMatchPosition s newpos in
    FindMatchPosition s 0
  with Not_found -> failwith ("no final semicolon in " ^ s);;

let processByProof ByProof s =
  let sleftProof = ws^ "proof" ^ws and
  srightProof = ";" ^ws^ "qed" ^ws0^ ";" in
  if ByProof = "by"
  then
    let pos = FindSemicolon s in
    let step = Str.string_before s pos and
    rest = Str.string_after s (Str.match_end()) in
    (step ^ " ;"),rest
  else
  (* the next if clause allows the skeleton proof "proof qed;" *)
  if Str.string_match (Str.regexp (ws0^ "qed" ^ws0^ ";")) s 0
  then
    "",(Str.string_after s (Str.match_end()))
  else
    let pos_after_qed = FindMatch sleftProof srightProof s in
    let pos = Str.search_backward (Str.regexp srightProof)
      s pos_after_qed in
    let body = (Str.string_before s pos) ^ " ; " and
    rest = Str.string_after s pos_after_qed in
    body,rest;;

let rec FindCases s =
  let sleftCase = ws^ "suppose" ^ws and
  srightCase = ws^ "end" ^ws0^ ";" in
  if Str.string_match (Str.regexp sleftCase) s 0
  then
    let case_end_rest = Str.string_after s (Str.match_end()) in
    let pos_after_end = FindMatch sleftCase srightCase case_end_rest in
    let pos = Str.search_backward (Str.regexp srightCase)
      case_end_rest pos_after_end in
    let case = Str.string_before case_end_rest pos and
    rest = Str.string_after case_end_rest pos_after_end in
      case :: (FindCases rest)
  else [];;

(* StringToTactic uses regexp functions from the Str library to transform a  *)
(* string into a tactic.  The allowable tactics can be written in BNF form   *)
(* as                                                                        *)
(* Tactic := ALL_TAC | Tactic THEN Tactic |                                  *)
(*   one-word-tactic (e.g. ARITH_TAC) |                                      *)
(*   one-word-thm_tactic one-word-thm (e.g. MATCH_MP_TAC num_WF) |           *)
(*   one-word-thmlist_tactic listof(thm | label | - | --) |                  *)
(*   intro_TAC string | exists_TAC string | X_gen_TAC term |                 *)
(*   case_split string listof(statement) Tactic THENL listof(Tactic) |       *)
(*   consider listof(variable) such that statement [label] Tactic |          *)
(*   raa label statement Tactic | assume label statement Tactic |            *)
(*   subgoal_TAC label statement Tactic                                      *)
(*                                                                           *)
(* The allowable string proofs which StringToTactic transforms into tactics  *)
(* can be written in BNF form as                                             *)
(*                                                                           *)
(* OneStepProof := one-word-tactic ";" (e.g. "ARITH_TAC;") |                 *)
(*   one-word-thm_tactic one-word-thm ";" (e.g. "MATCH_MP_TAC num_WF;") |    *)
(*   one-word-thmlist_tactic concatenationof(thm | label | - | --) ";" |     *)
(*   "intro_TAC" string ";" | "exists_TAC" term ";" | "X_gen_TAC" var ";"    *)
(*                                                                           *)
(* ByProofQed := "by" OneStepProof | "proof" Proof Proof ...  Proof "qed;"   *)
(*                                                                           *)
(* Proof := "" | OneStepProof | Proof Proof |                                *)
(*   "consider" variable-list "such that" term [label] ByProofQed |          *)
(*   "raa" statement [label] ByProofQed |                                    *)
(*   "assume" statement [label] ByProofQed | statement [label] ByProofQed |  *)
(*   "case_split" destruct ByProofQed                                        *)
(*   "suppose" statement ";" Proof "end;" ...                                *)
(*   "suppose" statement ";" Proof "end;"                                    *)
(*                                                                           *)
(* Case_split reduces the goal to various cases.  In the case_split          *)
(* above, ByProofQed is a proof of the disjunction of the statements, and    *)
(* each Proof solves the goal with its statement added as an assumption.     *)
(* The string destruct lab1 | lab2 | ... has the syntax of DESTRUCT_TAC,     *)
(* so lab1 is the label of the first statement in the first case, etc.       *)
(* The unidentified lower-case words above, e.g. term and statement, are     *)
(* strings.  The label of consider and intro_TAC must also be be nonempty.   *)
(* raa x [l] ByProofQed;                                                     *)
(* is a proof by contradiction (reductio ad absurdum).  ByProofQed proves    *)
(* the goal using the added assumption ~x.  There is a new subgoal F (false) *)
(* which has the added assumption x, also labeled l, which must be nonempty. *)
(* If - is used by ByProofQed, it will refer to ~x, also labeled l.          *)
(* assume x [l] ByProofQed;                                                  *)
(* turns a disjunction goal into a implication with discharged antecedent.   *)
(* ByProofQed is a proof that the goal is equivalent to a disjunction        *)
(* x \/ y, for some statement y.  The label l must nonempty.  Then the goal  *)
(* becomes y, with x an assumption labeled l.                                *)
(* statement [label] ByProofQed;                                             *)
(* is the workhorse of declarative proofs, based on subgoal_TAC: a statement *)
(* with a label and a proof ByProofQed.  Use [] if statement is never used   *)
(* except in the next line, where it can be referred to as - or --.          *)
(* thmlist->tactic ListofLabel-Theorem--;                                    *)
(* is a tactic constructed by a thmlist->tactic, e.g. MESON_TAC (written as  *)
(* fol) followed by a space-separated list of labels, theorems and - or --,  *)
(* which both refer to the previous statement, constructed by HYP.  If --    *)
(* occurs, the previous statement is used by so (using FIRST_ASSUM).  If -   *)
(* occurs, the previous statement is used the way that HYP uses theorems.    *)
(*                                                                           *)
(* Detected errors which result in a failure and an error message:           *)
(* 1) Square braces  [...] must be matched.                                  *)
(* 2) "proof" must be matched  by "qed;", or more precisely,                 *)
(* ws^ "proof" ^ws must be matched  by ";" ^ws^ "qed;",                      *)
(* where ws means nonempty whitespace, except in the  skeleton proof         *)
(* "proof" ws "qed;"                                                         *)
(* 3) In a case_split environment,                                           *)
(* ws^ "suppose" ^ws must be matched by ws^ "end;".                          *)
(* 4) Each step in a proof must end with ";".                                *)
(* 5) A proof must match the BNF for Proof.                                  *)

let rec StringToTactic s =
  if StringRegexpEqual (Str.regexp ws0) s
  then ALL_TAC
  else
  if Str.string_match (Str.regexp (ws^ "case_split" ^ws^ "\([^;]+\)" ^ws^
    "\(by\|proof\)" ^ws)) s 0
  then
    let sDestruct = (Str.matched_group  1 s) and
    proof,rest = processByProof (Str.matched_group 2 s)
      (Str.string_after s (Str.group_end 2)) in
    let list2Case = map (fun case -> Str.bounded_split (Str.regexp ";") case 2)
      (FindCases rest) in
    let listofDisj = map hd list2Case and
    listofTac = map (hd o tl) list2Case in
    (case_split sDestruct listofDisj (StringToTactic proof))
      THENL (map StringToTactic listofTac)
  else
    let pos = FindSemicolon s in
    let step = Str.string_before s pos and
    rest = Str.string_after s (Str.match_end()) in
    let tactic,rest =
      if StringRegexpEqual (Str.regexp (ws0^ "\([^ \t\n]+\)" ^ws0)) step &&
        is_tactic (Str.matched_group 1 step)
      then
        exec_tactic (Str.matched_group 1 step), rest
      else
      if StringRegexpEqual (Str.regexp
        (ws0^ "\([^][ \t\n]+\)" ^ws0^ "\([^][ \t\n]+\)" ^ws0)) step &&
        is_thmtactic (Str.matched_group 1 step) &&
        is_thm (Str.matched_group 2 step)
      then
        let ttac = (Str.matched_group 1 step) and
        thm = (Str.matched_group 2 step) in
        (exec_thmtactic ttac) (exec_thm thm), rest
      else
      if StringRegexpEqual (Str.regexp (ws0^ "\([^ \t\n]+\)\(" ^ws0^ "[^[]*"
        ^ws0^ "\)" ^ws0)) step &&
        is_thmlist_tactic (Str.matched_group 1 step)
      then
        let ttac = exec_thmlist_tactic (Str.matched_group 1 step) and
        LabThmList = Str.split (Str.regexp ws) (Str.matched_group 2 step) in
        let thms = filter is_thm LabThmList and
        labs0 = String.concat " " (filter (not o is_thm) LabThmList) in
        let labs = " "^ labs0 ^" " and
        listofThms = map exec_thm thms in
        if Str.string_match (Str.regexp ("[^-]*" ^ws^ "-" ^ws)) labs 0
        then
          let labs = Str.global_replace (Str.regexp (ws^ "-")) "" labs in
          (fun (asl,w as gl) ->
             (HYP ttac labs ((snd (hd asl)) :: listofThms)) gl), rest
        else if Str.string_match (Str.regexp ("[^-]*" ^ws^ "--" ^ws)) labs 0
        then
          let labs = Str.global_replace (Str.regexp (ws^ "--")) "" labs in
          so (HYP ttac labs listofThms), rest
        else HYP ttac labs listofThms, rest
      else
      if Str.string_match (Str.regexp (ws0^ "intro_TAC" ^ws)) step 0
      then
        let intro_string = (Str.global_replace (Str.regexp ",") ";"
          (Str.string_after step (Str.match_end()))) in
        INTRO_TAC intro_string, rest
      else
      if Str.string_match (Str.regexp (ws0^ "exists_TAC" ^ws)) step 0
      then
        let exists_string = Str.string_after step (Str.match_end()) in
        exists_TAC exists_string, rest
      else
      if Str.string_match (Str.regexp (ws0^ "X_gen_TAC" ^ws)) step 0
      then
        let gen_string = Str.string_after step (Str.match_end()) in
        X_gen_TAC gen_string, rest
      else
      if Str.string_match (Str.regexp (ws0^ "consider" ^ws^ "\(\(.\|\n\)+\)"
        ^ws^"such" ^ws^ "that" ^ws^ "\(\(.\|\n\)+\)" ^ws^ "\[\(\(.\|\n\)*\)\]"
        ^ws^ "\(by\|proof\)" ^ws)) step 0
      then
        let vars = Str.matched_group 1 step and
        t = Str.matched_group 3 step and
        lab = Str.matched_group 5 step and
        proof,rest = processByProof (Str.matched_group 7 step)
          (Str.string_after s (Str.group_end 7)) in
        (subgoal_THEN ("?" ^ vars ^ ". " ^ t)
        (DESTRUCT_TAC ("@" ^ vars ^ "." ^ lab)) THENL
        [StringToTactic proof; ALL_TAC]), rest
      else
        try
          let start = Str.search_forward (Str.regexp
          (ws^ "\[\([^]]*\)\]" ^ws^ "\(by\|proof\)" ^ws)) step 0 in
          let statement = Str.string_before step start and
          lab = Str.matched_group 1 step and
          proof,rest = processByProof (Str.matched_group 2 step)
            (Str.string_after s (Str.group_end 2)) in
          if Str.string_match (Str.regexp (ws0^ "\(raa\|assume\)" ^ws))
            statement 0
          then
            let statement = Str.string_after statement (Str.match_end()) in
            if Str.matched_group 1 step = "raa" then
              raa lab statement (StringToTactic proof), rest
            else
              assume lab statement (StringToTactic proof), rest
          else
            subgoal_TAC lab statement (StringToTactic proof), rest
        with Not_found -> failwith("can't parse "^ step) in
      tactic THEN StringToTactic rest;;

let theorem s =
  let s = CleanMathFontsForHOL_Light s in
  try
    let start = Str.search_forward (Str.regexp
      (ws ^ "proof" ^ws^ "\(\(.\|\n\)*\)" ^ws ^ "qed" ^ws0^ ";" ^ws0)) s 0 in
    let thm = Str.string_before s start and
    proof = Str.matched_group 1 s in
    prove (parse_env_string [] thm,   StringToTactic proof)
  with Not_found -> failwith("missing initial \"proof\" or final \"qed;\" in "^ s);;

let interactive_proof s =
  let proof = CleanMathFontsForHOL_Light s in
  e (StringToTactic proof);;

let interactive_goal s =
  let thm = CleanMathFontsForHOL_Light s in
  g (parse_env_string [] thm);;

let AXIOM_OF_CHOICE = theorem `;
  ∀P. (∀x. ∃y. P x y) ⇒ ∃f. ∀x. P x (f x)

  proof
    intro_TAC ∀P, H1;
    exists_TAC λx. @y. P x y;
    fol H1;
  qed;
`;;

let NSQRT_2 = theorem `;
  ∀p q. p * p = 2 * q * q  ⇒  q = 0

  proof
    MATCH_MP_TAC num_WF;
    intro_TAC ∀p, A, ∀q, B;
    EVEN(p * p) ⇔ EVEN(2 * q * q)     [] by fol B;
    EVEN(p)     [] by fol - ARITH EVEN_MULT;
    consider m such that p = 2 * m     [C] by fol - EVEN_EXISTS;
    case_split qp | pq by arithmetic;
    suppose q < p;
      q * q = 2 * m * m ⇒ m = 0     [] by fol qp A;
      NUM_RING_thmTAC - B C;
    end;
    suppose      p <= q;
      p * p <= q * q     [] by fol - LE_MULT2;
      q * q = 0     [] by ARITH_thmTAC - B;
    NUM_RING_thmTAC -;
    end;
  qed;
`;;

(* The following interactive version of the above proof shows a feature of   *)
(* proof/qed and case_split/suppose.  You can evaluate an incomplete proof   *)
(* of a statement in an interactive_proof and complete the proof afterward,  *)
(* as indicated below.  The "suppose" clauses of a case_split can also be    *)
(* incomplete.  Do not include code below the incomplete proof or case_split *)
(* in an interactive_proof body, for the usual THEN vs THENL reason.         *)

interactive_goal `;∀p q. p * p = 2 * q * q  ⇒  q = 0
`;;
interactive_proof `;
    MATCH_MP_TAC num_WF;
    intro_TAC ∀p, A, ∀q, B;
    EVEN(p * p) ⇔ EVEN(2 * q * q)     [] proof  qed;
`;;
interactive_proof `;
      fol B;
`;;
interactive_proof `;
    EVEN(p)     [] by fol - ARITH EVEN_MULT;
    consider m such that p = 2 * m     [C] proof fol - EVEN_EXISTS; qed;
`;;
interactive_proof `;
    case_split qp | pq by arithmetic;
    suppose q < p;
    end;
    suppose      p <= q;
    end;
`;;
interactive_proof `;
      q * q = 2 * m * m ⇒ m = 0     [] by fol qp A;
      NUM_RING_thmTAC - B C;
`;;
interactive_proof `;
      p * p <= q * q     [] by fol - LE_MULT2;
      q * q = 0     [] by ARITH_thmTAC - B;
      NUM_RING_thmTAC -;
`;;
let NSQRT_2 = top_thm();;
