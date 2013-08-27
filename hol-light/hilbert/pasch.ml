(* ========================================================================= *)
(* Alternative rendering of Pasch in terms of collinearity.                  *)
(*                                                                           *)
(*                                   Phil Scott                              *)
(*                                                                           *)
(*               Centre for Intelligent Systems and their Applications       *)
(*                             University of Edinburgh                       *)
(* ========================================================================= *)

discovery_depth := 20;;

module Id = Incidence_discovery(Di);;
let by_eqs b = (Id.inferred b).Id.eqs;;
let by_neqs b = (Id.inferred b).Id.neqs;;

let swapbet = prove (`!A B C. between A B C <=> between C B A`, MESON_TAC [g21]);;

(* We first prove a version of Pasch in terms of the existence of three planar
   triangles -- thanks to Laura for spotting that we only need three!. *)
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
  ;hence "?Fa. on_line Fa DE /\ (between A Fa C \/ between B Fa C)"
    from [0;1;4;5;6;7;8;9] using
    (fun thms -> MESON_TAC
      [REWRITE_RULE thms
          (SPECL [`A:point`;`B:point`;`C:point`;`D:point`;`DE:line`;`'a:plane`] g24)])
  ;qed from [3;4] by [g12]];;
