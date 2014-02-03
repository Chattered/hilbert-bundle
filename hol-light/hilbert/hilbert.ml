#use "topfind";;
#thread;;
#require "batteries";;
#require "monadlib";;
#require "oUnit";;

loads "hilbert/modules.ml";;
loads "hilbert/lib/lib.ml";;
loads "hilbert/lib/sets.ml";;

loads "IsabelleLight/support.ml";;
loads "IsabelleLight/new_tactics.ml";;

loads "hilbert/tactics.ml";;

loads "hilbert/discovery_base.ml";;
loads "hilbert/term_tree.ml";;

loads "hilbert/network.ml";;
loads "hilbert/concurrent.ml";;

loads "hilbert/make_mizar.ml";;

loads "hilbert/group1_axioms.ml";;
loads "hilbert/incidence_meta.ml";;
loads "hilbert/incidence_discovery_meta.ml";;
loads "hilbert/group1.ml";;

loads "hilbert/group2_axioms.ml";;
loads "hilbert/pasch.ml";;
loads "hilbert/incidence_discovery_extra.ml";;

loads "hilbert/group2_345.ml";;
loads "hilbert/infinity.ml";;
loads "hilbert/nums-derived.ml";;
loads "recursion.ml";;  (* Tools for primitive recursion on inductive types  *)
loads "arith.ml";;      (* Natural number arithmetic                         *)
loads "wf.ml";;         (* Theory of wellfounded relations                   *)
loads "calc_num.ml";;   (* Calculation with natural numbers                  *)
loads "normalizer.ml";; (* Polynomial normalizer for rings and semirings     *)
loads "grobner.ml";;    (* Groebner basis procedure for most semirings.      *)
loads "ind_types.ml";;  (* Tools for defining inductive types                *)
loads "lists.ml";;      (* Theory of lists                                   *)
loads "realax.ml";;     (* Definition of real numbers                        *)
loads "calc_int.ml";;   (* Calculation with integer-valued reals             *)
loads "realarith.ml";;  (* Universal linear real decision procedure          *)
loads "real.ml";;       (* Derived properties of reals                       *)
loads "calc_rat.ml";;   (* Calculation with rational-valued reals            *)
loads "int.ml";;        (* Definition of integers                            *)
loads "sets.ml";;       (* Basic set theory.                                 *)
loads "iterate.ml";;    (* Iterated operations                               *)
loads "cart.ml";;       (* Finite Cartesian products                         *)
loads "define.ml";;     (* Support for general recursive definitions         *)

(* ------------------------------------------------------------------------- *)
(* The help system.                                                          *)
(* ------------------------------------------------------------------------- *)

(* loads "help.ml";;       (\* Online help using the entries in Help directory   *\) *)
(* loads "database.ml";;   (\* List of name-theorem pairs for search system      *\) *)

loads "hilbert/arith_tactics.ml";;
(* Redefine "cases" for Mizar light *)
loads "hilbert/miz2a_p.ml";;

loads "hilbert/sets.ml";;
loads "hilbert/order.ml";;
loads "hilbert/halfplanes.ml";;
loads "hilbert/rays.ml";;
loads "hilbert/lists.ml";;
loads "hilbert/polygon.ml";;
