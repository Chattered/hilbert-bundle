(* ========================================================================= *)
(* Trees and a tree stream where tags are terms created from disjunctions.   *)
(*                                                                           *)
(*                                   Phil Scott                              *)
(*                                                                           *)
(*               Centre for Intelligent Systems and their Applications       *)
(*                             University of Edinburgh                       *)
(* ========================================================================= *)

module Termtree =
struct
  module Tree = Tagtree.Make(struct
    type t = term
    let cmp = (=)
    let print t = Printf.printf "%s%!"
      (string_of_term t)
  end)
  
  open Ll
    
  module Treem = Monad.MakeLazyPlus(Tree)
  include Tree
  
  (* Pulls disjuncts lazily from a theorem. *)
  let disjs thm =
    let rec djs tm =
      lazy (if is_disj tm then
          let (d,ds) = dest_disj tm in
          Cons (d, djs ds)
        else Cons (tm, nil))
    in djs (concl thm)

  (* Create a tree from disjunctive theorems. *)
  let disjuncts thm =
    if is_disj (concl thm) then
      (Treem.lift1
         (fun tm -> ASSUME tm)
         (Tree.branch (disjs thm)))
    else Tree.return thm
      
end

module Treestream : (sig
  include DISCOVERY
  val collapse  : 'a m -> 'a m
  val with_tags : 'a m -> (term list * 'a) m
  val discharge : thm m -> thm m
  val disjuncts : thm -> thm m
  val split     : thm m -> thm m
  val to_forced : thm m -> thm m
end) =
struct
  module Stream = Monad.MakeStreamC(Termtree)
  module Sm = Monad.Make(Stream)
  module Tm = Monad.MakeLazyPlus(Termtree)
    
  (* A stream of discovered generations with their tags. *)
  let with_tags xs = Ll.map Termtree.with_tags xs

  let collapse xs = Ll.map Termtree.collapse xs

  let discharge xs =
    collapse (Sm.lift1 (fun (terms,thm) -> rev_itlist DISCH terms thm)
                (with_tags xs))

  module Di = Discovery(struct
      include Stream

      let to_list xs =
        Ll.map (Ll.map snd o Termtree.to_list) (with_tags xs)

      (* A lazy list of discovered theorems, discharging case-splitting
         assumptions. *)
      let to_thms xs = to_list (discharge xs)
  end)

  module Dim = Monad.MakeLazyPlus(Di)

  include Di

  let disjuncts thm = Ll.singleton (Termtree.disjuncts thm)
      
  let split =
    conjuncts o C Dim.bind disjuncts o Dim.lift1 (CONV_RULE DNF_CONV)

  let to_forced xs =
    Ll.singleton (Ll.fold_left Tm.plus (Termtree.zero ())
                    (Ll.map Termtree.to_forced xs))
end
