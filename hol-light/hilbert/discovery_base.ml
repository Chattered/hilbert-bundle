(* ========================================================================= *)
(* General discovery library based on a stream.                              *)
(*                                                                           *)
(*                                   Phil Scott                              *)
(*                                                                           *)
(*               Centre for Intelligent Systems and their Applications       *)
(*                             University of Edinburgh                       *)
(* ========================================================================= *)

module type DISCOVERY  =
sig
  include Monad.StreamC
  val rewrite : thm list -> thm m -> thm m
  val pure_rewrite : thm list -> thm m -> thm m
  val subst : thm m -> thm m -> thm m
  val contr : thm m -> thm m -> thm m
  val (<*>) : ('a -> 'b) m -> 'a m -> 'b m
  val (<**>) : ('a -> 'b) m -> 'a m -> 'b m
  val lift1t : ('a -> 'b) -> 'a m -> 'b m
  val lift2t : ('a -> 'b -> 'c) -> 'a m -> 'b m -> 'c m
  val lift3t : ('a -> 'b -> 'c -> 'd) -> 'a m -> 'b m -> 'c m -> 'd m
  val mp : thm m -> thm m -> thm m
  val rule1 : thm -> thm m -> thm m
  val rule2 : thm -> thm m -> thm m -> thm m
  val rule3 : thm -> thm m -> thm m -> thm m -> thm m
  val rule4 : thm -> thm m -> thm m -> thm m -> thm m -> thm m
  val chain : thm m -> thm m -> thm m
  val term_cmp : thm -> thm -> bool
  val conjuncts : thm m -> thm m
  val to_list : 'a m -> 'a LazyList.t LazyList.t
  val to_thms : thm m -> thm LazyList.t LazyList.t
  val to_eager : int -> 'a m -> 'a list
  val to_eager_thms : int -> thm m -> thm list
end

(* Discovery of theorems is parameterised on arbitrary streams, with
   a custom version of the applicative interface. *)
module Discovery(Stream : sig
  include Monad.StreamC
  val to_list : 'a m -> 'a LazyList.t LazyList.t
  val to_thms : thm m -> thm LazyList.t LazyList.t
  val (<*>) : ('a -> 'b) m -> 'a m -> 'b m
end) :
sig
  include DISCOVERY with type 'a t = 'a Stream.t
end =
struct
  open Ll

  include Stream
  module Mo = Monad.MakeLazyPlus(Stream)
  module Ap = Applicative.Make(Stream)

  let (<**>) fs xs =
    Mo.join (Ap.lift2 
               (fun f x -> 
                 try
                   return (f x)
                 with _ -> zero ()) fs xs)
    
  let lift1t f xs = Ap.return f <**> xs

  let lift2t f xs ys = lift1t f xs <**> ys

  let lift3t f xs ys zs = lift2t f xs ys <**> zs

  let conjuncts xs =
    let rec conjuncts thm =
      lazy (if is_conj (concl thm) then
          next (conjuncts (CONJUNCT1 thm) ^@^ conjuncts (CONJUNCT2 thm))
        else Cons (thm, nil)) in
    Mo.lsum (Mo.lift1 conjuncts xs)

  let rewrite rls = Mo.lift1 (REWRITE_RULE rls)
  let pure_rewrite rls = Mo.lift1 (PURE_REWRITE_RULE rls)

  let subst eqs thms =
    let f eq thm =
      let thm' =
        let x,y = dest_eq (concl eq) in
        if term_order x y then
          PURE_ONCE_REWRITE_RULE [eq] thm
        else PURE_ONCE_REWRITE_RULE [SYM eq] thm in
      if thm = thm' then failwith "subst" else thm' in
    lift2t f eqs thms

  let contr d1 d2 =
    Mo.filter (fun thm -> concl thm = `F`)
      (Ap.lift2 (fun thm -> REWRITE_RULE [thm]) d1 d2)

  (* We use Stream.plus rather than plus because the type is more general,
     though they are the same function. *)
  let merge_all xs = end_itlist Mo.plus xs

  let mp rls ants = lift2t MATCH_MP rls ants
  let rule1 rl ants = mp (return rl) ants
  let rule2 rl ants1 ants2 = mp (rule1 rl ants1) ants2
  let rule3 rl ants1 ants2 ants3 = mp (rule2 rl ants1 ants2) ants3
  let rule4 rl ants1 ants2 ants3 ants4 =
    mp (rule3 rl ants1 ants2 ants3) ants4

  let rec chain rls ants =
    bind rls
      (fun thm ->
        if is_imp (snd (splitlist (dest_binder "!") (concl thm))) then
          chain (lift1t (MATCH_MP thm) ants) ants
        else return thm)

  let term_cmp x y =
    let _,c = dest_eq (concl (SIMP_CONV [] (mk_imp (concl y, concl x)))) in
    c = `T`

  let to_eager n =
    Ll.to_list o Ll.concat o Ll.take n o to_list

  let to_eager_thms n =
    Ll.to_list o Ll.concat o Ll.take n o to_thms
end
