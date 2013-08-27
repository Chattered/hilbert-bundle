(* Customising the stream monad with HOL Light theorem discovery. *)

module Termset = 
struct
  include BatSet.Make(struct 
                        type t = term
                        let compare = compare
                      end)
  let zero ()  = empty
  let plus s t = union s t
end

(* A tree monad whose branches are labelled with terms *)  
module Termtree =
struct
  module T = Tagtree.Base(struct
                            type t = term
                            let cmp = (=)
                            let print t = Printf.printf "%s%!"
                              (string_of_term t)
                          end)
  include T
 module Monad = (Monad.MakeLazyPlus(T) : Monad.LazyPlus
                 with type 'a m = 'a T.m)
end

module Discovery =
  (struct
     open Ll

     module Bl =
     struct
       include List
       include BatList
     end

     module Stream = Monad.StreamC(Termtree)

     type 'a m = 'a Lazy.t Termtree.m LazyList.t

     (* Stream functions *)
     let null  	      = Stream.null
     let lplus 	      = Stream.lplus
     let plus  	      = Stream.plus
     let zero  	      = Stream.zero
     let bind  xs f   = Stream.bind xs (fun x -> f (Lazy.force x))
     let (>>=)        = bind
     let join xs      = Stream.join (Stream.lift1 Lazy.force xs)
     let sequence xs  = 
       Stream.lift1 (fun x -> lazy x) (Stream.sequence (Bl.map (Stream.lift1 Lazy.force) xs))
     let transpose xs = 
       Ll.map (Stream.lift1 (fun x -> lazy x)) 
	 (Stream.transpose (Stream.lift1 Lazy.force xs))

     let cmp_on p x y =
       p (Lazy.force x) (Lazy.force y)

     let difference p =
       Stream.difference (cmp_on p)
	 
     let maxima p = Stream.maxima (cmp_on p)
       
     let unique p = Stream.unique (cmp_on p)

     let sum xs = Stream.lift1 (fun x -> lazy x) (Stream.sum (Stream.lift1 Lazy.force xs))

     (* The extra laziness is needed through this wrapper because of
	issues described in tagtree.mli. *)
     let return x = Stream.return (lazy x)

     let ap fs xs =
       Stream.lift2 Monad.Lazy.ap fs xs

     let lift1 f = ap (return f)
	 
     let filter p xss =
       sum (lift1 (fun x -> if p x then singleton x else nil) xss)

     let lift2 f xs ys =
       ap (lift1 f xs) ys

     let lift3 f xs ys zs =
       ap (lift2 f xs ys) zs

     let apt fs xs =
       sum (Stream.lift2 
	      (fun f x -> 
		lazy
		  (try
		     singleton ((Lazy.force f) (Lazy.force x))
		   with _ -> nil)) fs xs)

     let lift1t f xs =
       apt (return f) xs
	 
     let lift2t f xs ys =
       apt (lift1t f xs) ys
	 
     let lift3t f xs ys zs =
       apt (lift2t f xs ys) zs

     (* General utility functions. *)
     let rec take_to p xs =
       lazy (match next xs with
               Nil                  -> Nil
             | Cons (x,xs) when p x -> Cons (x,nil)
             | Cons (x,xs)          -> Cons (x,take_to p xs))
       
     let conjuncts xs =
       let rec conjuncts thm =
           lazy (if is_conj (concl thm) then
               next (conjuncts (CONJUNCT1 thm) ^@^ conjuncts (CONJUNCT2 thm))
             else Cons (thm, nil)) in
       sum (lift1 conjuncts xs)

     (* Non-deterministic match MP with enumerated sets *)
     (* Permute one set of values around another set, preserving their
        respective orderings. *)
     let permute_around xs ys =
       let rec p m xs ys =
         let insert x n p = take n xs ^@^ singleton x ^@^ p in
         let pm n ys = p (m - n) (drop n xs) ys in
	   lazy
             (match next xs with
		  Nil -> Cons (ys, nil)
                | _ -> match next ys with
        	      Nil -> Cons (xs, nil)
		    | Cons (y, ys) ->
        	        next (concat_map
        		        (fun n -> map (insert y n) (pm n ys))
        		        (range 0 m)))
       in p (length xs) xs ys

     let cons x xs = x :: xs

     let find_paths p tm =
       let rec f tm =
         if p tm then [[]] else
	   if is_abs tm then Bl.map (cons "b") (f (body tm))
	   else if is_comb tm then
             Bl.map (cons "l") (f (rator tm))
             @ Bl.map (cons "r") (f (rand tm))
	   else []
       in Bl.map implode (f tm)

     let rec find_terms p tm =
       if p tm then [tm] else
         if is_abs tm then find_terms p (body tm)
         else if is_comb tm then
	   find_terms p (rator tm) @ find_terms p (rand tm)
         else []

     let subst_path p tm1 tm2 =
       let rec s p tm =
         match p with
             [] -> tm2
	   | "l"::t -> mk_comb (s t (rator tm), rand tm)
	   | "r"::t -> mk_comb (rator tm, s t (rand tm))
	   | "b"::t -> mk_abs (bndvar tm, s t (body tm))
	   | _ -> raise (Failure "Invalid path.")
       in s (explode p) tm1
	    
     let rec bounds tm =
       match tm with
	   Var (_,_) -> []
         | Const (_,_) -> []
         | Comb(s,t) -> bounds s @ bounds t
         | Abs(x,t) -> x :: bounds t

     let rec map_try f xs =
       concat_map (fun x -> try singleton (f x) with _ -> nil) xs

     (* let reorder_tm bvs (subterm, path) = *)
     (*   let vs = dest_setenum subterm in *)
     (*   let mk_set xs = mk_setenum (xs, type_of (Bl.hd vs)) in *)
     (*   let bvs, vs   = Bl.partition (C Bl.mem bvs) vs in *)
     (*   let conv s tm = *)
     (*     let s' = subst_path path tm s in *)
     (*       SYM (PATH_CONV path (PURE_REWRITE_CONV [INSERT_COMM]) s') *)
     (*   in *)
     (*     map_try (conv o mk_set o Ll.to_list) (permute_around (Ll.of_list bvs)  *)
     (*    					 (Ll.of_list vs)) *)

     (* (\* Convert an implication into several, such that matches against the *)
     (*    results correspond to non-deterministic matches based on *)
     (*    commutative/associative rewriting of finite sets *\) *)
     (* let nd_rule thm = *)
     (*   let vs, body = strip_forall (concl thm) in *)
     (*   let nvs = Bl.map (variant (bounds body)) vs in *)
     (*   let tm = subst (Bl.combine nvs vs) body in *)
     (*   let rec reorderings ant thm' = function *)
     (*       [] -> singleton thm' *)
     (*     | ((t,p)::ps) -> *)
     (*         concat_map (fun c -> *)
     (*    		   reorderings ant *)
     (*                         (EQ_MP (ONCE_DEPTH_CONV *)
     (*                                   (LAND_CONV c) (concl thm')) *)
     (*                            (CONV_RULE (ONCE_DEPTH_CONV *)
     (*                                          (LAND_CONV *)
     (*                                             (PURE_REWRITE_CONV *)
     (*    					    [INSERT_COMM]))) thm')) *)
     (*                         ps) *)
     (*           (reorder_tm nvs (t,p)) *)
     (*   in *)
     (*     try *)
     (*       let ant,concl = (dest_imp o snd o strip_forall) tm in *)
     (*         reorderings ant thm *)
     (*           (Bl.combine (find_terms is_setenum ant) *)
     (*    	  (find_paths is_setenum ant)) *)
     (*     with _ -> nil *)

     let rewrite rls = lift1 (REWRITE_RULE rls)
     let pure_rewrite rls = lift1 (PURE_REWRITE_RULE rls)

     let contr d1 d2 =
       filter (fun thm -> concl thm = `F`)
         (lift2 (fun thm -> REWRITE_RULE [thm]) d1 d2)

     (* We use Stream.plus rather than plus because the type is more general,
        though they are the same function. *)
     let merge_all xs = end_itlist Stream.plus xs

     let mp rls ants = lift2t MATCH_MP rls ants
     let rule1 rl ants = mp (return rl) ants
     let rule2 rl ants1 ants2 = mp (rule1 rl ants1) ants2
     let rule3 rl ants1 ants2 ants3 = mp (rule2 rl ants1 ants2) ants3

     let rec chain rls ants =
       bind rls
         (fun thm -> if is_imp (concl thm) then
             mp (lift1t (MATCH_MP thm) ants) ants
           else return thm)
       
     (* Pulls disjuncts lazily from a theorem *)
     let disjs thm =
       let rec djs tm =
         lazy (if is_disj tm then
                 let (d,ds) = dest_disj tm in
                   Cons (d, djs ds)
               else Cons (tm, nil))
       in djs (concl thm)

     (* Branch a discovery on its disjunctive theorems. *)
     let disjuncts d =
       Stream.lift1 (fun x -> lazy x)
	 (Stream.bind d
            (fun thm ->
              if is_disj (concl (Lazy.force thm)) then
		Stream.lift1 ASSUME
                  (singleton
                     (Termtree.branch (disjs (Lazy.force thm))))
              else Stream.return (Lazy.force thm)))

     (* Discover the hypotheses of the top goal on demand. *)
     let monitor () =
       let hyps = Bl.concat (Bl.map (CONJUNCTS o snd) (fst (top_realgoal ())))
       in unique (=)
       (Ll.frm
          (fun () ->
	    try
              end_itlist Termtree.Monad.plus
                (Bl.map (fun x -> Termtree.return (lazy x)) hyps)
            with _ -> Termtree.zero ()))
               
     let goal_hyps () = Bl.map (concl o snd) (fst (top_realgoal ()))

     let disch_disjs thm =
       itlist DISCH (Bl.filter (not o C Bl.mem (goal_hyps ())) (hyp thm)) thm;;
     
     (* A lazy list of discovered values with their tags and dependencies. *)
     let chain_to_list chain =
       let tree_to_pairs tree =
         if Termtree.null tree then nil else
           let to_pair (terms, x) =
             terms, Lazy.force x
           in map to_pair (Termtree.collapse tree)
       in concat_map (fun t -> Printf.printf ";%!"; tree_to_pairs t) chain

     (* A lazy list of discovered theorems with their dependencies.
        All assumptions which are not in the hypotheses are discharged,
        including case-splitting assumptions. *)
     let to_thms chain =
       map (fun terms,thm ->
              rev_itlist DISCH (Ll.to_list terms) thm)
         (chain_to_list chain)

     let is_val x =
       try
         Lazy.lazy_is_val x
       with _ -> false

     (* Retrieve as much of a lazy list as has been forced to far. *)         
     let rec get_forced xs =
       if is_val xs then
         try
           match next xs with
               Cons (x,xs) -> lazy (Cons (x,get_forced xs))
             | Nil -> nil
         with _ -> nil
       else nil

     let rec to_excp xs =
       lazy (try
               match Ll.next xs with
                   Nil        -> Nil
                 | Cons(x,xs) -> Cons (x, to_excp xs)
        with _ -> Nil)

     (* Discover all values that have been forced, or until an exception is
        raised. *)
     let to_forced xs =
       to_excp (get_forced xs)

     (* Discover a list of theorems and then stop. *)
     let find_all terms chain =
       let rec f termset thms =
         if Termset.is_empty termset then nil else
           lazy (match next thms with
                     Nil -> Nil
                   | Cons (thm,thms) ->
                       if Termset.mem (concl thm) termset then
                         Cons (thm, f (Termset.remove (concl thm) termset) thms)
                       else next (f termset thms))
       in let termset = itlist Termset.add terms Termset.empty
       in Ll.to_list (f termset (to_thms chain))

     let delay xs = Stream.delay xs

     let find_count n xs =
       let f c t =
         let c' = c + Termtree.count t in
         c', (c', t) in
       map snd (take_to (fun (c,_) -> c >= n) (map_accum_l f 0 xs))

     let to_list = chain_to_list
     let of_list xs = merge_all (Bl.map return xs)
      
   end :
    sig
      include Monad.LazyPlus
    with type 'a m = 'a Lazy.t Termtree.m LazyList.t
      val delay : 'a m -> 'a m
      val merge_all : 'a m list -> 'a m
      val of_list : 'a list -> 'a m
      val rewrite : thm list -> thm m -> thm m
      val pure_rewrite : thm list -> thm m -> thm m
      val filter : ('a -> bool) -> 'a m -> 'a m
      val contr : thm m -> thm m -> thm m
      val sum : 'a LazyList.t m -> 'a m
      val sum : 'a LazyList.t m -> 'a m
      val maxima : ('a -> 'a -> bool) -> 'a m -> 'a m
      val difference : ('a -> 'a -> bool) -> 'a m -> 'a m -> 'a m
      val unique : ('a -> 'a -> bool) -> 'a m -> 'a m
      val lift1t : ('a -> 'b) -> 'a m -> 'b m
      val lift2t : ('a -> 'b -> 'c) -> 'a m -> 'b m -> 'c m
      val lift3t : ('a -> 'b -> 'c -> 'd) -> 'a m -> 'b m -> 'c m -> 'd m
      val mp : thm m -> thm m -> thm m
      val rule1 : thm -> thm m -> thm m
      val rule2 : thm -> thm m -> thm m -> thm m
      val rule3 : thm -> thm m -> thm m -> thm m -> thm m
      val chain : thm m -> thm m -> thm m
      val conjuncts : thm m -> thm m
      val disjuncts : thm m -> thm m
      (* val nd_rule : thm -> thm LazyList.t *)
      val monitor : unit -> thm m
      val to_list : 'a m -> (term Ll.t * 'a) Ll.t 
      val to_thms : thm m -> thm LazyList.t
      val to_forced : 'a LazyList.t -> 'a LazyList.t
      val find_all : term list -> thm m -> thm list
      val find_count : int -> 'a m -> 'a m
    end)
