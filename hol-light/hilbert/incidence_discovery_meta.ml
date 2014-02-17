(* ========================================================================= *)
(* Discovery based on incidence rules represented in ML.                     *)
(* These are the discoverers which made it into the thesis.                  *)
(*                                                                           *)
(*                                   Phil Scott                              *)
(*                                                                           *)
(*               Centre for Intelligent Systems and their Applications       *)
(*                             University of Edinburgh                       *)
(* ========================================================================= *)

module Incidence_discovery(Discovery : DISCOVERY) =
struct
  open Ll
  open Incidence

  include Discovery
  module Dim = Monad.MakeLazyPlus(Discovery)
  open Dim
      
  let compare thm1 thm2 =
    if is_col thm1 && is_col thm2 then
      Set.is_subset (dest_col thm1) (dest_col thm2)
    else if is_ncol thm1 && is_ncol thm2 then
      let (a,b,c),(x,y,z) = dest_ncol thm1, dest_ncol thm2 in
      Set.is_subset [a;b;c] [x;y;z]
    else if is_plane thm1 && is_plane thm2 then
      Set.is_subset (dest_plane thm1) (dest_plane thm2)
    else concl thm1 = concl thm2

  let unique     = unique ~cmp:(fun x y -> concl x = concl y)
  let difference = difference compare
  let maxima     = maxima compare
  let nub        = nub compare

  type incidence_base =
      { cols    : thm Discovery.m
      ; ncols   : thm Discovery.m
      ; eqs     : thm Discovery.m
      ; neqs    : thm Discovery.m
      ; planes  : thm Discovery.m
      ; all     : thm Discovery.m
      }

  let next = Lazy.force
        
  (* The complete inference system *)
  let inferred b =
    let b = rewrite [CONJ_ACI] b in
    let rec cols = lazy
      (next
         (maxima
            (plus (filter is_col b)
               (lift3t colcol (delay cols) (delay cols) neqs))))

    and ncols = lazy
       (next
          (maxima
             (plus (filter is_ncol b)
                (lift3t colncolncol cols (delay ncols) neqs'))))
             
    and eqs = lazy
      (next (plus
               (filter (is_eq o concl) b)
               (maxima
                  (lsum (lift1 Ll.of_list
                           (lift3t coleq cols cols ncols))))))

    and neqs = lazy
     (next
        (maxima
           (msum [neqs'
                 ;conjuncts (rule1 ncolneq ncols)])))

    and neqs' = lazy
     (next
        (maxima
           (msum [filter is_neq b
                 ;lsum (lift1t Ll.of_list
                          (lift2t colncolneq (delay cols) (delay ncols)))])))
         
    and planes = lazy
      (next
         (maxima
            (msum
               [filter is_plane b
               ;lift2t colcolplane cols cols
               ;lift1t colplane cols
               ;lift1t ncolplane ncols
               ;lift3t planeplane (delay planes) (delay planes) ncols
               ;lift3t colplaneplane cols (delay planes) neqs]))) in
    { cols   = cols
    ; ncols  = ncols
    ; planes = planes
    ; eqs    = eqs
    ; neqs   = neqs
    ; all    = msum [cols;ncols;planes;eqs;neqs;b]
    }

end

