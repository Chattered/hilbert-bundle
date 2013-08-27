(** Set theoretic functions on strictly-ordered lists.

    @author Phil Scott
*)

module Set =
struct
  let of_list xs = Bl.sort 
  
  let rec mem x = function
      []      -> false
    | y :: ys when x = y -> true
    | y :: ys when y < x -> mem x ys 
    | _ -> false
        
  let rec (insert : ?cmp:('a -> 'a -> int) -> 'a -> 'a list -> 'a list) =
    fun ?(cmp=compare) x xs ->
      match xs with
          []    -> [x]
        | y::ys ->
          if cmp x y < 0 then x :: y :: ys
          else if cmp x y = 0 then y :: ys
          else y :: (insert x ys)          
          
  let rec (intersect : ?cmp:('a -> 'a -> int) -> 'a list -> 'a list -> 'a list) =
    fun ?(cmp=compare) lst1 lst2 ->
      match lst1, lst2 with
	  [], _ -> []
        | _, [] -> []
        | (x :: tl1), (y :: tl2) when cmp x y = 0 -> x :: intersect ~cmp tl1 tl2
        | (x :: tl1), (y :: tl2) when cmp x y < 0 -> intersect ~cmp tl1 lst2
        | (x :: tl1), (y :: tl2) -> intersect ~cmp lst1 tl2

  let rec (is_subset : ?cmp:('a -> 'a -> int) -> 'a list -> 'a list -> bool) =
    fun ?(cmp=compare) lst1 lst2 ->
      match lst1, lst2 with
	  [], _ -> true
        | _, [] -> false
        | (x :: tl1), (y :: tl2) when cmp x y > 0 -> is_subset ~cmp lst1 tl2 
        | (x :: tl1), (y :: tl2) when cmp x y = 0 -> is_subset ~cmp tl1 tl2
        | (x :: tl1), (y :: tl2) -> false

  let rec (difference :?cmp:('a -> 'a -> int) ->  'a list -> 'a list -> 'a list) =
    fun ?(cmp=compare) lst1 lst2 ->
      match lst1, lst2 with
	  [], _ -> []
        | _, [] -> lst1
        | (x :: tl1), (y :: tl2) when cmp x y = 0 -> difference ~cmp tl1 tl2
        | (x :: tl1), (y :: tl2) when cmp x y < 0 -> x :: difference ~cmp tl1 lst2
        | (x :: tl1), (y :: tl2) -> difference lst1 tl2

  let rec (union : ?cmp:('a -> 'a -> int) -> 'a list -> 'a list -> 'a list) =
    fun ?(cmp=compare) lst1 lst2 ->
      match lst1, lst2 with
	  [], _ -> lst2
        | _, [] -> lst1
        | (x :: tl1), (y :: tl2) when cmp x y = 0 -> x :: (union ~cmp tl1 tl2)
        | (x :: tl1), (y :: tl2) when cmp x y < 0 -> x :: (union ~cmp tl1 lst2)
        | (x :: tl1), (y :: tl2) -> y :: (union ~cmp lst1 tl2)

end
