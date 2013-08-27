(* Counting of function applications. *)

module Discovery_count(Di : DISCOVERY) =
struct
  let count               = ref 0
  let max_count           = ref 1000
  let callback            = ref (fun () -> ())
  let register_callback f = callback := f
  let set_max_count n     = max_count := n
    
  let call_count () = !count
  let incr_count () =
    incr count;
    if !count > !max_count then
      begin
        count := 0;
        !callback ()
      end

  let bind xs f = Di.bind xs (fun x -> incr_count (); f x)

  let ap fs xs = Di.lift2 (fun f x -> incr_count (); f x) fs xs

  let lift1 f          = ap (Di.return f)
  let lift2 f xs ys    = ap (Di.lift1 f xs) ys
  let lift3 f xs ys zs = ap (Di.lift2 f xs ys) zs

  let apt fs xs = Di.apt (Di.lift1 (fun f -> incr_count (); f) fs) xs

  let lift1t f xs       = apt (Di.return f)
  let lift2t f xs ys    = apt (Di.lift1t f xs) ys
  let lift3t f xs ys zs = apt (Di.lift2t f xs ys) zs
end
