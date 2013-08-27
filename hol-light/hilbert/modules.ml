(* Rebindings of module names. See issues about CamelCase.  *)

module Bl = BatList;;
module Bl = BatList;;
module Bp = BatPrintf;;
module Bio = BatIO;;
module Tagtree = TagTree;;

module Ll =
struct
  include LazyList
  let frm xs = from xs
end;;
