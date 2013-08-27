let unset = unset_jrh_lexer;;

(* Simple local connection, returning an out-channel. *)
let connect_to port =
  let fd = Unix.socket Unix.PF_INET6 Unix.SOCK_STREAM 0 in
  Unix.connect fd (Unix.ADDR_INET (Unix.inet6_addr_loopback, port));
  BatUnix.output_of_descr fd

let write_lazy_list output xs =
  Ll.iter (fun x -> BatIO.write_line output x; BatIO.flush output) xs

let set = set_jrh_lexer;;
