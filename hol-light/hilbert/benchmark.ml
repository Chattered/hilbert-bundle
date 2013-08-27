let try_accept = MAP_EVERY (fun thm -> TRY (ACCEPT_TAC thm));;

h ("!A B C D. between A B C /\ between B C D ==> between A C D");;
f (fix ["A:point";"B:point";"C:point";"D:point"]);;
f (assume "between A B C /\ between B C D" at 0);;
f (consider ["E:point"] st
     "~(?a. on_line A a /\ on_line B a /\ on_line E a)"
     from [0] by [g21;triangle]);;
f (obviously by_neqs
     (consider ["Fa:point"] st "between C E Fa" at 1 by [g22]));;
f (consider ["G:point"] st
     ("(?a. on_line B a /\ on_line Fa a /\ on_line G a) /\ between A G E")
     at 2 proof
     [obviously Pasch.by_pasch
         (consider ["G:point"] st
            ("(?a. on_line B a /\ on_line Fa a /\ on_line G a)" ^
                "/\ (between A G E \/ between C G E)") from [0]
            using try_accept)
     ;obviously one_eq (qed by [g21;g23] from [1])]);;
f (have "between B G Fa" at 3 proof
        [obviously Pasch.by_pasch
            (consider ["G':point"] st
               ("(?a. on_line A a /\ on_line E a /\ on_line G' a)" ^
                   "/\ (between B G' C \/ between B G' Fa)") from [1]
               using try_accept)
        ;obviously two_eqs (qed by [g21;g23] from [0])]);;

let bench d n =
  let t = Sys.time () in
  Ll.iter (fun thm ->
    Printf.printf "%s: %s\n%!"
      (string_of_float (Sys.time () -. t))
      (string_of_term (concl thm)))
    (Ll.concat (Id.to_thms (Ll.take n d)));; 
