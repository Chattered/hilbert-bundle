(* ========================================================================= *)
(*            "Mizar Light" by Freek Wiedijk.                                *)
(*                                                                           *)
(*        http://www.cs.ru.nl/~freek/mizar/miz.pdf                           *)
(* ========================================================================= *)

(* Tried to add an "induction" primitive, but it doesn't really work :( *)

exception Innergoal of goal;;

(* ------------------------------------------------------------------------- *)
(* Set up more infix operators.                                              *)
(* ------------------------------------------------------------------------- *)

Topdirs.dir_directory (!hol_dir);;

Topdirs.load_file Format.std_formatter
 (Filename.concat (!hol_dir) "hilbert/pa_f.cmo");;

List.iter (fun s -> Hashtbl.add (Pa_j_phil.ht) s true)
 ["st'";"st";"at";"from";"by";"parts";"using";"proof";"THEN'"];;

loads "hilbert/miz2a_p.ml";;
