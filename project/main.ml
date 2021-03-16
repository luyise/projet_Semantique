(*
  Cours "Sémantique et Application à la Vérification de programmes"

  Antoine Miné 2015
  Marc Chevalier 2018
  Ecole normale supérieure, Paris, France / CNRS / INRIA
*)

(*
  Simple driver: parses the file given as argument and prints it back.

  You should modify this file to call your functions instead!
*)


(* parse filename *)
let doit filename =
  let prog = File_parser.parse_file filename in
  let cfg = Tree_to_cfg.prog prog in
  Printf.printf "\n graphe de flot de controle (avec un éventuel rajout d'arc vers la fonction main) ";
  let cfg1 = (Iterator.add_arc_to_main cfg) in
  Printf.printf "%a" Cfg_printer.print_cfg cfg1;          (*Sans l'arc rajouté : cfg; *)
  Cfg_printer.output_dot "cfg.dot" cfg1;           
  let module Iterator = Iterator.MakeIterator(Domain.Concrete) in       
  Iterator.iterate_cfg (Format.std_formatter) cfg1

(* parses arguments to get filename *)
let main () =
  match Array.to_list Sys.argv with
  | _::filename::_ -> doit filename
  | _ -> invalid_arg "no source file specified"

let _ = main ()