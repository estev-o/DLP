open Parsing;;
open Lexing;;

open Lambda;;
open Parser;;
open Lexer;;

let top_level_loop () =
  print_endline "Evaluator of lambda expressions...";
  let rec loop ctx =
    try
      print_string ">> ";
      flush stdout;
      let c = s token (from_string (read_line ())) in
      loop (execute ctx c)
    with
      Lexical_error ->
        print_endline "lexical error";
        loop ctx
    | Parse_error ->
        print_endline "Parse error.";
        loop ctx
    | Type_error e ->
        print_endline ("Type error: " ^ e);
        loop ctx
    | End_of_file ->
        print_endline "End of File.";
  in
    loop emptyctx
  ;;

top_level_loop ()
;;

