open Parsing;;
open Lexing;;

open Lambda;;
open Parser;;
open Lexer;;

let find_fin s =
  let len = String.length s in
  let rec aux i =
    if i + 1 >= len then
      None
    else if s.[i] = ';' && s.[i + 1] = ';' then
      Some i
    else
      aux (i + 1)
  in
  aux 0
;;

let read_command () =
  let buf = Buffer.create 256 in
  let rec loop is_first =
    if is_first then print_string ">> ";
    flush stdout;
    try
      let line = read_line () in
      if not is_first then Buffer.add_char buf '\n';
      match find_fin line with
        | Some idx ->
            Buffer.add_substring buf line 0 idx;
            Buffer.add_string buf ";;";
            Buffer.contents buf
        | None ->
            Buffer.add_string buf line;
            loop false
    with
      End_of_file ->
        raise End_of_file
  in
  loop true
;;

let top_level_loop () =
  print_endline "Evaluator of lambda expressions...";
  let rec loop ctx =
    try
      let input = read_command () in
      let c = s token (from_string input) in
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
