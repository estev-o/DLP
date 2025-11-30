
{
  open Parser;;
  exception Lexical_error;;
}

rule token = parse
    [' ' '\t' '\n']  { token lexbuf }
  | "lambda"    { LAMBDA }
  | "L"         { LAMBDA }
  | "true"      { TRUE }
  | "false"     { FALSE }
  | "if"        { IF }
  | "then"      { THEN }
  | "else"      { ELSE }
  | "succ"      { SUCC }
  | "pred"      { PRED }
  | "iszero"    { ISZERO }
  | "isnil"     { ISNIL }
  | "head"      { HEAD }
  | "tail"      { TAIL }
  | "cons"      { CONS }
  | "nil"       { NIL }
  | "let"       { LET }  
  | "letrec"    { LETREC }  (*RECUSIVIDAD*)
  | "in"        { IN }
  | "concat"    { CONCAT }
  | "case"      { CASE }
  | "of"        { OF }
  | "as"        { AS }
  | ";;"        { FIN }
  | "Bool"      { BOOL }
  | "Nat"       { NAT }
  | "List"      { LIST }
  | "String"    { STRING }
  | "Quit"      { QUIT }
  | '('         { LPAREN }
  | ')'         { RPAREN }
  | '{'         { LBRACE }
  | '}'         { RBRACE }
  | '<'         { LANGLE }
  | '>'         { RANGLE }
  | ','         { COMMA }
  | '.'         { DOT }
  | "|"        { BAR }
  | "=>"       { ARROW2 }
  | '='         { EQ }
  | ':'         { COLON }
  | "->"        { ARROW }
  | ['0'-'9']+  { INTV (int_of_string (Lexing.lexeme lexbuf)) }
  | ['a'-'z']['a'-'z' '_' '0'-'9']*
                { IDV (Lexing.lexeme lexbuf) }
  | '"'[^ '"' ';' '\n']*'"'
                { let s = Lexing.lexeme lexbuf in
                  STRINGV (String.sub s 1 (String.length s - 2)) }
  | eof         { EOF }
  | _           { raise Lexical_error }
