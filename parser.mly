
%{
  open Lambda;;
%}

%token LAMBDA
%token TRUE
%token FALSE
%token IF
%token THEN
%token ELSE
%token SUCC
%token PRED
%token ISZERO
%token LET
%token LETREC
%token IN
%token CONCAT
%token BOOL
%token NAT
%token STRING
%token QUIT
%token FIN

%token LPAREN
%token RPAREN
%token LBRACE
%token RBRACE
%token COMMA
%token DOT
%token EQ
%token COLON
%token ARROW
%token EOF

%token <int> INTV
%token <string> IDV
%token <string> STRINGV

%start s
%type <Lambda.command> s //antes era <Lambda.term>

%%

s :
    command FIN EOF
        { $1 }

command :
    IDV COLON ty EQ term
        { Bind ($1, $3, $5) }
  | term
        { Eval $1 }
  | QUIT
        { Quit }

term :
    appTerm
      { $1 }
  | IF term THEN term ELSE term
      { TmIf ($2, $4, $6) }
  | LAMBDA IDV COLON ty DOT term
      { TmAbs ($2, $4, $6) }
  | LET IDV EQ term IN term
      { TmLetIn ($2, $4, $6) }

appTerm :
    atomicTerm
      { $1 }
  | SUCC atomicTerm
      { TmSucc $2 }
  | PRED atomicTerm
      { TmPred $2 }
  | ISZERO atomicTerm
      { TmIsZero $2 }
  | CONCAT atomicTerm atomicTerm
      { TmConcat ($2, $3) }
  | appTerm atomicTerm
      { TmApp ($1, $2) }
      
  | LETREC IDV COLON ty EQ term IN term
      { TmLetIn ($2, TmFix (TmAbs ($2, $4, $6)), $8) }  
  
  | appTerm DOT INTV
      { TmProj ($1, $3)}

atomicTerm :
    LPAREN term RPAREN
      { $2 }
  | LBRACE term_list RBRACE
      { TmTuple $2 }
  | TRUE
      { TmTrue }
  | FALSE
      { TmFalse }
  | IDV
      { TmVar $1 }
  | INTV
      { let rec f = function
            0 -> TmZero
          | n -> TmSucc (f (n-1))
        in f $1 }
  | STRINGV
      { TmString $1 }

term_list :
    term
      { [$1] }
  | term_list COMMA term
      { $1 @ [$3] }

ty :
    atomicTy
      { $1 }
  | atomicTy ARROW ty
      { TyArr ($1, $3) }
  | LBRACE ty_list RBRACE
      { TyTuple $2 }

ty_list :
    ty
      { [$1] }
  | ty_list COMMA ty
      { $1 @ [$3] }

atomicTy :
    LPAREN ty RPAREN
      { $2 }
  | BOOL
      { TyBool }
  | NAT
      { TyNat }
  | STRING
      { TyString }
