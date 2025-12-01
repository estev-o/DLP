
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
%token ISNIL
%token HEAD
%token TAIL
%token CONS
%token NIL
%token LET
%token LETREC
%token IN
%token CONCAT
%token CASE
%token OF
%token BAR
%token AS
%token BOOL
%token NAT
%token STRING
%token LIST
%token QUIT
%token FIN

%token LPAREN
%token RPAREN
%token LBRACE
%token RBRACE
%token LANGLE
%token RANGLE
%token COMMA
%token DOT
%token EQ
%token COLON
%token ARROW
%token ARROW2
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
  | IDV EQ term
        { BindInfer ($1, $3) }
  | IDV EQ ty
        { TypeBind ($1, $3) }
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
  | CASE term OF branches
      { TmCase ($2, $4) }

appTerm :
    atomicTerm
      { $1 }
  | SUCC atomicTerm
      { TmSucc $2 }
  | PRED atomicTerm
      { TmPred $2 }
  | ISZERO atomicTerm
      { TmIsZero $2 }
  | ISNIL atomicTerm
      { TmIsNil $2 }
  | HEAD atomicTerm
      { TmHead $2 }
  | TAIL atomicTerm
      { TmTail $2 }
  | CONS atomicTerm atomicTerm
      { TmCons ($2, $3) }
  | CONCAT atomicTerm atomicTerm
      { TmConcat ($2, $3) }
  | appTerm atomicTerm
      { TmApp ($1, $2) }
      
  | LETREC IDV COLON ty EQ term IN term
      { TmLetIn ($2, TmFix (TmAbs ($2, $4, $6)), $8) }  
  
  | appTerm DOT INTV
      { TmProj ($1, $3)}
  | appTerm DOT IDV
      { TmRProj ($1, $3)}

term_field:
    IDV EQ term
        { ($1, $3) }

term_field_list:
    term_field
        { [$1] }
 |  term_field_list COMMA term_field
        { $1 @ [$3] }

atomicTerm :
    LPAREN term RPAREN
      { $2 }
  | LBRACE term_list RBRACE
      { TmTuple $2 }
  | LBRACE term_field_list RBRACE
      { TmRecord $2 }
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
  | NIL ty
      { TmNil $2 }
  | LANGLE IDV EQ term RANGLE AS ty
      { TmVariant ($2, $4, $7) }

term_list :
    term
      { [$1] }
  | term_list COMMA term
      { $1 @ [$3] }

ty_field :
    IDV COLON ty
        { ($1, $3) }

ty_field_list :
    ty_field
        { [$1] }
 |  ty_field_list COMMA ty_field
        { $1 @ [$3] }

ty :
    atomicTy
      { $1 }
  | atomicTy ARROW ty
      { TyArr ($1, $3) }
  | LBRACE ty_list RBRACE
      { TyTuple $2 }
  | LANGLE var_fields RANGLE
      { TyVariant $2 }
  | LBRACE ty_field_list RBRACE
      { TyRecord $2}

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
  | LIST atomicTy
      { TyList $2 }
  | IDV
      { TyVar $1 }

var_fields :
    IDV COLON ty
      { [($1, $3)] }
  | var_fields COMMA IDV COLON ty
      { $1 @ [($3, $5)] }

branches :
    branch
      { [$1] }
  | branches BAR branch
      { $1 @ [$3] }

branch :
    LANGLE IDV EQ IDV RANGLE ARROW2 term
      { ($2, $4, $7) }
