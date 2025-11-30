type ty =
    TyBool
  | TyNat
  | TyArr of ty * ty
  | TyString
  | TyList of ty
  | TyTuple of ty list 
  | TyRecord of (string * ty) list
  | TyVariant of (string * ty) list
;;


type term =
    TmTrue
  | TmFalse
  | TmIf of term * term * term
  | TmZero
  | TmSucc of term
  | TmPred of term
  | TmIsZero of term
  | TmVar of string
  | TmAbs of string * ty * term
  | TmApp of term * term
  | TmLetIn of string * term * term
  | TmFix of term (* RECUSIVIDAD *)
  | TmString of string
  | TmConcat of term * term 
  | TmTuple of term list
  | TmRecord of (string * term) list
  | TmProj of term * int
  | TmRProj of term * string
  | TmNil of ty
  | TmCons of term * term
  | TmIsNil of term
  | TmHead of term
  | TmTail of term
  | TmVariant of string * term * ty
  | TmCase of term * (string * string * term) list
;;

(* COMMAND *)
type command =
    Eval of term
  | Bind of string * ty * term
  | Quit
;;

(* BINDING *)
type binding =
    TyBind of ty
  | TyTmBind of ty * term
;;

type context =
  (string * binding) list
;;


val emptyctx : context;;
val addtbinding : context -> string -> ty -> context;;
val addvbinding : context -> string -> ty -> term -> context;;
val gettbinding : context -> string -> ty;;
val getvbinding : context -> string -> term;;

val string_of_ty : ty -> string;;
exception Type_error of string;;
val typeof : context -> term -> ty;;

val string_of_term : term -> string;;
exception NoRuleApplies;;
val eval : context -> term -> term;;

val execute : context -> command -> context;;