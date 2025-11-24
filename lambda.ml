type ty =
    TyBool
  | TyNat
  | TyArr of ty * ty
  | TyString
  | TyTuple of ty list 
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
  | TmFix of term (* RECUSIVIDAD*)
  | TmString of string
  | TmConcat of term * term 
  | TmTuple of term list
  | TmProj of term * int
;;

type command =
    Eval of term
  | Bind of string * ty * term
  | Quit
;;
type binding =
    TyBind of ty
  | TyTmBind of ty * term
;;
type context =
  (string * binding) list
;;

(* CONTEXT MANAGEMENT *)

let emptyctx =
  []
;;

let addtbinding ctx s bind =
  (s, TyBind bind) :: ctx
;;

let addvbinding ctx s ty tm =
  (s, TyTmBind (ty, tm)) :: ctx
;;

let gettbinding ctx s =
  match List.assoc s ctx with
      TyBind ty -> ty
    | TyTmBind (ty, _) -> ty
;;

let getvbinding ctx s =
  match List.assoc s ctx with
      TyTmBind (_, tm) -> tm
    | _ -> raise Not_found
;;

(* TYPE MANAGEMENT (TYPING) *)

let rec string_of_ty ty = match ty with
    TyBool ->
      "Bool"
  | TyNat ->
      "Nat"
  | TyArr (ty1, ty2) ->
      "(" ^ string_of_ty ty1 ^ ")" ^ " -> " ^ "(" ^ string_of_ty ty2 ^ ")"
  | TyString ->
      "String"
  | TyTuple ty_list ->
      let string_of_ty_list list =
        list
        |> List.map string_of_ty
        |> String.concat ", "
      in
      "{" ^ string_of_ty_list ty_list ^ "}"
;;

exception Type_error of string
;;

let rec typeof ctx tm = match tm with
    (* T-True *)
    TmTrue ->
      TyBool

    (* T-False *)
  | TmFalse ->
      TyBool

    (* T-If *)
  | TmIf (t1, t2, t3) ->
      if typeof ctx t1 = TyBool then
        let tyT2 = typeof ctx t2 in
        if typeof ctx t3 = tyT2 then tyT2
        else raise (Type_error "arms of conditional have different types")
      else
        raise (Type_error "guard of conditional not a boolean")

    (* T-Zero *)
  | TmZero ->
      TyNat

    (* T-Succ *)
  | TmSucc t1 ->
      if typeof ctx t1 = TyNat then TyNat
      else raise (Type_error "argument of succ is not a number")

    (* T-Pred *)
  | TmPred t1 ->
      if typeof ctx t1 = TyNat then TyNat
      else raise (Type_error "argument of pred is not a number")

    (* T-Iszero *)
  | TmIsZero t1 ->
      if typeof ctx t1 = TyNat then TyBool
      else raise (Type_error "argument of iszero is not a number")

    (* T-Var *)
  | TmVar x ->
      (try gettbinding ctx x with
       _ -> raise (Type_error ("no binding type for variable " ^ x)))

    (* T-Abs *)
  | TmAbs (x, tyT1, t2) ->
      let ctx' = addtbinding ctx x tyT1 in
      let tyT2 = typeof ctx' t2 in
      TyArr (tyT1, tyT2)

    (* T-App *)
  | TmApp (t1, t2) ->
      let tyT1 = typeof ctx t1 in
      let tyT2 = typeof ctx t2 in
      (match tyT1 with
           TyArr (tyT11, tyT12) ->
             if tyT2 = tyT11 then tyT12
             else raise (Type_error "parameter type mismatch")
         | _ -> raise (Type_error "arrow type expected"))

    (* T-Let *)
  | TmLetIn (x, t1, t2) ->
      let tyT1 = typeof ctx t1 in
      let ctx' = addtbinding ctx x tyT1 in
      typeof ctx' t2

    (* T-Fix RECURSIVIDAD*) 
  | TmFix t1 ->
      let tyT1 = typeof ctx t1 in
      (match tyT1 with
           TyArr (tyT11, tyT12) ->
             if tyT11 = tyT12 then tyT12
             else raise (Type_error "result of body not compatible with domain")
         | _ -> raise (Type_error "arrow type expected"))
  | TmString _ ->
      TyString
  | TmConcat (t1, t2) ->
      if typeof ctx t1 = TyString && typeof ctx t2 = TyString then TyString
      else raise (Type_error "argument of concat is not a string")
  (* T-TUPLE *)
  | TmTuple t1 ->
      let ty_list = List.map (fun t -> typeof ctx t) t1 in
      TyTuple ty_list
  (* T-PROJ *)
  | TmProj (t, i) ->
      let ty_t = typeof ctx t in
      (match ty_t with
          TyTuple ty_list-> 
            if i > 0 && i <= List.length ty_list then
              List.nth ty_list (i - 1)
            else
              raise (Type_error "Index out of bounds")
        | _ -> raise (Type_error "Term projected is not a tuple"))

;;


(* TERMS MANAGEMENT (EVALUATION) *)

let rec nat_value = function
    TmZero -> Some 0
  | TmSucc t -> (match nat_value t with Some n -> Some (n+1) | None -> None)
  | _ -> None
;;

let rec string_of_term tm =
  let open Format in
  let prec_if = 1 and prec_abs = 1 and prec_let = 1 and prec_app = 3 and prec_proj = 4 and prec_atom = 5 in
  let rec pp_term prec fmt t =
    let needs_paren my_prec = my_prec < prec in
    let paren my_prec printer =
      let wrap = needs_paren my_prec in
      if wrap then fprintf fmt "(";
      printer ();
      if wrap then fprintf fmt ")"
    in
    match nat_value t with
    | Some n -> fprintf fmt "%d" n
    | None ->
    match t with
    | TmTrue -> fprintf fmt "true"
    | TmFalse -> fprintf fmt "false"
    | TmString s -> fprintf fmt "\"%s\"" s
    | TmVar s -> fprintf fmt "%s" s
    | TmTuple ts ->
        let rec pp_elems fmt = function
          | [] -> ()
          | [x] -> fprintf fmt "%a" (pp_term prec_atom) x
          | x :: xs -> fprintf fmt "%a, %a" (pp_term prec_atom) x pp_elems xs
        in
        fprintf fmt "{%a}" pp_elems ts
    | TmProj (t', i) ->
        paren prec_proj (fun () -> fprintf fmt "%a.%d" (pp_term prec_proj) t' i)
    | TmIf (t1, t2, t3) ->
        paren prec_if (fun () ->
          fprintf fmt "@[<v 2>if %a@ then %a@ else %a@]"
            (pp_term prec_if) t1 (pp_term prec_if) t2 (pp_term prec_if) t3)
    | TmLetIn (s, t1, t2) ->
        paren prec_let (fun () ->
          fprintf fmt "@[<v 2>let %s = %a@ in %a@]" s (pp_term prec_let) t1 (pp_term prec_let) t2)
    | TmAbs (s, tyS, t') ->
        paren prec_abs (fun () ->
          fprintf fmt "@[<2>lambda %s:%s.@ %a@]" s (string_of_ty tyS) (pp_term prec_abs) t')
    | TmApp (t1, t2) ->
        paren prec_app (fun () -> fprintf fmt "@[<2>%a@ %a@]" (pp_term prec_app) t1 (pp_term (prec_app+1)) t2)
    | TmConcat (t1, t2) ->
        paren prec_app (fun () -> fprintf fmt "@[<2>concat@ %a@ %a@]" (pp_term (prec_app+1)) t1 (pp_term (prec_app+1)) t2)
    | TmFix t' ->
        paren prec_app (fun () -> fprintf fmt "@[<2>fix@ %a@]" (pp_term (prec_app+1)) t')
    | TmSucc t' ->
        paren prec_app (fun () -> fprintf fmt "@[<2>succ@ %a@]" (pp_term (prec_app+1)) t')
    | TmPred t' ->
        paren prec_app (fun () -> fprintf fmt "@[<2>pred@ %a@]" (pp_term (prec_app+1)) t')
    | TmIsZero t' ->
        paren prec_app (fun () -> fprintf fmt "@[<2>iszero@ %a@]" (pp_term (prec_app+1)) t')
    | TmZero -> assert false
  in
  Format.asprintf "%a" (pp_term 0) tm
;;

let rec ldif l1 l2 = match l1 with
    [] -> []
  | h::t -> if List.mem h l2 then ldif t l2 else h::(ldif t l2)
;;

let rec lunion l1 l2 = match l1 with
    [] -> l2
  | h::t -> if List.mem h l2 then lunion t l2 else h::(lunion t l2)
;;

let rec free_vars tm = match tm with
    TmTrue ->
      []
  | TmFalse ->
      []
  | TmIf (t1, t2, t3) ->
      lunion (lunion (free_vars t1) (free_vars t2)) (free_vars t3)
  | TmZero ->
      []
  | TmSucc t ->
      free_vars t
  | TmPred t ->
      free_vars t
  | TmIsZero t ->
      free_vars t
  | TmVar s ->
      [s]
  | TmAbs (s, _, t) ->
      ldif (free_vars t) [s]
  | TmApp (t1, t2) ->
      lunion (free_vars t1) (free_vars t2)
  | TmLetIn (s, t1, t2) ->
      lunion (ldif (free_vars t2) [s]) (free_vars t1)
  (* RECUSIVIDAD *)
  | TmFix t ->
      free_vars t
  | TmString _ ->
      []
  | TmConcat (t1, t2) -> 
      lunion (free_vars t1) (free_vars t2)

  | TmTuple term_list -> 
      List.fold_left lunion [] (List.map free_vars term_list)

  | TmProj (t, i) ->
      free_vars t
;;

let rec fresh_name x l =
  if not (List.mem x l) then x else fresh_name (x ^ "'") l
;;

let rec subst x s tm = match tm with
    TmTrue ->
      TmTrue
  | TmFalse ->
      TmFalse
  | TmIf (t1, t2, t3) ->
      TmIf (subst x s t1, subst x s t2, subst x s t3)
  | TmZero ->
      TmZero
  | TmSucc t ->
      TmSucc (subst x s t)
  | TmPred t ->
      TmPred (subst x s t)
  | TmIsZero t ->
      TmIsZero (subst x s t)
  | TmVar y ->
      if y = x then s else tm
  | TmAbs (y, tyY, t) ->
      if y = x then tm
      else let fvs = free_vars s in
           if not (List.mem y fvs)
           then TmAbs (y, tyY, subst x s t)
           else let z = fresh_name y (free_vars t @ fvs) in
                TmAbs (z, tyY, subst x s (subst y (TmVar z) t))
  | TmApp (t1, t2) ->
      TmApp (subst x s t1, subst x s t2)
  | TmLetIn (y, t1, t2) ->
      if y = x then TmLetIn (y, subst x s t1, t2)
      else let fvs = free_vars s in
           if not (List.mem y fvs)
           then TmLetIn (y, subst x s t1, subst x s t2)
           else let z = fresh_name y (free_vars t2 @ fvs) in
                TmLetIn (z, subst x s t1, subst x s (subst y (TmVar z) t2))
  (* RECUSIVIDAD *)
  | TmFix t1 ->
      TmFix (subst x s t1)
  | TmString st ->
      TmString st
  | TmConcat (t1, t2) -> 
      TmConcat (subst x s t1, subst x s t2)

  | TmTuple term_list ->
      TmTuple (List.map (subst x s) term_list)

  | TmProj (t, i) ->
      TmProj (subst x s t, i)
;;

let rec isnumericval tm = match tm with
    TmZero -> true
  | TmSucc t -> isnumericval t
  | _ -> false
;;

let rec isval tm = match tm with
    TmTrue  -> true
  | TmFalse -> true
  | TmAbs _ -> true
  | TmString _ -> true
  | t when isnumericval t -> true
  | TmTuple term_list ->  List.for_all isval term_list
  | _ -> false
;;

exception NoRuleApplies
;;

let rec eval1 ctx tm = match tm with
    (* E-IfTrue *)
    TmIf (TmTrue, t2, _) ->
      t2

    (* E-IfFalse *)
  | TmIf (TmFalse, _, t3) ->
      t3

    (* E-If *)
  | TmIf (t1, t2, t3) ->
      let t1' = eval1 ctx t1 in
      TmIf (t1', t2, t3)

    (* E-Succ *)
  | TmSucc t1 ->
      let t1' = eval1 ctx t1 in
      TmSucc t1'

    (* E-PredZero *)
  | TmPred TmZero ->
      TmZero

    (* E-PredSucc *)
  | TmPred (TmSucc nv1) when isnumericval nv1 ->
      nv1

    (* E-Pred *)
  | TmPred t1 ->
      let t1' = eval1 ctx t1 in
      TmPred t1'

    (* E-IszeroZero *)
  | TmIsZero TmZero ->
      TmTrue

    (* E-IszeroSucc *)
  | TmIsZero (TmSucc nv1) when isnumericval nv1 ->
      TmFalse

    (* E-Iszero *)
  | TmIsZero t1 ->
      let t1' = eval1 ctx t1 in
      TmIsZero t1'

    (* E-AppAbs *)
  | TmApp (TmAbs(x, _, t12), v2) when isval v2 ->
      subst x v2 t12

    (* E-App2: evaluate argument before applying function *)
  | TmApp (v1, t2) when isval v1 ->
      let t2' = eval1 ctx t2 in
      TmApp (v1, t2')

    (* E-App1: evaluate function before argument *)
  | TmApp (t1, t2) ->
      let t1' = eval1 ctx t1 in
      TmApp (t1', t2)

    (* E-LetV *)
  | TmLetIn (x, v1, t2) when isval v1 ->
      subst x v1 t2

    (* E-Let *)
  | TmLetIn(x, t1, t2) ->
      let t1' = eval1 ctx t1 in
      TmLetIn (x, t1', t2)

    (* E-FixBeta RECURSIVIDAD *)
  | TmFix (TmAbs (x, _, t2)) ->
      subst x tm t2 
    (* E-Fix RECURSIVIDAD*)
  | TmFix t1 ->
      let t1' = eval1 ctx t1 in
      TmFix t1'

  | TmVar s ->
    getvbinding ctx s

  | TmConcat (TmString s1, TmString s2) -> 
      TmString (s1 ^ s2)
  
  | TmConcat (TmString s1, t2) ->
      let t2' = eval1 ctx t2 in
      TmConcat (TmString s1, t2')

  | TmConcat (t1, t2) ->
      let t1' = eval1 ctx t1 in
      TmConcat (t1', t2)

  (* E-ProjTuple*)
  | TmProj (TmTuple t, i) ->
      List.nth t (i-1)

  (* E-PROJ *)
  | TmProj (t, i) ->
      let t' = eval1 ctx t in
      TmProj (t', i)
  
  (* E-TUPLE *)
 | TmTuple term_list ->
      let rec aux evaluated remaining =
        match remaining with
        | [] ->
            raise NoRuleApplies
        | t :: rest_of_terms ->
            if isval t then
              aux (t :: evaluated) rest_of_terms
            else
              let t' = eval1 ctx t in 
              TmTuple ((List.rev evaluated) @ [t'] @ rest_of_terms)
      in
      aux [] term_list

  | _ ->
      raise NoRuleApplies
;;

let apply_ctx ctx tm =
  List.fold_left (fun t x -> subst x (getvbinding ctx x) t) tm (free_vars tm)
;;
let rec eval ctx tm =
  try
    let tm' = eval1 ctx tm in
    eval ctx tm'
  with
    NoRuleApplies -> tm
;;

let execute ctx = function
    Eval tm ->
      let tyTm = typeof ctx tm in
      let tm' = eval ctx tm in
      print_endline ("- : " ^ string_of_ty tyTm ^ " = " ^ string_of_term tm');
      ctx
  | Bind (s, ty, tm) ->
      let tyTm = typeof ctx tm in
      if tyTm = ty then
        let tm' = eval ctx tm in
        print_endline (s ^ " : " ^ string_of_ty tyTm ^ " = " ^ string_of_term tm');
        addvbinding ctx s tyTm tm'
      else
        raise (Type_error ("Type mismatch in binding: expected " ^ string_of_ty ty ^ " but got " ^ string_of_ty tyTm))
  | Quit ->
    raise End_of_file
