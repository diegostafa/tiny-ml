(*
* TinyML
* Typing.fs: typing algorithms
*)

module TinyML.Typing

open Ast

type subst = (tyvar * ty) list
let mutable private fresh_var_counter = 0
let type_error fmt = throw_formatted TypeError fmt

// --- FREEVARS

// in: type
// out: tv contained in t
let rec freevars_ty t =
    match t with
    | TyName _ -> Set.empty
    | TyArrow (t1, t2) -> (freevars_ty t1) + (freevars_ty t2)
    | TyVar tv -> Set.singleton tv
    | TyTuple ts -> List.fold (fun acc t -> acc + freevars_ty t) Set.empty ts

// in: scheme (forall tvs in type)
// out: freevars type  tvs
let freevars_scheme (Forall (tvs, t)) = freevars_ty t - tvs

// in: scheme environment
// out: freevars in each scheme
let freevars_scheme_env env =
    env
    |> List.unzip
    |> snd
    |> List.fold (fun fvs sch -> (fvs + freevars_scheme sch)) Set.empty


// --- \TODO SUBSTITUTION

// in: substitution, type
// out: substituted type
let rec apply_subst (s: subst) (t: ty) =
    let search_subst key s =
        List.tryFind (fun (tv, _) -> key = tv) s

    match t with
    | TyName (_) -> t
    | TyArrow (l, r) -> (apply_subst s l, apply_subst s r) |> TyArrow
    | TyTuple (ts) -> ts |> List.map (apply_subst s) |> TyTuple
    | TyVar (tv) ->
        match search_subst tv s with
        | Some v -> snd v
        | None -> t

// in: substitutions s1, s2
// out: substitution where s2 is appeied to every type of s1
let compose_subst (s1: subst) (s2: subst) =
    s1
    |> List.map (fun (tv, t) -> (tv, apply_subst s2 t))
    |> List.append s2
    |> List.distinctBy fst


// --- \TODO UNIFICATION

// in: types t1, t2
// out: substitution that unified t1 and t2
let rec unify (t1: ty) (t2: ty) =
    let rec occurs (var: tyvar) (t: ty) : bool = Set.contains var (freevars_ty t)

    match (t1, t2) with
    | TyName n, TyName m when n = m -> []
    | TyTuple (xs), TyTuple (ys) when xs.Length = ys.Length ->
        List.zip xs ys
        |> List.fold (fun s (x, y) -> compose_subst s (unify x y)) []
    | TyArrow (l1, r1), TyArrow (l2, r2) -> compose_subst (unify l1 l2) (unify r1 r2)
    | TyVar tv, t when not (occurs tv t) -> [ (tv, t) ]
    | t, TyVar tv when not (occurs tv t) -> [ (tv, t) ]

    // error cases
    | TyName _, TyName _ ->
        type_error
            "unify error: different type constructors can't be unified (t1 = %s , t2 = %s)"
            (pretty_ty t1)
            (pretty_ty t2)
    | TyTuple _, TyTuple _ ->
        type_error
            "unify error: tuples with different sizes can't be unified (t1 = %s , t2 = %s)"
            (pretty_ty t1)
            (pretty_ty t2)
    | TyVar _, _ ->
        type_error
            "unify error: t2 can't be unified if it occurs in t1 (t1 = %s , t2 = %s)"
            (pretty_ty t1)
            (pretty_ty t2)
    | _, TyVar _ ->
        type_error
            "unify error: t2 can't be unified if it occurs in t1 (t1 = %s , t2 = %s)"
            (pretty_ty t1)
            (pretty_ty t2)
    | _ ->
        type_error
            "unify error: unification is not supported with these types(t1 = %s , t2 = %s)"
            (pretty_ty t1)
            (pretty_ty t2)


// --- TYPE CHECKER

let gamma0 =
    [ ("+", TyArrow(TyInt, TyArrow(TyInt, TyInt)))
      ("-", TyArrow(TyInt, TyArrow(TyInt, TyInt))) ]

let rec typecheck_expr (env: ty env) (e: expr) : ty =
    match e with
    | Lit (LInt _) -> TyInt
    | Lit (LFloat _) -> TyFloat
    | Lit (LString _) -> TyString
    | Lit (LChar _) -> TyChar
    | Lit (LBool _) -> TyBool
    | Lit LUnit -> TyUnit

    | Var v -> env |> List.find (fun (var, _) -> var = v) |> snd

    | Lambda (_, None, _) -> unexpected_error "typecheck_expr: unannotated lambda is not supported"

    | Lambda (x, Some t1, e) ->
        let t2 = typecheck_expr ((x, t1) :: env) e
        TyArrow(t1, t2)

    | App (e1, e2) ->
        let t1 = typecheck_expr env e1
        let t2 = typecheck_expr env e2

        match t1 with
        | TyArrow (l, r) ->
            if l = t2 then
                r
            else
                type_error
                    "wrong application: argument type %s does not match function domain %s"
                    (pretty_ty t2)
                    (pretty_ty l)
        | _ -> type_error "expecting a function on left side of application, but got %s" (pretty_ty t1)

    | Let (x, tyo, e1, e2) ->
        let t1 = typecheck_expr env e1

        match tyo with
        | None -> ()
        | Some t ->
            if t <> t1 then
                type_error
                    "type annotation in let binding of %s is wrong: exptected %s, but got %s"
                    x
                    (pretty_ty t)
                    (pretty_ty t1)

        typecheck_expr ((x, t1) :: env) e2

    | IfThenElse (e1, e2, e3o) ->
        let t1 = typecheck_expr env e1

        if t1 <> TyBool then
            type_error "if condition must be a bool, but got a %s" (pretty_ty t1)

        let t2 = typecheck_expr env e2

        match e3o with
        | None ->
            if t2 <> TyUnit then
                type_error "if-then without else requires unit type on then branch, but got %s" (pretty_ty t2)

            TyUnit
        | Some e3 ->
            let t3 = typecheck_expr env e3

            if t2 <> t3 then
                type_error
                    "type mismatch in if-then-else: then branch has type %s and is different from else branch type %s"
                    (pretty_ty t2)
                    (pretty_ty t3)

            t2

    | Tuple es -> TyTuple(List.map (typecheck_expr env) es)

    | LetRec (f, None, e1, e2) -> unexpected_error "typecheck_expr: unannotated let rec is not supported"

    | LetRec (f, Some tf, e1, e2) ->
        let env0 = (f, tf) :: env
        let t1 = typecheck_expr env0 e1

        match t1 with
        | TyArrow _ -> ()
        | _ -> type_error "let rec is restricted to functions, but got type %s" (pretty_ty t1)

        if t1 <> tf then
            type_error "let rec type mismatch: expected %s, but got %s" (pretty_ty tf) (pretty_ty t1)

        typecheck_expr env0 e2

    | BinOp (e1,
             ("+"
             | "-"
             | "/"
             | "%"
             | "*" as op),
             e2) ->
        let t1 = typecheck_expr env e1
        let t2 = typecheck_expr env e2

        match t1, t2 with
        | TyInt, TyInt -> TyInt
        | TyFloat, TyFloat -> TyFloat
        | TyInt, TyFloat
        | TyFloat, TyInt -> TyFloat
        | _ -> type_error "binary operator expects two int operands, but got %s %s %s" (pretty_ty t1) op (pretty_ty t2)

    | BinOp (e1,
             ("<"
             | "<="
             | ">"
             | ">="
             | "="
             | "<>" as op),
             e2) ->
        let t1 = typecheck_expr env e1
        let t2 = typecheck_expr env e2

        match t1, t2 with
        | TyInt, TyInt -> ()
        | _ ->
            type_error "binary operator expects two numeric operands, but got %s %s %s" (pretty_ty t1) op (pretty_ty t2)

        TyBool

    | BinOp (e1,
             ("and"
             | "or" as op),
             e2) ->
        let t1 = typecheck_expr env e1
        let t2 = typecheck_expr env e2

        match t1, t2 with
        | TyBool, TyBool -> ()
        | _ ->
            type_error "binary operator expects two bools operands, but got %s %s %s" (pretty_ty t1) op (pretty_ty t2)

        TyBool

    | BinOp (_, op, _) -> unexpected_error "typecheck_expr: unsupported binary operator (%s)" op

    | UnOp ("not", e) ->
        let t = typecheck_expr env e

        if t <> TyBool then
            type_error "unary not expects a bool operand, but got %s" (pretty_ty t)

        TyBool

    | UnOp ("-", e) ->
        let t = typecheck_expr env e

        match t with
        | TyInt -> TyInt
        | TyFloat -> TyFloat
        | _ -> type_error "unary negation expects a numeric operand, but got %s" (pretty_ty t)

    | UnOp (op, _) -> unexpected_error "typecheck_expr: unsupported unary operator (%s)" op

    | _ -> unexpected_error "typecheck_expr: unsupported expression: %s [AST: %A]" (pretty_expr e) e


// --- TODO TYPE INFERENCE

// in: unit
// out: fresh type variable
let gen_fresh_var =
    fresh_var_counter <- fresh_var_counter + 1
    TyVar fresh_var_counter

let instantiate (Forall (tvs, ty)) =
    let rec refresh tvs ty =
        match ty with
        | TyName _ -> ty
        | TyVar a when not (List.contains a tvs) -> ty
        | TyVar _ -> gen_fresh_var
        | TyArrow (l, r) -> TyArrow(refresh tvs l, refresh tvs r)
        | TyTuple (ts) -> ts |> List.map (refresh tvs) |> TyTuple

    refresh (Set.toList tvs) ty

let generalize ty senv =
    let qtv = (freevars_ty ty) - (freevars_scheme_env senv)
    Forall(qtv, ty)

let gamma_scheme =
    gamma0
    |> List.fold (fun env (tv, ty) -> env @ [ (tv, generalize ty env) ]) []

let rec typeinfer_expr (senv: scheme env) (e: expr) : ty * subst =
    match e with
    | Lit (LInt _) -> TyInt, []
    | Lit (LBool _) -> TyBool, []
    | Lit (LFloat _) -> TyFloat, []
    | Lit (LString _) -> TyString, []
    | Lit (LChar _) -> TyChar, []
    | Lit LUnit -> TyUnit, []

    | Var x ->
        match List.tryFind (fun e -> fst e = x) senv with
        | Some (_, sch) -> instantiate sch, []
        | _ -> type_error "typeinfer_expr: variable %s is not defined in the environment" x


    | Let (var, ann, e1, e2) ->
        let t1, s1 = typeinfer_expr senv e1
        let tvs = freevars_ty t1 - freevars_scheme_env senv
        let sch = Forall(tvs, t1)
        let t2, s2 = typeinfer_expr ((var, sch) :: senv) e2
        t2, compose_subst s2 s1

    | _ -> failwithf "not implemented"
