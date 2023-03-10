(*
* TinyML
* Typing.fs: typing algorithms
*)

module TinyML.Typing

open Ast

type subst = (tyvar * ty) list
let private fresh_tv_counter_init = 97
let mutable private fresh_tv_counter = fresh_tv_counter_init
let type_error fmt = throw_formatted TypeError fmt


// --- FREEVARS

// in: type
// out: tv contained in t
let rec freevars_ty ty =
    match ty with
    | TyName _ -> Set.empty
    | TyArrow (t1, t2) -> (freevars_ty t1) + (freevars_ty t2)
    | TyVar tv -> Set.singleton tv
    | TyTuple ts -> List.fold (fun acc t -> acc + freevars_ty t) Set.empty ts

// in: scheme (forall tvs in type)
// out: freevars type  tvs
let freevars_scheme (Forall (tvs, ty)) = freevars_ty ty - tvs

// in: scheme environment
// out: freevars in each scheme
let freevars_scheme_env env =
    env
    |> List.unzip
    |> snd
    |> List.fold (fun fvs sch -> (fvs + freevars_scheme sch)) Set.empty


// --- \TODO: SUBSTITUTION

// in: substitution, type
// out: substituted type
let rec apply_subst s ty =
    let search_subst key s =
        List.tryFind (fun (tv, _) -> key = tv) s

    match ty with
    | TyName (_) -> ty
    | TyArrow (l, r) -> (apply_subst s l, apply_subst s r) |> TyArrow
    | TyTuple (ts) -> ts |> List.map (apply_subst s) |> TyTuple
    | TyVar (tv) ->
        match search_subst tv s with
        | Some v -> snd v
        | None -> ty

// in: substitutions s1, s2
// out: substitution where s2 is appeied to every type of s1
let compose_subst s1 s2 =
    s1
    |> List.map (fun (tv, t) -> (tv, apply_subst s2 t))
    |> List.append s2
    |> List.distinctBy fst

// in: type
// out: the same type in which every tv is normalized
let normalize_tvs ty =
    let tvs = freevars_ty ty |> Set.toList

    match tvs with
    | [] -> ty
    | _ ->
        let normalizer =
            (List.minBy
                (fun tv ->
                    match tv with
                    | n -> n)
                tvs)
            - fresh_tv_counter_init

        let final_s =
            tvs
            |> List.zip tvs
            |> List.map (fun (tv1, tv2) -> (tv1, TyVar(tv2 - normalizer)))

        apply_subst final_s ty


// --- \TODO: UNIFICATION

// in: types t1, t2
// out: substitution that unified t1 and t2
let rec unify ty1 ty2 =
    let rec occurs tv ty : bool = Set.contains tv (freevars_ty ty)

    match (ty1, ty2) with
    | TyName n, TyName m when n = m -> []
    | TyTuple (xs), TyTuple (ys) when xs.Length = ys.Length ->
        List.zip xs ys
        |> List.fold (fun s (x, y) -> compose_subst s (unify x y)) []
    | TyArrow (l1, r1), TyArrow (l2, r2) ->
        let unify_l = unify l1 l2
        let r1, r2 = apply_subst unify_l r1, apply_subst unify_l r2
        let unify_r = unify r1 r2
        compose_subst unify_l unify_r

    | TyVar tv, t
    | t, TyVar tv when not (occurs tv t) || ty1 = ty2 -> [ (tv, t) ]

    // error cases
    | TyName _, TyName _ ->
        type_error
            "unify error: different type constructors can't be unified (t1 = %s , t2 = %s)"
            (pretty_ty ty1)
            (pretty_ty ty2)
    | TyTuple _, TyTuple _ ->
        type_error
            "unify error: tuples of different sizes can't be unified (t1 = %s , t2 = %s)"
            (pretty_ty ty1)
            (pretty_ty ty2)
    | TyVar _, _ ->
        type_error
            "unify error: t2 can't be unified if it occurs in t1 (t1 = %s , t2 = %s)"
            (pretty_ty ty1)
            (pretty_ty ty2)
    | _, TyVar _ ->
        type_error
            "unify error: t2 can't be unified if it occurs in t1 (t1 = %s , t2 = %s)"
            (pretty_ty ty1)
            (pretty_ty ty2)
    | _ ->
        type_error
            "unify error: unification is not supported with these types (t1 = %s , t2 = %s)"
            (pretty_ty ty1)
            (pretty_ty ty2)


// --- TYPE CHECKER

// in: unit
// out: type environement for type checking
let gamma0: list<string * ty> =
    let gen_intf_binop op =
        [ (op, TyArrow(TyInt, TyArrow(TyInt, TyInt)))
          (op, TyArrow(TyFloat, TyArrow(TyInt, TyFloat)))
          (op, TyArrow(TyInt, TyArrow(TyFloat, TyFloat)))
          (op, TyArrow(TyFloat, TyArrow(TyFloat, TyFloat))) ]

    let gen_bool_binop op ty1 ty2 =
        [ (op, TyArrow(ty1, TyArrow(ty1, TyBool)))
          (op, TyArrow(ty2, TyArrow(ty1, TyBool)))
          (op, TyArrow(ty1, TyArrow(ty2, TyBool)))
          (op, TyArrow(ty2, TyArrow(ty2, TyBool))) ]

    [ ("not", TyArrow(TyBool, TyBool))
      ("and", TyArrow(TyBool, TyArrow(TyBool, TyBool)))
      ("or", TyArrow(TyBool, TyArrow(TyBool, TyBool))) ]

    @ gen_intf_binop "+"
      @ gen_intf_binop "-"
        @ gen_intf_binop "*"
          @ gen_intf_binop "/"
            @ gen_bool_binop "<" TyInt TyFloat
              @ gen_bool_binop ">" TyInt TyFloat
                @ gen_bool_binop "<=" TyInt TyFloat
                  @ gen_bool_binop ">=" TyInt TyFloat
                    @ gen_bool_binop "=" TyInt TyFloat
                      @ gen_bool_binop "<>" TyInt TyFloat

// in: expression, type environment
// out: type of the expression
let rec typecheck_expr env e =
    match e with
    | Lit (LInt _) -> TyInt
    | Lit (LFloat _) -> TyFloat
    | Lit (LString _) -> TyString
    | Lit (LChar _) -> TyChar
    | Lit (LBool _) -> TyBool
    | Lit LUnit -> TyUnit

    | Var v -> env |> List.find (fun (var, _) -> var = v) |> snd

    | Lambda (x, ann, e) ->
        match ann with
        | Some t ->
            let t2 = typecheck_expr ((x, t) :: env) e
            TyArrow(t, t2)
        | None -> unexpected_error "typecheck_expr: unannotated lambda is not supported"

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


// --- \TODO: TYPE INFERENCE

// in: unit
// out: fresh type variable
let gen_fresh_tv () =
    fresh_tv_counter <- fresh_tv_counter + 1
    TyVar fresh_tv_counter

// in: scheme
// out: non quntified type with refreshed type variables
let instantiate sch =
    match sch with
    | Forall (tvs, ty) ->
        let fresh_sub =
            tvs
            |> Set.map (fun tv -> (tv, gen_fresh_tv ()))
            |> Set.toList

        apply_subst fresh_sub ty

// in: type, scheme environment
// out: scheme quantifying every tv in the type not in the env
let generalize ty env =
    let quantified_tv = (freevars_ty ty) - (freevars_scheme_env env)
    Forall(quantified_tv, ty)

// in: type
// out: type scheme without quantified variables
let gen_fake_sch ty = Forall(Set.empty, ty)

// in: substitution, scheme environment
// out: a new environment in which every type has been applied to the substitution
let apply_subst_to_env s env =
    List.map (fun (key, (Forall (tvs, ty))) -> (key, (Forall(tvs, apply_subst s ty)))) env

// in: unit
// out: scheme environement for type inference
let s_gamma0: list<string * scheme> =
    List.fold (fun env (tv, ty) -> env @ [ (tv, generalize ty env) ]) [] gamma0

// in: operation code, a type
// out: empty list if the type is not a supported operator, some list otherwise
let unify_check op_name expected_op_ty =
    let subs =
        gamma0
        |> List.filter (fun g -> fst g = op_name)
        |> List.map snd
        |> List.map (fun x ->
            try
                Some(unify x expected_op_ty)
            with
            | _ -> None)
        |> List.choose (fun x -> x)
        |> List.tryHead

    match subs with
    | Some s -> List.tryHead s
    | None -> unexpected_error "unify_check: couldn't unify %A with %A" (op_name) (pretty_ty expected_op_ty)

// in: expression, scheme environment
// out: type of the expression,
let typeinfer_normalized env expr =
    let rec typeinfer_expr env expr =
        match expr with
        | Lit (LInt _) -> TyInt, []
        | Lit (LBool _) -> TyBool, []
        | Lit (LFloat _) -> TyFloat, []
        | Lit (LString _) -> TyString, []
        | Lit (LChar _) -> TyChar, []
        | Lit LUnit -> TyUnit, []

        | Var x ->
            match List.tryFind (fun entry -> fst entry = x) env with
            | Some (_, sch) -> instantiate sch, []
            | _ -> type_error "typeinfer_expr: variable %s is not defined in the environment" x

        | Tuple (ts) ->
            let fold_infer_tuple (acc_ty, acc_s, acc_env) t =
                let t_ty, t_s = typeinfer_expr acc_env t
                let t_ty = acc_ty @ [ t_ty ]
                let new_s = compose_subst t_s acc_s
                let new_env = apply_subst_to_env t_s acc_env
                (t_ty, new_s, new_env)

            let t_ty, t_s, _ = List.fold fold_infer_tuple ([], [], env) ts
            TyTuple t_ty, t_s

        | Lambda (param, ann, body) ->
            let param_ty =
                match ann with
                | Some ty -> ty
                | None -> gen_fresh_tv ()

            let new_env = (param, gen_fake_sch param_ty) :: env
            let body_ty, body_s = typeinfer_expr new_env body
            let param_ty = apply_subst body_s param_ty

            TyArrow(param_ty, body_ty), body_s

        | App (l, r) ->
            let l_ty, l_s = typeinfer_expr env l
            let r_ty, r_s = typeinfer_expr (apply_subst_to_env l_s env) r
            let l_ty = apply_subst r_s l_ty

            // check if the left expression is actually a lambda
            let ret_ty = gen_fresh_tv ()
            let arr_s = unify l_ty (TyArrow(r_ty, ret_ty))

            let final_s = l_s |> compose_subst r_s |> compose_subst arr_s
            let app_ty = apply_subst final_s ret_ty

            app_ty, final_s

        | Let (name, ann, e1, e2) ->
            let e1_ty, e1_s =
                match ann with
                | Some ty -> ty, []
                | None -> typeinfer_expr env e1

            let new_env = apply_subst_to_env e1_s env
            let sch = generalize e1_ty new_env
            let e2_ty, e2_s = typeinfer_expr ((name, sch) :: new_env) e2
            e2_ty, compose_subst e2_s e1_s

        | LetRec (name, ann, e1, e2) ->
            let let_ty =
                match ann with
                | Some ty -> ty
                | None -> gen_fresh_tv ()

            let new_env = (name, gen_fake_sch let_ty) :: env
            let e1_ty, e1_s = typeinfer_expr new_env e1
            let is_lambda = unify e1_ty (TyArrow(gen_fresh_tv (), gen_fresh_tv ()))

            let new_env = apply_subst_to_env e1_s env
            let sch = generalize e1_ty new_env
            let e2_ty, e2_s = typeinfer_expr ((name, sch) :: new_env) e2

            e2_ty, compose_subst e2_s e1_s

        | IfThenElse (cond, e1, e2) ->
            // if
            let cond_ty, cond_s = typeinfer_expr env cond
            let acc_s = compose_subst cond_s (unify cond_ty TyBool)
            let new_env = apply_subst_to_env acc_s env

            // then
            let e1_ty, e1_s = typeinfer_expr new_env e1
            let acc_s = compose_subst acc_s e1_s
            let new_env = apply_subst_to_env acc_s new_env

            // optional else
            match e2 with
            | Some e2 ->
                let e2_ty, e2_s = typeinfer_expr new_env e2
                let acc_s = compose_subst acc_s e2_s
                let unify_branch = unify (apply_subst acc_s e1_ty) (apply_subst acc_s e2_ty)
                let e_ty = apply_subst acc_s e1_ty
                let acc_s = compose_subst acc_s unify_branch
                e_ty, acc_s
            | None -> TyUnit, compose_subst (unify e1_ty TyUnit) acc_s


        | BinOp (e1, op, e2) when gamma0 |> List.map fst |> List.contains op ->
            let e1_ty, e1_s = typeinfer_expr env e1
            let e2_ty, e2_s = typeinfer_expr (apply_subst_to_env e1_s env) e2
            let unification = unify_check op (TyArrow(e1_ty, TyArrow(e2_ty, gen_fresh_tv ())))

            match unification with
            | Some (tv, ty) -> ty, compose_subst e2_s [ tv, ty ]
            | _ -> unexpected_error "typeinfer_expr: the binary operator does not support the passed operands (%s)" op

        | UnOp (op, e) when gamma0 |> List.map fst |> List.contains op ->
            let e_ty, e_s = typeinfer_expr env e
            let unification = unify_check op (TyArrow(e_ty, gen_fresh_tv ()))

            match unification with
            | Some (tv, ty) -> ty, compose_subst e_s [ tv, ty ]
            | _ -> unexpected_error "typeinfer_expr: the binary operator does not support the passed operands (%s)" op

        // error cases
        | BinOp (_, op, _) -> unexpected_error "typeinfer_expr: unsupported binary operator (%s)" op
        | _ -> unexpected_error "typeinfer_expr: unsupported expression: %s [AST: %A]" (pretty_expr expr) expr

    let res_ty, res_s = typeinfer_expr env expr
    normalize_tvs res_ty, res_s
