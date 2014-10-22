module Algebra.Boolean

open Microsoft.FSharp.Quotations
open Microsoft.FSharp.Quotations.ExprShape
open Microsoft.FSharp.Quotations.Patterns
open Microsoft.FSharp.Quotations.DerivedPatterns

let (|True'|_|) expr =
    match expr with
    | Value (o, t) when t = typeof<bool> && (o :?> bool) = true ->
        Some expr
    | _ ->
        None

let (|False'|_|) expr =
    match expr with
    | Value (o, t) when t = typeof<bool> && (o :?> bool) = false ->
        Some expr
    | _ ->
        None

let (|Or'|_|) expr =
    match expr with
    | IfThenElse (left, True' _, right) ->
        Some (left, right)
    | _ ->
        None

let (|And'|_|) expr =
    match expr with
    | IfThenElse (left, right, False' _) ->
        Some (left, right)
    | _ ->
        None

let (|Not'|_|) expr =
    match expr with
    | SpecificCall <@@ not @@> (_, _, [e]) ->
        Some e
    | _ ->
        None

let associate quote =
    match quote with
    | Or' (Or' (l, r), r') ->
        <@@ %%l || (%%r || %%r') @@>
    | Or' (l, Or' (l', r)) ->
        <@@ %%l || %%l' || %%r @@>
    | And' (And' (l, r), r') ->
        <@@ %%l && (%%r && %%r') @@>
    | And' (l, And' (l', r)) ->
        <@@ %%l && %%l' && %%r @@>
    | _ ->
        quote

let commute quote =
    match quote with
    | Or' (left, right) ->
        <@@ %%right || %%left @@>
    | And' (left, right) ->
        <@@ %%right && %%left @@>
    | _ ->
        quote

let distribute quote =
    match quote with
    | And' (p, Or' (p', p'')) ->
        <@@ (%%p && %%p') || (%%p && %%p'') @@>
    | Or' (p, And' (p', p'')) ->
        <@@ (%%p || %%p') && (%%p || %%p'') @@>
    | _ ->
        quote

let gather quote =
    match quote with
    | And' (Or'(p, p'), Or'(p'', p''')) when p = p'' ->
        <@@ %%p || (%%p' && %%p''') @@>
    | Or' (And'(p, p'), And'(p'', p''')) when p = p'' ->
        <@@ %%p && (%%p' || %%p''') @@>
    | _ ->
        quote

let identity quote =
    let rec transform q =
        match q with
        | And' (True' _, p)
        | And' (p, True' _)
        | Or' (False' _, p) 
        | Or' (p, False' _)
            -> transform p
        | ShapeVar v -> Expr.Var v
        | ShapeLambda (v, e) -> Expr.Lambda(v, transform e)
        | ShapeCombination (o, es) ->
            RebuildShapeCombination(o, es |> List.map transform)
    transform quote

let annihilate quote =
    let rec transform q =
        match q with
        | And' (False' f, _)
        | And' (_, False' f)
            -> f
        | Or' (True' t, _) 
        | Or' (_, True' t)
            -> t
        | ShapeVar v -> Expr.Var v
        | ShapeLambda (v, e) -> Expr.Lambda(v, transform e)
        | ShapeCombination (o, es) ->
            RebuildShapeCombination(o, es |> List.map transform)
    transform quote

let absorb quote =
    let rec transform q =
        match q with
        | And' (p, Or' (p', _)) 
        | And' (p, Or' (_, p')) 
        | And' (Or' (p', _), p)
        | And' (Or' (_, p'), p)
        | Or' (p, And' (p', _))
        | Or' (p, And' (_, p'))
        | Or' (And' (p', _), p)
        | Or' (And' (_, p'), p) when p = p' ->
            p
        | ShapeVar v -> Expr.Var v
        | ShapeLambda (v, e) -> Expr.Lambda(v, transform e)
        | ShapeCombination (o, es) ->
            RebuildShapeCombination(o, es |> List.map transform)
    transform quote

let idempotence quote =
    let rec transform q =
        match q with
        | And' (p, p') when p = p' ->
            transform p
        | Or' (p, p')  when p = p' ->
            transform p
        | ShapeVar v -> Expr.Var v
        | ShapeLambda (v, e) -> Expr.Lambda(v, transform e)
        | ShapeCombination (o, es) ->
            RebuildShapeCombination(o, es |> List.map transform)
    transform quote

let complement quote =
    let rec transform q =
        match q with
        | And' (p, Not' p')
        | And' (Not' p, p') when p = p' ->
            <@@ false @@>
        | Or' (p, Not' p')
        | Or' (Not' p, p') when p = p' ->
            <@@ true @@>
        | ShapeVar v -> Expr.Var v
        | ShapeLambda (v, e) -> Expr.Lambda(v, transform e)
        | ShapeCombination (o, es) ->
            RebuildShapeCombination(o, es |> List.map transform)
    transform quote

let doubleNegation quote =
    match quote with
    | Not' (Not' p) ->
        p
    | _ ->
        quote

let deMorgan quote =
    match quote with
    | Or' (Not' p, Not' p') ->
        <@@ not (%%p && %%p') @@>
    | And' (Not' p, Not' p') ->
        <@@ not (%%p || %%p') @@>
    | _ ->
        quote

let beta quote =
    let rec findApplication values q =
        match q with
        | Application (body, value) ->
            findApplication (value::values) body 
        | ShapeLambda (v, e) ->
            match values with
            | [] ->
                Expr.Lambda(v, findApplication [] e)
            | h::t ->
                findApplication t (replaceVar v.Name h e)
        | ShapeVar v ->
            Expr.Var v
        | ShapeCombination (o, es) ->
            RebuildShapeCombination(o, es |> List.map (findApplication values))
    and replaceVar name value body =
        match body with
        | ShapeVar v ->
            if v.Name = name then value else Expr.Var v
        | ShapeLambda (v, e) ->
            Expr.Lambda(v, replaceVar name value e)
        | ShapeCombination (o, es) ->
            RebuildShapeCombination(o, es |> List.map (replaceVar name value))
    findApplication [] quote