module Algebra.Boolean

open Microsoft.FSharp.Quotations
open Microsoft.FSharp.Quotations.DerivedPatterns
open Microsoft.FSharp.Quotations.ExprShape
open Microsoft.FSharp.Quotations.Patterns

let id' quote =
    let rec transform q =
        match q with
        | ShapeVar v -> Expr.Var v
        | ShapeLambda (v, e) -> Expr.Lambda(v, transform e)
        | ShapeCombination (o, es) ->
            ExprShape.RebuildShapeCombination(o, es)
    transform quote