module Algebra.Boolean.Tests

open Microsoft.FSharp.Quotations
open Algebra.Boolean
open Algebra.Boolean.Simplifiers
open Xunit

[<Fact>]
let ``not pattern`` () =
    Assert.Equal (<@@ true @@>, match <@@ not true @@> with Not' e -> e)

[<Fact>]
let ``Commute ||`` () =
    Assert.Equal (<@@ false || true @@>, commute <@@ true || false @@>)

[<Fact>]
let ``Commute &&`` () =
    Assert.Equal (<@@ false && true @@>, commute <@@ true && false @@>)

[<Fact>]
let ``Commute is top level only`` () =
    Assert.Equal (<@@ false && (false || true) @@>, commute <@@ (false || true) && false @@>)

[<Fact>]
let ``Identity reduction &&`` () =
    Assert.Equal (<@@ false @@>, identity <@@ true && false @@>)

[<Fact>]
let ``Identity reduction ||`` () =
    Assert.Equal (<@@ true @@>, identity <@@ true || false @@>)

[<Fact>]
let ``Identity reduction recurses`` () =
    Assert.Equal (<@@ true @@>, identity <@@ (true || false) && true @@>)

[<Fact>]
let ``Identity reduction recurses with none boolean`` () =
    Assert.Equal (<@@ "bob" = "fred" @@>, identity <@@ ("bob" = "fred" || false) && true @@>)

[<Fact>]
let ``Identity reduction recurses with none boolean 2`` () =
    Assert.Equal (<@@ "bob" = "fred" @@>, identity <@@ (false || "bob" = "fred") && true @@>)

[<Fact>]
let ``Idempotence reduction &&`` () =
    Assert.Equal (<@@ true @@>, idempotence <@@ true && true @@>)

[<Fact>]
let ``Idempotence reduction ||`` () =
    Assert.Equal (<@@ true @@>, idempotence <@@ true || true @@>)

[<Fact>]
let ``Associate a || b || c -> a || (b || c)`` () =
    Assert.Equal (<@@ 1 = 1 || (2 = 2 || 3 = 3) @@>, associate <@@ 1 = 1 || 2 = 2 || 3 = 3 @@>)

[<Fact>]
let ``Associate a && b && c -> a && (b && c)`` () =
    Assert.Equal (<@@ 1 = 1 && (2 = 2 && 3 = 3) @@>, associate <@@ 1 = 1 && 2 = 2 && 3 = 3 @@>)

[<Fact>]
let ``Associate a || (b || c) -> a || b || c`` () =
    Assert.Equal (<@@ 1 = 1 || 2 = 2 || 3 = 3 @@>, associate <@@ 1 = 1 || (2 = 2 || 3 = 3) @@>)

[<Fact>]
let ``Associate a && (b && c) -> a && b && c`` () =
    Assert.Equal (<@@ 1 = 1 && 2 = 2 && 3 = 3 @@>, associate <@@ 1 = 1 && (2 = 2 && 3 = 3) @@>)

[<Fact>]
let ``Annihilation reduction ||`` () =
    Assert.Equal (<@@ true @@>, annihilate <@@ 1 = 2 || true @@>)

[<Fact>]
let ``Annihilation reduction &&`` () =
    Assert.Equal (<@@ false @@>, annihilate <@@ 1 = 1 && false @@>)

[<Fact>]
let ``Absorption reduction 1`` () =
    Assert.Equal (<@@ 2 = 1 @@>, absorb <@@ 2 = 1 && (2 = 1 || 3 = 4) @@>)

[<Fact>]
let ``Absorption reduction 2`` () =
    Assert.Equal (<@@ 2 = 1 @@>, absorb <@@ 2 = 1 || (3 = 3 && 2 = 1) @@>)

[<Fact>]
let ``Complement ||`` () =
    Assert.Equal (<@@ true @@>, complement <@@ true || not true @@>)

[<Fact>]
let ``Complement &&`` () =
    Assert.Equal (<@@ false @@>, complement <@@ true && not true @@>)

[<Fact>]
let ``Complement || 2`` () =
    Assert.Equal (<@@ true @@>, complement <@@ "fred".StartsWith "bob" || not ("fred".StartsWith "bob") @@>)

[<Fact>]
let ``Double negation`` () =
    Assert.Equal (<@@ true @@>, doubleNegation <@@ not (not true) @@>)

[<Fact>]
let ``De Morgan &&`` () =
    Assert.Equal (<@@ not ("bob" = "bob" || "fred" = "bob") @@>, deMorgan <@@ not ("bob" = "bob") && not ("fred" = "bob") @@>)

[<Fact>]
let ``De Morgan ||`` () =
    Assert.Equal (<@@ not ("bob" = "bob" && "fred" = "bob") @@>, deMorgan <@@ not ("bob" = "bob") || not ("fred" = "bob") @@>)

[<Fact>]
let ``Beta reduction 1`` () =
    Assert.Equal (<@@ "bob" @@>, beta <@@ (fun (x : string) -> x) "bob" @@>)

[<Fact>]
let ``Beta reduction 2`` () =
    Assert.Equal (<@@ "bob" + "fred" @@>, beta <@@ (fun (x : string) -> x + "fred") "bob" @@>)

[<Fact>]
let ``Beta reduction 3`` () =
    Assert.Equal (<@@ "bob" + "fred" @@>, beta <@@ (fun x -> fun y -> x + y) "bob" "fred" @@>)

[<Fact>]
let ``Beta reduction 4`` () =
    Assert.Equal (<@@ "bob" + "fred" @@>, beta <@@ (fun x y -> x + y) "bob" "fred" @@>)

[<Fact>]
let ``Beta reduction 5`` () =
    Assert.DoesNotThrow(
        fun () ->
            beta <@@ Seq.filter (fun x -> true) Seq.empty<string> @@> |> ignore)

[<Fact>]
let ``Beta reduction 6`` () =
    Assert.DoesNotThrow(
        fun () ->
            beta <@@ 
                    (fun _ ->
                        let p =
                            fun (_ : string) -> true
                        Seq.filter p Seq.empty<string>) ()
                @@> |> ignore)

[<Fact>]
let ``unbind works`` () =
    Assert.Equal(<@@ 10 + 20 @@>, 
        unbind <@@ 
            let x = 10
            x + 20
        @@>)

[<Fact>]
let ``unbind works 2`` () =
    Assert.Equal(<@@ 10 + 10 @@>, 
        unbind <@@ 
            let x = 10
            x + x
        @@>)

[<Fact>]
let ``unbind works 3`` () =
    Assert.Equal(<@@ 10 + 10 + 20 @@>, 
        unbind <@@ 
            let x = 10
            let y = 20
            x + x + y
        @@>)

[<Fact>]
let ``unbind works 4`` () =
    Assert.Equal(<@@ 5 + 5 + (20 + 10) @@>, 
        unbind <@@ 
            let x = 10 in
            let y = 20 + x
            let x = 5
            x + x + y
        @@>)

[<Fact>]
let ``unpipe works`` () =
    Assert.Equal (<@@ not false @@>, unpipe <@@ false |> not @@>)

[<Fact>]
let ``unpipe works recursively`` () =
    Assert.Equal (<@@ not (not false) @@>, unpipe <@@ false |> not |> not @@>)

[<Fact>]
let ``Generic method unpiping`` () =
    Assert.DoesNotThrow (fun () -> unpipe <@@ Seq.empty<string> |> Seq.filter (fun x -> true) @@> |> ignore)