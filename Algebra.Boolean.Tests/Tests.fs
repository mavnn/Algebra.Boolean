module Algebra.Boolean.Tests

open Algebra.Boolean
open Xunit

[<Fact>]
let ``Infrastructure test`` () =
    Assert.Equal(<@@ 1 + 1 @@>, id' <@@ 1 + 1 @@>)