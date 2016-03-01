module Starling.Lang.Guarder

open Starling.Collections
open Starling.Expr
open Starling.Core.Model
open Starling.Utils
open Starling.Lang.AST
open Starling.Lang.Modeller

/// Converts a func from conditional to guarded form.
/// This takes the set of all conditions forming the suffix of any guards
/// generated from this view.
let rec guardCFuncIn (suffix : Set<BoolExpr>) = 
    function 
    | CFunc.Func v -> 
        [ { Cond = 
                suffix
                |> Set.toList
                |> mkAnd
            Item = v } ]
    | CFunc.ITE(expr, tviews, fviews) -> 
        List.concat [ guardCViewIn (suffix.Add expr) (Multiset.toList tviews)
                      guardCViewIn (suffix.Add(mkNot expr)) (Multiset.toList fviews) ]

/// Resolves a list of views, given a set of conditions held true.
and guardCViewIn suffix = concatMap (guardCFuncIn suffix)

/// Resolves a full condition-view multiset into a guarded-view multiset.
let guardCView : CView -> GView = 
    // TODO(CaptainHayashi): woefully inefficient.
    Multiset.toList
    >> guardCViewIn Set.empty 
    >> Multiset.ofList

/// Converts a viewed command to guarded views.
let rec guardViewedCommand { Command = command ; Post = post } =
    { Command = guardPartCmd command ; Post = guardCView post }

/// Converts a block to guarded views.
and guardBlock {Pre = pre; Contents = contents} =
    { Pre = guardCView pre
      Contents = List.map guardViewedCommand contents }

/// Converts a PartCmd to guarded views.
and guardPartCmd : PartCmd<CView> -> PartCmd<GView> =
    function
    | Prim p -> Prim p
    | While (isDo, expr, inner) ->
        While (isDo, expr, guardBlock inner)
    | ITE (expr, inTrue, inFalse) ->
        ITE (expr, guardBlock inTrue, guardBlock inFalse)

/// Converts a method to guarded views.
let guardMethod { Signature = signature; Body = body } = 
    { Signature = signature; Body = guardBlock body }

/// Converts an entire model to guarded views.
let guard : Model<Method<CView, PartCmd<CView>>, DView> -> Model<Method<GView, PartCmd<GView>>, DView> =
    mapAxioms guardMethod
