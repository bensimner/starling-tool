/// Tests for Starling.Horn and Starling.HSF.
module Starling.Tests.Horn

open Chessie.ErrorHandling
open NUnit.Framework
open Starling.Collections
open Starling.Var
open Starling.Utils
open Starling.Expr
open Starling.Model
open Starling.Horn
open Starling.HSF
open Starling.Errors.Horn
open Starling.Tests.Studies

/// Tests for Starling.Horn and Starling.HSF.
type HornTests() =
    /// Tests the view predicate name generator.
    [<TestCaseSource("ViewPredNamings")>]
    member x.``the HSF predicate name generator generates names correctly`` v =
        let pn : Multiset<View> -> string = predNameOfMultiset
        pn v

    /// Test cases for the viewdef variable extractor.
    /// These all use the ticketed lock model.
    static member ViewDefHeads =
        let ms : ViewDef list -> Multiset<ViewDef> = Multiset.ofList
        [ TestCaseData(ms [ { Name = "holdLock"
                              Params = [] }
                            { Name = "holdTick"
                              Params = [ (Type.Int, "t") ] } ]).Returns(Some <| Pred { Name = "v_holdLock_holdTick"
                                                                                       Params =
                                                                                           [ aUnmarked "serving"
                                                                                             aUnmarked "ticket"
                                                                                             aUnmarked "t" ] })
            .SetName("List HSF params of ticketed lock view 'holdLock() * holdTick(t)' as serving, ticket, and t") ]

    /// Tests the viewdef LHS translator.
    [<TestCaseSource("ViewDefHeads")>]
    member x.``the HSF viewdef LHS translator works correctly using the ticketed lock model`` v =
        v
        |> bodyOfConstraint (ticketLockModel.Globals
                             |> Map.toSeq
                             |> Seq.map fst
                             |> Set.ofSeq)
        |> okOption

    /// Test cases for the viewdef Horn clause modeller.
    /// These are in the form of models whose viewdefs are to be modelled.
    static member ViewDefModels =
      [ TestCaseData(ticketLockModel)
          .Returns(
              Set.ofList
                  [ { Head = Ge (aUnmarked "ticket", aUnmarked "serving")
                      Body = [ Pred { Name = "v"
                                      Params = [ aUnmarked "serving"; aUnmarked "ticket" ] } ] }
                    { Head = Gt (aUnmarked "ticket", aUnmarked "t")
                      Body = [ Pred { Name = "v_holdTick"
                                      Params = [ aUnmarked "serving"; aUnmarked "ticket"; aUnmarked "t" ] } ] }
                    { Head = Gt (aUnmarked "ticket", aUnmarked "serving")
                      Body = [ Pred { Name = "v_holdLock"
                                      Params = [ aUnmarked "serving"; aUnmarked "ticket" ] } ] }
                    { Head = Neq (aUnmarked "serving", aUnmarked "t")
                      Body = [ Pred { Name = "v_holdLock_holdTick"
                                      Params = [ aUnmarked "serving"; aUnmarked "ticket"; aUnmarked "t" ] } ] }
                    { Head = Neq (aUnmarked "ta", aUnmarked "tb")
                      Body = [ Pred { Name = "v_holdTick_holdTick"
                                      Params = [ aUnmarked "serving"; aUnmarked "ticket"; aUnmarked "ta"; aUnmarked "tb" ] } ] }
                    { Head = False
                      Body = [ Pred { Name = "v_holdLock_holdLock"
                                      Params = [ aUnmarked "serving"; aUnmarked "ticket"] } ] }
                  ]
              |> Some
          ).SetName("Model the ticketed lock's viewdefs as Horn clauses") ]

    /// Tests the model viewdef translator.
    [<TestCaseSource("ViewDefModels")>]
    member x.``the HSF model viewdef translator works correctly using various models`` (mdl: PartModel) =
        mdl |> hsfModelViewDefs |> okOption

    /// Test cases for the variable Horn clause modeller.
    /// These are in the form of models whose viewdefs are to be modelled.
    static member VariableModels =
      [ TestCaseData(ticketLockModel)
          .Returns(
              Set.ofList
                  [ { Head = Pred { Name = "v"
                                    Params = [ aUnmarked "serving"; aUnmarked "ticket" ] }
                      Body = [ Eq (aUnmarked "serving", AInt 0L) ] }
                    { Head = Pred { Name = "v"
                                    Params = [ aUnmarked "serving"; aUnmarked "ticket" ] }
                      Body = [ Eq (aUnmarked "ticket", AInt 0L) ] } ]
              |> Some
          ).SetName("Model the ticketed lock's variable initialisations as Horn clauses") ]

    /// Tests the model viewdef translator.
    [<TestCaseSource("VariableModels")>]
    member x.``the HSF model variable initialiser works correctly using various models`` (mdl: PartModel) =
        mdl |> hsfModelVariables |> okOption
