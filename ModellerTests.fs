module Starling.Tests.Modeller

open NUnit.Framework
open Starling
open Starling.Collections
open Starling.Core.Expr
open Starling.Core.Var
open Starling.Core.Model
open Starling.Core.Command
open Starling.Core.Instantiate
open Starling.Lang.AST
open Starling.Lang.Modeller
open Starling.Tests.Studies

/// Wrapper for search modeller tests.
/// Mainly exists to persuade nUnit to use the correct types.
type SearchViewDefEntry =
    { Search : int option
      InitDefs : ViewDef<DView> list }

/// Tests for the modeller.
type ModellerTests() =
    /// View prototypes for the ticket lock modeller.
    static member TicketLockProtos : FuncTable<unit> =
        makeFuncTable
            [ (func "holdLock" [], ())
              (func "holdTick" [(Type.Int, "t")], ()) ]

    /// Sample environment used in expression modelling tests.
    static member Env =
        Map.ofList [ ("foo", Type.Int)
                     ("bar", Type.Int)
                     ("baz", Type.Bool)
                     ("emp", Type.Bool) ]

    static member EmptyCView : unit -> CView = Multiset.empty

    /// <summary>
    ///     Test cases for checking view modelling on correct view exprs.
    /// </summary>
    static member ViewExprsGood =
        [ TestCaseData(View.Unit)
             .Returns(Some (ModellerTests.EmptyCView ()))
             .SetName("Modelling the unit view returns the empty multiset")
          TestCaseData(afunc "holdLock" [] |> View.Func)
             .Returns(Some (Multiset.singleton (CFunc.Func (vfunc "holdLock" []))))
             .SetName("Modelling a valid single view returns a singleton multiset")
        ]

    /// <summary>
    ///     Tests view modelling on correct view exprs.
    /// </summary>
    [<TestCaseSource("ViewExprsGood")>]
    member x.``View modelling on correct view expressions succeeds`` vex =
        vex
        |> modelCView ModellerTests.TicketLockProtos ModellerTests.Env
        |> okOption


    /// <summary>
    ///     Test cases for checking view modelling on incorrect view exprs.
    /// </summary>
    static member ViewExprsBad =
        [ TestCaseData(afunc "badfunc" [] |> View.Func)
             .Returns(Some [NoSuchView "badfunc"])
             .SetName("Modelling an unknown single view returns an error")
          TestCaseData(afunc "holdTick" [] |> View.Func)
             .Returns(Some [LookupError ("holdTick", CountMismatch(0, 1))])
             .SetName("Modelling a single view with bad parameter count returns an error")
          TestCaseData(afunc "holdTick" [Expression.True] |> View.Func)
             .Returns(Some [LookupError ("holdTick", Error.TypeMismatch ((Type.Int, "t"), Type.Bool))])
             .SetName("Modelling a single view with bad parameter type returns an error") ]

    /// <summary>
    ///     Tests view modelling on correct view exprs.
    /// </summary>
    [<TestCaseSource("ViewExprsBad")>]
    member x.``View modelling on incorrect view expressions fails`` vex =
        vex
        |> modelCView ModellerTests.TicketLockProtos ModellerTests.Env
        |> failOption


    /// Arithmetic expression modelling tests.
    static member ArithmeticExprs =
        [ TestCaseData(Bop(Add, Bop(Mul, Int 1L, Int 2L), Int 3L)).Returns(Some <| AAdd [ AMul [ AInt 1L
                                                                                                 AInt 2L ]
                                                                                          AInt 3L ])
            .SetName("model (1 * 2) + 3") ]

    /// Tests whether the arithmetic expression modeller works.
    [<TestCaseSource("ArithmeticExprs")>]
    member x.``test the arithmetic expression modeller`` ast = modelArithExpr ModellerTests.Env ast |> okOption


    /// Boolean expression modelling tests.
    /// These all use the ticket lock model.
    static member BooleanExprs =
        [ TestCaseData(Bop(And, Bop(Or, True, True), False)).Returns(Some BFalse)
            .SetName("model and simplify (true || true) && false") ]

    /// Tests whether the arithmetic expression modeller works.
    [<TestCaseSource("BooleanExprs")>]
    member x.``test the Boolean expression modeller`` ast =
        ast
        |> modelBoolExpr ModellerTests.Env
        |> okOption


    /// Tests for modelling bad variable lists.
    static member BadVarLists =
        [ TestCaseData([ (Type.Bool, "foo")
                         (Type.Bool, "foo") ]).Returns(Some <| [ VarMapError.Duplicate "foo" ])
              .SetName("disallow var lists with duplicates of same type")

          TestCaseData([ (Type.Int, "bar")
                         (Type.Bool, "bar") ]).Returns(Some <| [ VarMapError.Duplicate "bar" ])
              .SetName("disallow var lists with duplicates of different type") ]


    /// Tests the creation of var lists.
    [<TestCaseSource("BadVarLists")>]
    member x.``invalid var lists are rejected during mapping`` vl = makeVarMap vl |> failOption

    /// Tests for modelling valid variable lists.
    static member VarLists =
        let emp : (Type * string) list = []
        let empm : VarMap = Map.empty
        [ TestCaseData([ (Type.Int, "baz")
                         (Type.Bool, "emp") ])
              .Returns(Some <| Map.ofList [ ("baz", Type.Int)
                                            ("emp", Type.Bool) ])
              .SetName("allow var lists with no duplicate variables")
          TestCaseData(emp).Returns(Some <| empm).SetName("allow empty var lists") ]

    /// Tests the creation of var lists.
    [<TestCaseSource("VarLists")>]
    member x.``valid var lists are accepted during mapping`` (vl: (Type * string) list) =
        makeVarMap vl |> okOption


    /// Tests for the atomic primitive modeller.
    /// These use the ticket lock model.
    static member AtomicPrims =
        [ TestCaseData(Fetch(LVIdent "t", LV(LVIdent "ticket"), Increment))
            .Returns(Some <| func "!ILoad++" ["t" |> aBefore |> AExpr; "t" |> aAfter |> AExpr
                                              "ticket" |> aBefore |> AExpr; "ticket" |> aAfter |> AExpr])
            .SetName("model a valid integer load as a prim") ]

    /// Tests the atomic primitive modeller using the ticket lock.
    [<TestCaseSource("AtomicPrims")>]
    member x.``atomic primitives are modelled correctly as prims`` a = modelPrim ticketLockModel.Globals ticketLockModel.Locals a |> okOption


    /// Constructs a Prim of the correct type to come out of a modeller.
    static member mprim (cmd : Command) : PartCmd<CView> = Prim cmd

    /// Constructs a single Prim of type Command<View>.
    static member prim (ac : Prim) : Command<View> = Command.Prim [ ac ]

    /// Tests for the command axiom modeller.
    /// These use the ticket lock model.
    static member CommandAxioms =
        [ TestCaseData(ModellerTests.prim(Fetch(LVIdent "t",
                                                LV(LVIdent "ticket"),
                                                Increment)))
            .Returns(ModellerTests.mprim
                         [ func "!ILoad++" [ "t" |> aBefore |> AExpr
                                             "t" |> aAfter |> AExpr
                                             "ticket" |> aBefore |> AExpr
                                             "ticket" |> aAfter |> AExpr ]]
                     |> Some)
            .SetName("model a valid integer load command as an axiom") ]

    /// Tests the command modeller using the ticket lock.
    [<TestCaseSource("CommandAxioms")>]
    member x.``commands are modelled correctly as part-commands`` c =
        c
        |> modelCommand ModellerTests.TicketLockProtos
                        ticketLockModel.Globals
                        ticketLockModel.Locals
        |> okOption


    /// Type-constraining builder for viewdef sets.
    static member viewDefSet (vs : ViewDef<DView> seq) : Set<ViewDef<DView>> =
        Set.ofSeq vs

    /// Tests for the search modeller.
    /// These use TicketLockProtos.
    static member SearchViewDefs =
        [ TestCaseData({ Search = None; InitDefs = []})
             .Returns(ModellerTests.viewDefSet [])
             .SetName("Searching for no viewdefs does not change an empty viewdef set")
          TestCaseData({ Search = None; InitDefs = ticketLockViewDefs })
             .Returns(ModellerTests.viewDefSet ticketLockViewDefs)
             .SetName("Searching for no viewdefs does not change a full viewdef set")
          TestCaseData({ Search = Some 0; InitDefs = []})
             .Returns(ModellerTests.viewDefSet
                          [ { View = Multiset.empty ()
                              Def = None }])
             .SetName("Searching for size-0 viewdefs adds emp to an empty viewdef set")
          TestCaseData({ Search = Some 0; InitDefs = ticketLockViewDefs })
             .Returns(ModellerTests.viewDefSet ticketLockViewDefs)
             .SetName("Searching for size-0 viewdefs does not change a full viewdef set")
          TestCaseData({ Search = Some 1; InitDefs = [] })
             .Returns(ModellerTests.viewDefSet
                          [ { View = Multiset.empty ()
                              Def = None }
                            { View = Multiset.singleton (func "holdLock" [])
                              Def = None }
                            { View = Multiset.singleton (func "holdTick" [(Type.Int, "t0")])
                              Def = None }])
             .SetName("Searching for size-1 viewdefs yields viewdefs for emp and the view prototypes") ]

    /// Tests viewdef searches.
    [<TestCaseSource("SearchViewDefs")>]
    member x.``viewdef searches are carried out correctly`` svd =
        addSearchDefs ModellerTests.TicketLockProtos svd.Search svd.InitDefs
        |> Set.ofList

    /// Full case studies to model.
    static member Models =
        [ TestCaseData(ticketLockCollated).Returns(Some ticketLockModel).SetName("model the ticket lock") ]

    /// Tests the whole modelling process.
    [<TestCaseSource("Models")>]
    member x.``case studies are modelled correctly`` col = model col |> okOption

