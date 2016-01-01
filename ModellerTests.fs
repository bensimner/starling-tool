module Starling.Tests.Modeller

open Chessie.ErrorHandling // ok
open Fuchu // general test framework
open Microsoft.Z3 // anything involving ctx
open Starling
open Starling.Collections
open Starling.Var
open Starling.Model
open Starling.Lang.AST
open Starling.Lang.Modeller
open Starling.Tests.Studies
open Starling.Pretty.Lang.AST

/// Assertion that converting the arithmetic expression `expr` to Z3
/// yields the given AST.
let assertZ3ArithExpr ctx expr z3 = 
    let model = ticketLockModel ctx
    Assert.Equal(Pretty.Types.hsep
                     [printExpression expr
                      "-Z3->" |> Pretty.Types.String
                      z3.ToString() |> Pretty.Types.String]
                 |> Pretty.Types.print, ok z3, arithExprToZ3 model model.Locals expr)

/// Assertion that converting the Boolean expression `expr` to Z3
/// yields the given AST.
let assertZ3BoolExpr ctx expr z3 = 
    let model = ticketLockModel ctx
    Assert.Equal(Pretty.Types.hsep
                     [printExpression expr
                      "-Z3->" |> Pretty.Types.String
                      z3.ToString() |> Pretty.Types.String]
                 |> Pretty.Types.print, ok z3, boolExprToZ3 model model.Locals expr)

let testExprToZ3 ctx = 
    testList "Test translation of expressions" 
        [ testList "Test translation of arithmetic expressions" 
              [ testCase "Test arithmetic-only expressions" 
                <| fun _ -> 
                    assertZ3ArithExpr ctx (Bop(Add, Bop(Mul, Int 1L, Int 2L), Int 3L)) 
                        (ctx.MkAdd [| ctx.MkMul [| ctx.MkInt 1 :> ArithExpr
                                                   ctx.MkInt 2 :> ArithExpr |]
                                      ctx.MkInt 3 :> ArithExpr |]) ]
          
          testList "Test translation of Boolean expressions" 
              [ testCase "Test Boolean-only expressions" <| fun _ -> 
                    (* We simplify obviously-true/false expressions down.
                     * This is one of them.
                     *)
                    assertZ3BoolExpr ctx (Bop(And, Bop(Or, True, True), False)) (ctx.MkFalse()) ] ]

let testModelVarListNoDuplicates ctx = 
    testList "Test modelling of variables forbids duplicates" 
        [ testCase "Forbid duplicate with same type" <| fun _ -> 
              Assert.Equal("bool foo; bool foo -> error", fail <| Starling.Errors.Var.Duplicate "foo", 
                           Starling.Var.makeVarMap ctx [ (Type.Bool, "foo")
                                                         (Type.Bool, "foo") ])
          testCase "Forbid duplicate with different type" <| fun _ -> 
              Assert.Equal("bool foo; int foo -> error", fail <| Starling.Errors.Var.Duplicate "foo", 
                           Starling.Var.makeVarMap ctx [ (Type.Bool, "foo")
                                                         (Type.Int, "foo") ]) ]

let testModelVars ctx = testList "Test modelling of variables" [ testModelVarListNoDuplicates ctx ]

/// Converts a model to some form that is accurately comparable.
let modelToComparable model = (model.Globals, model.Locals, model.Axioms, model.VProtos, model.DefViews)

let testModelPrimOnAtomic (ctx : Context) = 
    testCase "test modelPrimOnAtomic with ticketed lock example" 
    <| fun _ -> 
        Assert.Equal
            ("modelPrimOnAtomic with <t = ticket++>", ok (IntLoad(Some(LVIdent "t"), LVIdent "ticket", Increment)), 
             (modelPrimOnAtomic (ticketLockModel ctx) (Fetch(LVIdent "t", LV(LVIdent "ticket"), Increment))))

let testModelAxiomOnCommand (ctx : Context) = 
    testCase "test modelAxiomOnCommand with ticketed lock example" 
    <| fun _ -> 
        Assert.Equal
            ("modelAxiomOnCommand with {emp} <t = ticket++> {holdLock()}", 
             ok (PAAxiom { Conditions = 
                               { Pre = Multiset.empty()
                                 Post = 
                                     Multiset.ofList [ CondView.Func { VName = "holdTick"
                                                                       VParams = [ ctx.MkIntConst "t" ] } ] }
                           Inner = IntLoad(Some(LVIdent "t"), LVIdent "ticket", Increment) }), 
             (modelAxiomOnCommand (ticketLockModel ctx) 
                  { Pre = Multiset.empty()
                    Post = 
                        Multiset.ofList [ CondView.Func { VName = "holdTick"
                                                          VParams = [ ctx.MkIntConst "t" ] } ] } 
                  (Atomic(Fetch(LVIdent "t", LV(LVIdent "ticket"), Increment)))))

let testMakeAxiomConditionPair (ctx : Context) = 
    testCase "Test makeAxiomConditionPair with ticketed lock example" 
    <| fun _ -> 
        Assert.Equal
            ("makeAxiomConditionPair emp holdTick(t)", 
             ok ({ Pre = Multiset.empty()
                   Post = 
                       Multiset.ofList [ CondView.Func { VName = "holdTick"
                                                         VParams = [ ctx.MkIntConst "t" ] } ] }), 
             makeAxiomConditionPair (ticketLockModel ctx) (Unit) (View.Func {Name = "holdTick"; Params = [ LV(LVIdent "t") ]}))

let testTicketedLock ctx = 
    testCase "Test that the ticketed lock produces the correct model" <| fun _ -> 
        Assert.Equal("ticketed lock collation -> ticketed lock model", 
                     ticketLockModel ctx
                     |> ok
                     |> lift modelToComparable, modelWith ctx ticketLockCollated |> lift modelToComparable)

[<Tests>]
let testModeller = 
    let ctx = new Context()
    
    let t = 
        testList "Test the modeller" [ testExprToZ3 ctx
                                       testModelVars ctx
                                       testModelPrimOnAtomic ctx
                                       testMakeAxiomConditionPair ctx
                                       testList "Test modelling of case studies" [ testTicketedLock ctx ] ]
    ctx.Dispose()
    t
