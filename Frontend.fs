﻿/// <summary>
///     The Starling-language frontend driver.
/// </summary>
module Starling.Lang.Frontend

open Chessie.ErrorHandling
open Starling
open Starling.Core.Pretty
open Starling.Core.Expr
open Starling.Core.Expr.Pretty
open Starling.Core.Graph
open Starling.Core.Graph.Pretty
open Starling.Core.Model
open Starling.Core.Model.Pretty
open Starling.Core.View
open Starling.Core.View.Pretty
open Starling.Core.GuardedView
open Starling.Core.GuardedView.Pretty
open Starling.Core.Symbolic
open Starling.Core.Symbolic.Pretty
open Starling.Core.Var
open Starling.Core.Var.Pretty
open Starling.Lang.AST.Pretty
open Starling.Lang.Modeller
open Starling.Lang.Modeller.Pretty
open Starling.Lang.Guarder


(*
 * Request and response types
 *)

/// <summary>
///     Type of requests to the Starling frontend.
/// </summary>
type Request =
    /// Only parse a Starling script; return `Response.Parse`.
    | Parse
    /// Parse and collate a Starling script; return `Response.Collate`.
    | Collate
    /// Parse, collate, and model a Starling script; return `Response.Model`.
    | Model
    /// Parse, collate, model, and guard a Starling script;
    /// return `Response.Guard`.
    | Guard
    /// Parse, collate, model, guard, and graph a Starling script;
    /// return `Response.Graph`.
    | Graph
    /// Parse, collate, model, guard, and graph a Starling script;
    /// call continuation with Model<Graph, DView>.
    | Continuation

/// <summary>
///     Type of responses from the Starling frontend.
/// </summary>
type Response =
    /// Output of the parsing step only.
    | Parse of AST.Types.ScriptItem list
    /// Output of the parsing and collation steps.
    | Collate of Collator.Types.CollatedScript
    /// Output of the parsing, collation, and modelling steps.
    | Model of Model<ModellerMethod, ViewDefiner<BoolExpr<Sym<Var>> option>>
    /// Output of the parsing, collation, modelling, and guarding stages.
    | Guard of Model<GuarderMethod, ViewDefiner<BoolExpr<Sym<Var>> option>>
    /// Output of the parsing, collation, modelling, guarding and destructuring stages.
    | Graph of Model<Graph, ViewDefiner<BoolExpr<Sym<Var>> option>>

(*
 * Error types
 *)

/// <summary>
///     Type of errors generated by the Starling frontend.
/// </summary>
type Error =
    /// A parse error occurred, details of which are enclosed in string form.
    | Parse of string
    /// A modeller error occurred, given as a `ModelError`.
    | Model of Lang.Modeller.Types.ModelError
    /// A graph error occurred, given as a `CFG.Error`.
    | Graph of Core.Graph.Types.Error

(*
 * Pretty-printing
 *)

/// <summary>
///     Pretty-prints a response.
/// </summary>
/// <param name="mview">
///     The ModelView instructing this pretty-printer on how to print
///     models.
/// </param>
/// <returns>
///     A function converting Responses to Docs.
/// </returns>
let printResponse (mview : ModelView) : Response -> Doc =
    let printVModel paxiom m =
        printModelView
            paxiom
            (printViewDefiner
                (Option.map (printBoolExpr (printSym printVar))
                 >> withDefault (String "?")))
            mview m

    function
    | Response.Parse s -> Lang.AST.Pretty.printScript s
    | Response.Collate c -> Lang.Collator.Pretty.printCollatedScript c
    | Response.Model m ->
        printVModel
            (printMethod (printViewExpr printCView)
                         (printPartCmd (printViewExpr printCView)))
            m
    | Response.Guard m ->
        printVModel
            (printMethod (printViewExpr (printIteratedGView (printSym String)))
                         (printPartCmd (printViewExpr (printIteratedGView (printSym String)))))
            m
    | Response.Graph m ->
        printVModel printGraph m

/// <summary>
///     Pretty-prints an error.
/// </summary>
let printError : Error -> Doc =
    function
    | Error.Parse e -> Core.Pretty.String e
    | Error.Model e -> Lang.Modeller.Pretty.printModelError e
    | Error.Graph e -> Core.Graph.Pretty.printError e

(*
 * Driver functions
 *)

/// Runs the Starling frontend.
/// Takes six arguments: the first is whether to output times; the second is the
/// `Response` telling the frontend what
/// to output; the third, and fourth, are functions to connect the successful, and
/// error, output with the surrounding pipeline; the fifth is a continuation for the
/// surrounding pipeline; and final is an optional filename from which the frontend
/// should read (if empty, read from stdin).
let run
  (times : bool)
  (request : Request)
  (success : Response -> 'response)
  (error : Error -> 'error)
  (continuation
     : Result<Model<Graph, ViewDefiner<BoolExpr<Sym<Var>> option>>, 'error>
     -> Result<'response, 'error>)
  : string option -> Result<'response, 'error> =
    let phase op test output continuation m =
        let time = System.Diagnostics.Stopwatch.StartNew()
        op m
        |> (time.Stop(); (if times then printfn "Phase %A; Elapsed: %dms" test time.ElapsedMilliseconds); id)
        |> if request = test then lift (output >> success) >> mapMessages error else continuation

    let parse = Parser.parseFile >> mapMessages Error.Parse
    let collate = lift Collator.collate
    let model = bind (Modeller.Main.model >> mapMessages Error.Model)
    let guard = lift Guarder.guard
    let graph = bind (Grapher.graph >> mapMessages Error.Graph)

    let ( ** ) = ( <| )
    phase    parse   Request.Parse   Response.Parse
    ** phase collate Request.Collate Response.Collate
    ** phase model   Request.Model   Response.Model
    ** phase guard   Request.Guard   Response.Guard
    ** phase graph   Request.Graph   Response.Graph
    ** (mapMessages error >> continuation)
