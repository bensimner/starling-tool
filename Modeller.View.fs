namespace Starling.Lang.Modeller

open Chessie.ErrorHandling
open Starling.Collections
open Starling.Core
open Starling.Core.Model
open Starling.Core.TypeSystem
open Starling.Core.Var
open Starling.Core.View
open Starling.Lang.AST
open Starling.Utils

/// <summary>
///     The part of the modeller responsible for constructing views.
/// </summary>
module View =
    /// <summary>
    ///     Represents an error when converting a view or view definition.
    /// </summary>
    type Error =
        /// An expression in the view generated an error.
        | BadExpr of expr : Expression * err : Expr.Error
        /// A view was requested that does not exist.
        | NoSuchView of name : string
        /// A view lookup failed.
        | LookupError of name : string * err : Instantiate.Types.Error
        /// A view used variables in incorrect ways, eg by duplicating.
        | BadVar of err : VarMapError
        /// A viewdef conflicted with the shared variables.
        | SVarConflict of err : VarMapError

    /// Merges a list of prototype and definition parameters into one list,
    /// binding the types from the former to the names from the latter.
    let funcViewParMerge (ppars : TypedVar list) (dpars : Var list)
      : TypedVar list =
        List.map2 (fun ppar dpar -> withType (typeOf ppar) dpar) ppars dpars

    /// Adapts Instantiate.lookup to the modeller's needs.
    let lookupFunc (protos : FuncDefiner<ProtoInfo>) (func : Func<_>)
      : Result<DFunc, Error> =
        protos
        |> Instantiate.lookup func
        |> mapMessages (curry LookupError func.Name)
        |> bind (function
                 | Some (proto, _) -> proto |> ok
                 | None -> func.Name |> NoSuchView |> fail)


    module Pretty =
        open Starling.Core.Pretty
        open Starling.Core.Var.Pretty
        open Starling.Lang.AST.Pretty

        /// Pretty-prints view conversion errors.
        let printError : Error -> Doc =
            function
            | BadExpr(expr, err) ->
                wrapped "expression"
                    (printExpression expr)
                    (Starling.Lang.Modeller.Expr.Pretty.printError err)
            | NoSuchView name -> fmt "no view prototype for '{0}'" [ String name ]
            | LookupError(name, err) -> wrapped "lookup for view" (name |> String) (err |> Instantiate.Pretty.printError)
            | BadVar err ->
                colonSep [ "invalid variable usage" |> String
                           err |> printVarMapError ]
            | SVarConflict err ->
                colonSep [ "parameters conflict with shared variables" |> String
                           err |> printVarMapError ]
