/// <summary>
///     The main part of the converter from Starling's language AST to
///     its internal representation.
/// </summary>
namespace Starling.Lang.Modeller

open Chessie.ErrorHandling
open Starling
open Starling.Collections
open Starling.Core
open Starling.Core.TypeSystem
open Starling.Core.TypeSystem.Check
open Starling.Core.Expr
open Starling.Core.Var
open Starling.Core.Symbolic
open Starling.Core.Model
open Starling.Core.View
open Starling.Core.Command
open Starling.Core.Command.Create
open Starling.Core.Instantiate
open Starling.Core.Sub
open Starling.Lang
open Starling.Lang.AST
open Starling.Lang.Collator
open Starling.Lang.Modeller.Definer
open Starling.Lang.Modeller.Expr
open Starling.Lang.Modeller.View



/// <summary>
///     Types used only in the modeller and adjacent pipeline stages.
/// </summary>
[<AutoOpen>]
module Types =
    /// A conditional (flat or if-then-else) func.
    type CFunc =
        | ITE of SVBoolExpr * CView * CView
        | Func of SVFunc
        override this.ToString() = sprintf "CFunc(%A)" this

    /// A conditional view, or multiset of CFuncs.
    and CView = Multiset<IteratedContainer<CFunc, Sym<Var>>>

    /// A partially resolved command.
    type PartCmd<'view> =
        | Prim of Command
        | While of
            isDo : bool
            * expr : SVBoolExpr
            * inner : Block<'view, PartCmd<'view>>
        | ITE of
            expr : SVBoolExpr
            * inTrue : Block<'view, PartCmd<'view>>
            * inFalse : Block<'view, PartCmd<'view>>
        override this.ToString() = sprintf "PartCmd(%A)" this

    /// <summary>
    ///     Internal context for the method modeller.
    /// </summary>
    type MethodContext =
        { /// <summary>
          ///     The environment of visible shared variables.
          /// </summary>
          SharedVars : VarMap
          /// <summary>
          ///     The environment of visible thread-local variables.
          /// </summary>
          ThreadVars : VarMap
          /// <summary>
          ///     A definer containing the visible view prototypes.
          /// </summary>
          ViewProtos : FuncDefiner<ProtoInfo> }

    type ModellerViewExpr = ViewExpr<CView>
    type ModellerPartCmd = PartCmd<ModellerViewExpr>
    type ModellerBlock = Block<ModellerViewExpr, ModellerPartCmd>
    type ModellerViewedCommand = ViewedCommand<ModellerViewExpr, ModellerPartCmd>
    type ModellerMethod = Method<ModellerViewExpr, ModellerPartCmd>

    /// Represents an error when converting a view prototype.
    type ViewProtoError =
        /// A parameter name was used more than once in the same view prototype.
        | VPEDuplicateParam of AST.Types.ViewProto * param : string

    /// Represents an error when converting a prim.
    type PrimError =
        /// A prim used a bad shared variable.
        | BadSVar of var : LValue * err : VarMapError
        /// A prim used a bad thread variable.
        | BadTVar of var : LValue * err : VarMapError
        /// A prim used a bad variable of ambiguous scope.
        | BadAVar of var : LValue * err : VarMapError
        /// A prim contained a bad expression.
        | BadExpr of expr : AST.Types.Expression * err : Modeller.Expr.Error
        /// A prim tried to increment an expression.
        | IncExpr of expr : AST.Types.Expression
        /// A prim tried to decrement an expression.
        | DecExpr of expr : AST.Types.Expression
        /// A prim tried to increment a Boolean.
        | IncBool of expr : AST.Types.Expression
        /// A prim tried to decrement a Boolean.
        | DecBool of expr : AST.Types.Expression
        /// A prim tried to atomic-load from a non-lvalue expression.
        | LoadNonLV of expr : AST.Types.Expression
        /// A prim had a type error in it.
        | TypeMismatch of expected : Type * bad : LValue * got : Type
        /// A prim has no effect.
        | Useless

    /// Represents an error when converting a method.
    type MethodError =
        /// The method contains a semantically invalid local assign.
        | BadAssign of dest : LValue * src : AST.Types.Expression
                                     * err : PrimError
        /// The method contains a semantically invalid atomic action.
        | BadAtomic of atom : Atomic * err : PrimError
        /// The method contains a bad if-then-else condition.
        | BadITECondition of expr: AST.Types.Expression * err: Modeller.Expr.Error
        /// The method contains a bad while condition.
        | BadWhileCondition of expr: AST.Types.Expression * err: Modeller.Expr.Error
        /// The method contains a bad view.
        | BadView of view : ViewExpr<AST.Types.View> * err : Modeller.View.Error
        /// The method contains an command not yet implemented in Starling.
        | CommandNotImplemented of cmd : AST.Types.Command<ViewExpr<View>>

    /// Represents an error when converting a model.
    type ModelError =
        /// A view prototype in the program generated a `ViewProtoError`.
        | BadVProto of proto : AST.Types.ViewProto * err : ViewProtoError
        /// A constraint in the program generated a definer error.
        | BadDefiner of definer : (AST.Types.ViewSignature * AST.Types.Expression option) list
                      * err : Modeller.Definer.Error
        /// A method in the program generated an `MethodError`.
        | BadMethod of methname : string * err : MethodError
        /// A variable in the program generated a `VarMapError`.
        | BadVar of scope: string * err : VarMapError


/// <summary>
///     Pretty printers for the modeller types.
/// </summary>
module Pretty =
    open Starling.Core.Pretty
    open Starling.Collections.Multiset.Pretty
    open Starling.Core.TypeSystem.Pretty
    open Starling.Core.Var.Pretty
    open Starling.Core.Model.Pretty
    open Starling.Core.Expr.Pretty
    open Starling.Core.Command.Pretty
    open Starling.Core.Symbolic.Pretty
    open Starling.Core.View.Pretty
    open Starling.Lang.AST.Pretty

    /// Pretty-prints a CFunc.
    let rec printCFunc : CFunc -> Doc =
        function
        | CFunc.ITE(i, t, e) ->
            hsep [ String "if"
                   printSVBoolExpr i
                   String "then"
                   t |> printCView |> ssurround "[" "]"
                   String "else"
                   e |> printCView |> ssurround "[" "]" ]
        | Func v -> printSVFunc v

    /// Pretty-prints a CView.
    and printCView : CView -> Doc =
        printMultiset (printIteratedContainer printCFunc (printSym printVar))
        >> ssurround "[|" "|]"

    /// Pretty-prints a part-cmd at the given indent level.
    let rec printPartCmd (pView : 'view -> Doc) : PartCmd<'view> -> Doc =
        function
        | PartCmd.Prim prim -> Command.Pretty.printCommand prim
        | PartCmd.While(isDo, expr, inner) ->
            cmdHeaded (hsep [ String(if isDo then "Do-while" else "While")
                              (printSVBoolExpr expr) ])
                      [printBlock pView (printPartCmd pView) inner]
        | PartCmd.ITE(expr, inTrue, inFalse) ->
            cmdHeaded (hsep [String "begin if"
                             (printSVBoolExpr expr) ])
                      [headed "True" [printBlock pView (printPartCmd pView) inTrue]
                       headed "False" [printBlock pView (printPartCmd pView) inFalse]]

    /// Pretty-prints view prototype conversion errors
    let printViewProtoError : ViewProtoError -> Doc =
        function
        | VPEDuplicateParam(vp, param) ->
            fmt "view proto '{0} has duplicate param {1}" [ printViewProto vp
                                                            String param ]

    /// Pretty-prints prim errors.
    let printPrimError : PrimError -> Doc =
        function
        | BadSVar (var, err : VarMapError) ->
            wrapped "shared lvalue" (printLValue var)
                                    (printVarMapError err)
        | BadTVar (var, err : VarMapError) ->
            wrapped "thread-local lvalue" (printLValue var)
                                          (printVarMapError err)
        | BadAVar (var, err : VarMapError) ->
            wrapped "lvalue" (printLValue var) (printVarMapError err)
        | BadExpr (expr, err : Modeller.Expr.Error) ->
            wrapped "expression" (printExpression expr)
                                 (Modeller.Expr.Pretty.printError err)
        | IncExpr expr ->
            fmt "cannot increment an expression ('{0}')"
                [ printExpression expr ]
        | DecExpr expr ->
            fmt "cannot decrement an expression ('{0}')"
                [ printExpression expr ]
        | IncBool expr ->
            fmt "cannot increment a Boolean ('{0}')"
                [ printExpression expr ]
        | DecBool expr ->
            fmt "cannot decrement a Boolean ('{0}')"
                [ printExpression expr ]
        | LoadNonLV expr ->
            fmt "cannot load from non-lvalue expression '{0}'"
                [ printExpression expr ]
        | TypeMismatch (expected, bad, got) ->
            fmt "lvalue '{0}' should be of type {1}, but is {2}"
                [ printLValue bad
                  printType expected
                  printType got ]
        | Useless -> String "command has no effect"

    /// Pretty-prints method errors.
    let printMethodError : MethodError -> Doc =
        function
        | BadAssign (dest, src, err) ->
            wrapped "local assign" (printAssign dest src) (printPrimError err)
        | BadAtomic (atom, err) ->
            wrapped "atomic action" (printAtomic atom) (printPrimError err)
        | BadITECondition (expr, err) ->
            wrapped "if-then-else condition"
                (printExpression expr)
                (Modeller.Expr.Pretty.printError err)
        | BadWhileCondition (expr, err) ->
            wrapped "while-loop condition"
                (printExpression expr)
                (Modeller.Expr.Pretty.printError err)
        | BadView (view, err) ->
            wrapped "view expression"
                (printViewExpr printView view)
                (Modeller.View.Pretty.printError err)
        | CommandNotImplemented cmd ->
            fmt "command {0} not yet implemented"
                [ printCommand (printViewExpr printView) cmd ]

    /// Pretty-prints model conversion errors.
    let printModelError : ModelError -> Doc =
        function
        | BadDefiner(constrs, err) ->
            wrapped "constraint set"
                (constrs |> List.map (uncurry printConstraint) |> commaSep |> Truncate)
                (Modeller.Definer.Pretty.printError err)
        | BadVar(scope, err) ->
            wrapped "variables in scope" (String scope) (printVarMapError err)
        | BadMethod(methname, err) ->
            wrapped "method" (String methname) (printMethodError err)
        | BadVProto(vproto, err) ->
            wrapped "view prototype" (printViewProto vproto)
                                     (printViewProtoError err)

module Main =
    (*
     * Starling imperative language semantics
     *)
    let prim : string -> TypedVar list -> TypedVar list -> SVBoolExpr -> PrimSemantics =
        fun name results args body -> { Name = name; Results = results; Args = args; Body = body }

    /// <summary>
    ///   The core semantic function for the imperative language.
    /// </summary>
    /// <remarks>
    ///   <para>
    ///     The functions beginning with '!' have special syntax in the
    ///     imperative language.
    ///   </para>
    /// </remarks>
    let coreSemantics : PrimSemanticsMap =
        // TODO(CaptainHayashi): specify this in the language (standard library?).
        // TODO(CaptainHayashi): generic functions?
        // TODO(CaptainHayashi): add shared/local/expr qualifiers to parameters?
        List.fold (fun m (a : PrimSemantics) -> Map.add a.Name a m) Map.empty
        <| [ (*
           * CAS
           *)
          (prim "ICAS" [ Int "destA"; Int "testA"; ] [ Int "destB"; Int "testB"; Int "set"; ]
               <| mkAnd [ mkImplies (iEq (siVar "destB") (siVar "testB"))
                                 (mkAnd [ iEq (siVar "destA") (siVar "set")
                                          iEq (siVar "testA") (siVar "testB") ] )
                          mkImplies (mkNot (iEq (siVar "destB") (siVar "testB")))
                                    (mkAnd [ iEq (siVar "destA") (siVar "destB")
                                             iEq (siVar "testA") (siVar "destB") ] ) ] )
          // Boolean CAS
          (prim "BCAS" [Bool "destA"; Bool "testA"; ] [Bool "destB"; Bool "testB"; Bool "set"; ]
               <| mkAnd [ mkImplies (bEq (sbVar "destB") (sbVar "testB"))
                                    (mkAnd [ bEq (sbVar "destA") (sbVar "set")
                                             bEq (sbVar "testA") (sbVar "testB") ] )
                          mkImplies (mkNot (bEq (sbVar "destB") (sbVar "testB")))
                                    (mkAnd [ bEq (sbVar "destA") (sbVar "destB")
                                             bEq (sbVar "testA") (sbVar "destB") ] ) ] )

          (*
           * Atomic load
           *)
          // Integer load
          (prim "!ILoad"  [ Int "dest" ] [ Int "src" ]
               <| iEq (siVar "dest") (siVar "src"))

          // Integer load-and-increment
          (prim "!ILoad++"  [ Int "dest"; Int "srcA" ] [ Int "srcB" ]
               <| mkAnd [ iEq (siVar "dest") (siVar "srcB")
                          iEq (siVar "srcA") (mkAdd2 (siVar "srcB") (AInt 1L)) ])

          // Integer load-and-decrement
          (prim "!ILoad--"  [ Int "dest"; Int "srcA" ] [ Int "srcB" ]
               <| mkAnd [ iEq (siVar "dest") (siVar "srcB")
                          iEq (siVar "srcA") (mkSub2 (siVar "srcB") (AInt 1L)) ])

          // Integer increment
          (prim "!I++"  [ Int "srcA" ] [ Int "srcB" ]
               <| iEq (siVar "srcA") (mkAdd2 (siVar "srcB") (AInt 1L)))

          // Integer decrement
          (prim "!I--"  [ Int "srcA" ] [ Int "srcB" ]
               <| iEq (siVar "srcA") (mkSub2 (siVar "srcB") (AInt 1L)))

          // Boolean load
          (prim "!BLoad"  [ Bool "dest" ] [ Bool "src" ]
               <| bEq (sbVar "dest") (sbVar "src"))

          (*
           * Atomic store
           *)

          // Integer store
          (prim "!IStore" [ Int "dest" ] [ Int "src" ]
               <| iEq (siVar "dest") (siVar "src"))

          // Boolean store
          (prim "!BStore" [ Bool "dest" ] [ Bool "src" ]
               <| bEq (sbVar "dest") (sbVar "src"))

          (*
           * Local set
           *)

          // Integer local set
          (prim "!ILSet" [ Int "dest" ] [ Int "src" ]
               <| iEq (siVar "dest") (siVar "src"))

          // Boolean store
          (prim "!BLSet" [ Bool "dest" ] [ Bool "src" ]
               <| bEq (sbVar "dest") (sbVar "src"))

          (*
           * Assumptions
           *)

          // Identity
          (prim "Id" [] [] BTrue)

          // Assume
          (prim "Assume" [] [Bool "expr"] <| sbVar "expr") ]


    //
    // View applications
    //

    /// Models an AFunc as a CFunc.
    let modelCFunc
      ({ ViewProtos = protos; ThreadVars = env } : MethodContext)
      (afunc : Func<Expression>) =
        // First, make sure this AFunc actually has a prototype
        // and the correct number of parameters.
        afunc
        |> lookupFunc protos
        |> bind (fun proto ->
                 // First, model the AFunc's parameters.
                 afunc.Params
                 |> Seq.map
                        (wrapMessages Modeller.View.Error.BadExpr
                            (Modeller.Expr.model env id))
                 |> collect
                 // Then, put them into a VFunc.
                 |> lift (vfunc afunc.Name)
                 // Now, we can use Instantiate's type checker to ensure
                 // the params in the VFunc are of the types mentioned
                 // in proto.
                 |> bind (fun vfunc ->
                              Instantiate.checkParamTypes vfunc proto
                              |> mapMessages (curry LookupError vfunc.Name)))
        // Finally, lift to CFunc.
        |> lift CFunc.Func

    /// Tries to flatten a view AST into a CView.
    /// Takes an environment of local variables, and the AST itself.
    let rec modelCView (ctx : MethodContext) : View -> Result<CView, Modeller.View.Error> =
        let mkCView cfunc = Multiset.singleton ({ Func = cfunc; Iterator = None })
        function
        | View.Func afunc ->
            modelCFunc ctx afunc |> lift mkCView
        | View.If(e, l, r) ->
            lift3 (fun em lm rm -> CFunc.ITE(em, lm, rm) |> mkCView)
                  (wrapMessages Modeller.View.Error.BadExpr (modelBool ctx.ThreadVars id) e)
                  (modelCView ctx l)
                  (modelCView ctx r)
        | Unit -> Multiset.empty |> ok
        | Join(l, r) ->
            lift2 (Multiset.append)
                  (modelCView ctx l)
                  (modelCView ctx r)

    //
    // Axioms
    //

    let (|Shared|_|) ctx (lvalue : LValue) = tryLookupVar ctx.SharedVars lvalue
    let (|Thread|_|) ctx (lvalue : LValue) = tryLookupVar ctx.ThreadVars lvalue

    /// Converts a Boolean load to a Prim.
    let modelBoolLoad : MethodContext -> Var -> Expression -> FetchMode -> Result<PrimCommand, PrimError> =
        fun { SharedVars = svars } dest srcExpr mode ->
        (* In a Boolean load, the destination must be LOCAL and Boolean;
         *                    the source must be a GLOBAL Boolean lvalue;
         *                    and the fetch mode must be Direct.
         *)
        match srcExpr.Node with
        | LV srcLV ->
            trial {
                let! src = wrapMessages BadSVar (lookupVar svars) srcLV
                match src, mode with
                | Typed.Bool s, Direct ->
                    return
                        command
                            "!BLoad"
                                [ Bool dest ]
                                [ s |> Before |> Reg |> BVar |> Expr.Bool ]

                | Typed.Bool s, Increment -> return! fail (IncBool srcExpr)
                | Typed.Bool s, Decrement -> return! fail (DecBool srcExpr)
                | _ -> return! fail (TypeMismatch (Type.Bool (), srcLV, typeOf src))
            }
        | _ -> fail (LoadNonLV srcExpr)

    /// Converts an integer load to a Prim.
    let modelIntLoad : MethodContext -> Var -> Expression -> FetchMode -> Result<PrimCommand, PrimError> =
        fun { SharedVars = svars } dest srcExpr mode ->
        (* In an integer load, the destination must be LOCAL and integral;
         *                    the source must be a GLOBAL arithmetic lvalue;
         *                    and the fetch mode is unconstrained.
         *)
        match srcExpr.Node with
        | LV srcLV ->
            trial {
                let! src = wrapMessages BadSVar (lookupVar svars) srcLV
                match src, mode with
                | Typed.Int s, Direct ->
                    return command "!ILoad" [ Int dest ] [ s |> Before |> Reg |> AVar |> Expr.Int ]

                | Typed.Int s, Increment ->
                    return command "!ILoad++" [ Int dest; Int s ] [ s |> Before |> Reg |> AVar |> Expr.Int ]

                | Typed.Int s, Decrement ->
                    return command "!ILoad--" [ Int dest; Int s ] [ s |> Before |> Reg |> AVar |> Expr.Int ]

                | _ -> return! fail (TypeMismatch (Type.Int (), srcLV, typeOf src))
            }
        | _ -> fail (LoadNonLV srcExpr)

    /// Converts a Boolean store to a Prim.
    let modelBoolStore : MethodContext -> Var -> Expression -> FetchMode -> Result<PrimCommand, PrimError> =
        fun { ThreadVars = tvars } dest src mode ->
        (* In a Boolean store, the destination must be GLOBAL and Boolean;
         *                     the source must be LOCAL and Boolean;
         *                     and the fetch mode must be Direct.
         *)
        trial {
            let! sxp = wrapMessages BadExpr (modelBool tvars Before) src
            match mode with
            | Direct ->
                return
                    command
                        "!BStore"
                        [ Bool dest ]
                        [ sxp |> Expr.Bool ]
            | Increment -> return! fail (IncBool src)
            | Decrement -> return! fail (DecBool src)
        }

    /// Converts an integral store to a Prim.
    let modelIntStore : MethodContext -> Var -> Expression -> FetchMode -> Result<PrimCommand, PrimError> =
        fun { ThreadVars = tvars } dest src mode ->
        (* In an integral store, the destination must be GLOBAL and integral;
         *                       the source must be LOCAL and integral;
         *                       and the fetch mode must be Direct.
         *)
        trial {
            let! sxp =
                wrapMessages BadExpr (modelInt tvars MarkedVar.Before) src
            match mode with
            | Direct ->
                return
                    command
                        "!IStore"
                        [ Int dest ]
                        [ sxp |> Expr.Int ]

            | Increment -> return! fail (IncExpr src)
            | Decrement -> return! fail (DecExpr src)
        }

    /// Converts a CAS to part-commands.
    let modelCAS : MethodContext -> LValue -> LValue -> Expression -> Result<PrimCommand, PrimError> =
        fun { SharedVars = svars; ThreadVars = tvars } destLV testLV set ->
        (* In a CAS, the destination must be SHARED;
         *           the test variable must be THREADLOCAL;
         *           and the to-set value must be a valid expression.
         * dest, test, and set must agree on type.
         * The type of dest and test influences how we interpret set.
         *)
        wrapMessages BadSVar (lookupVar svars) destLV
        >>= (fun dest ->
                 mkPair dest
                 <!> wrapMessages BadTVar (lookupVar tvars) testLV)
        >>= (function
             | UnifyBool (d, t) ->
                 set
                 |> wrapMessages BadExpr (modelBool tvars MarkedVar.Before)
                 |> lift
                        (fun s ->
                            command "BCAS"
                                [ Bool d; Bool t ]
                                [ d |> sbBefore |> Expr.Bool
                                  t |> sbBefore |> Expr.Bool
                                  s |> Expr.Bool ] )
             | UnifyInt (d, t) ->
                set
                |> wrapMessages BadExpr (modelInt tvars MarkedVar.Before)
                |> lift
                       (fun s ->
                            command "ICAS"
                                [ Int d; Int t ]
                                [ d |> siBefore |> Expr.Int
                                  t |> siBefore |> Expr.Int
                                  s |> Expr.Int ] )
             | UnifyFail (d, t) ->
                 // Oops, we have a type error.
                 // Arbitrarily single out test as the cause of it.
                 fail (TypeMismatch (typeOf d, testLV, typeOf t)))

    /// Converts an atomic fetch to a model command.
    let modelFetch : MethodContext -> LValue -> Expression -> FetchMode -> Result<PrimCommand, PrimError> =
        fun ctx destLV srcExpr mode ->
        (* First, determine whether we have a fetch from shared to thread
         * (a load), or a fetch from thread to shared (a store).
         * Also figure out whether we have a Boolean or arithmetic
         * version.
         * We figure this out by looking at dest.
         *)
        match destLV with
        | Shared ctx (Typed.Int dest) -> modelIntStore ctx dest srcExpr mode
        | Shared ctx (Typed.Bool dest) -> modelBoolStore ctx dest srcExpr mode
        | Thread ctx (Typed.Int dest) -> modelIntLoad ctx dest srcExpr mode
        | Thread ctx (Typed.Bool dest) -> modelBoolLoad ctx dest srcExpr mode
        | lv -> fail (BadAVar(lv, NotFound (flattenLV lv)))

    /// Converts a single atomic command from AST to part-commands.
    let rec modelAtomic : MethodContext -> Atomic -> Result<PrimCommand, PrimError> =
        fun ctx a ->
        let prim =
            match a.Node with
            | CompareAndSwap(dest, test, set) -> modelCAS ctx dest test set
            | Fetch(dest, src, mode) -> modelFetch ctx dest src mode
            | Postfix(operand, mode) ->
                (* A Postfix is basically a Fetch with no destination, at this point.
                 * Thus, the source must be SHARED.
                 * We don't allow the Direct fetch mode, as it is useless.
                 *)
                trial {
                    let! stype = wrapMessages BadSVar (lookupVar ctx.SharedVars) operand
                    // TODO(CaptainHayashi): sort out lvalues...
                    let op = flattenLV operand
                    match mode, stype with
                    | Direct, _ ->
                        return! fail Useless
                    | Increment, Typed.Bool _ ->
                        return! fail (IncBool (freshNode <| LV operand))
                    | Decrement, Typed.Bool _ ->
                        return! fail (DecBool (freshNode <| LV operand))
                    | Increment, Typed.Int _ ->
                        return command "!I++" [ Int op ] [op |> Before |> Reg |> AVar |> Expr.Int ]
                    | Decrement, Typed.Int _ ->
                        return command "!I--" [ Int op ] [op |> Before |> Reg |> AVar |> Expr.Int ]
                }
            | Id -> ok (command "Id" [] [])
            | Assume e ->
                e
                |> wrapMessages BadExpr (modelBool ctx.ThreadVars MarkedVar.Before)
                |> lift (Expr.Bool >> List.singleton >> command "Assume" [])
        lift (fun cmd -> { cmd with Node = Some a }) prim

    /// Converts a local variable assignment to a Prim.
    and modelAssign : MethodContext -> LValue -> Expression -> Result<PrimCommand, PrimError> =
        fun { ThreadVars = tvars } lLV e ->
        (* We model assignments as !ILSet or !BLSet, depending on the
         * type of l, which _must_ be in the locals set..
         * We thus also have to make sure that e is the correct type.
         *)
        trial {
            let! l = wrapMessages BadTVar (lookupVar tvars) lLV
            match l with
            | Typed.Bool ls ->
                let! em =
                    wrapMessages BadExpr (modelBool tvars MarkedVar.Before) e
                return
                    command
                        "!BLSet"
                        [ Bool ls ]
                        [ em |> Expr.Bool ]
            | Typed.Int ls ->
                let! em =
                    wrapMessages BadExpr (modelInt tvars MarkedVar.Before) e
                return
                    command
                        "!ILSet"
                        [ Int ls ]
                        [ em |> Expr.Int ]
        }

    /// Creates a partially resolved axiom for an if-then-else.
    and modelITE
      : MethodContext
        -> Expression
        -> Block<ViewExpr<View>, Command<ViewExpr<View>>>
        -> Block<ViewExpr<View>, Command<ViewExpr<View>>>
        -> Result<ModellerPartCmd, MethodError> =
        fun ctx i t f ->
            trial { let! iM =
                        wrapMessages
                            BadITECondition
                            (modelBool ctx.ThreadVars id)
                            i
                    (* We need to calculate the recursive axioms first, because we
                     * need the inner cpairs for each to store the ITE placeholder.
                     *)
                    let! tM = modelBlock ctx t
                    let! fM = modelBlock ctx f
                    return ITE(iM, tM, fM) }

    /// Converts a while or do-while to a PartCmd.
    /// Which is being modelled is determined by the isDo parameter.
    /// The list is enclosed in a Chessie result.
    and modelWhile
      (isDo : bool)
      (ctx : MethodContext)
      (e : Expression)
      (b : Block<ViewExpr<View>, Command<ViewExpr<View>>>)
      : Result<ModellerPartCmd, MethodError> =
        (* A while is also not fully resolved.
         * Similarly, we convert the condition, recursively find the axioms,
         * inject a placeholder, and add in the recursive axioms.
         *)
        lift2 (fun eM bM -> PartCmd.While(isDo, eM, bM))
              (wrapMessages
                   BadWhileCondition
                   (modelBool ctx.ThreadVars id)
                   e)
              (modelBlock ctx b)

    /// Converts a PrimSet to a PartCmd.
    and modelPrim
      (ctx : MethodContext)
      ({ PreAssigns = ps; Atomics = ts; PostAssigns = qs } : PrimSet)
      : Result<ModellerPartCmd, MethodError> =

        let mAssign = uncurry (wrapMessages2 BadAssign (modelAssign ctx))
        let mAtomic = wrapMessages BadAtomic (modelAtomic ctx)

        [ Seq.map mAssign ps ; Seq.map mAtomic ts ; Seq.map mAssign qs ]
        |> Seq.concat
        |> collect
        |> lift Prim

    /// Converts a command to a PartCmd.
    /// The list is enclosed in a Chessie result.
    and modelCommand
      (ctx : MethodContext)
      (n : Command<ViewExpr<View>>)
      : Result<ModellerPartCmd, MethodError> =
        match n.Node with
        | Command'.Prim p -> modelPrim ctx p
        | Command'.If(i, t, e) -> modelITE ctx i t e
        | Command'.While(e, b) -> modelWhile false ctx e b
        | Command'.DoWhile(b, e) -> modelWhile true ctx e b
        | _ -> fail (CommandNotImplemented n)

    /// Converts a view expression into a CView.
    and modelViewExpr (ctx : MethodContext)
      : ViewExpr<View> -> Result<ModellerViewExpr, Modeller.View.Error> =
        function
        | Mandatory v -> modelCView ctx v |> lift Mandatory
        | Advisory v -> modelCView ctx v |> lift Advisory

    /// Converts the view and command in a ViewedCommand.
    and modelViewedCommand
      (ctx : MethodContext)
      ({Post = post; Command = command}
         : ViewedCommand<ViewExpr<View>, Command<ViewExpr<View>>>)
      : Result<ModellerViewedCommand, MethodError> =
        lift2 (fun postM commandM -> {Post = postM; Command = commandM})
              (post |> modelViewExpr ctx
                    |> mapMessages (curry MethodError.BadView post))
              (command |> modelCommand ctx)

    /// Converts the views and commands in a block.
    /// The converted block is enclosed in a Chessie result.
    and modelBlock
      (ctx : MethodContext)
      ({Pre = bPre; Contents = bContents} :
           Block<ViewExpr<View>, Command<ViewExpr<View>>>)
      : Result<ModellerBlock, MethodError> =
        lift2 (fun bPreM bContentsM -> {Pre = bPreM; Contents = bContentsM})
              (bPre |> modelViewExpr ctx
                    |> mapMessages (curry MethodError.BadView bPre))
              (bContents |> Seq.map (modelViewedCommand ctx) |> collect)

    /// Converts a method's views and commands.
    /// The converted method is enclosed in a Chessie result.
    let modelMethod
      (ctx : MethodContext)
      ({ Signature = sg ; Body = b }
         : Method<ViewExpr<View>, Command<ViewExpr<View>>>)
      : Result<string * ModellerMethod, ModelError> =
        // TODO(CaptainHayashi): method parameters
        b
        |> modelBlock ctx
        |> lift (fun c -> (sg.Name, { Signature = sg ; Body = c }))
        |> mapMessages (curry BadMethod sg.Name)

    /// Checks a view prototype to see if it contains duplicate parameters.
    let checkViewProtoDuplicates (proto : ViewProto)
      : Result<ViewProto, ViewProtoError> =
        match proto with
        | NoIterator (f, _) | WithIterator (f, _) ->
            f.Params
            |> Seq.map valueOf
            |> findDuplicates
            |> Seq.toList
            |> function
               | [] -> ok proto
               | ds -> List.map (fun d -> VPEDuplicateParam(proto, d)) ds |> Bad

    /// Checks view prototypes and converts them to func-table form.
    let modelViewProtos (protos : #(ViewProto seq))
      : Result<FuncDefiner<ProtoInfo>, ModelError> =
        let modelViewProto proto =
            proto
            |> checkViewProtoDuplicates
            |> lift
                   (function
                    | NoIterator (f, isAnonymous) ->
                        (f, { IsIterated = false; IsAnonymous = isAnonymous; } )
                    | WithIterator (f, _) ->
                        (f, { IsIterated = true; IsAnonymous = false; } ))
            |> mapMessages (curry BadVProto proto)

        protos
        |> Seq.map modelViewProto
        |> collect
        |> lift FuncDefiner.ofSeq

    /// Converts a collated script to a model.
    let model
      (collated : CollatedScript)
      : Result<Model<ModellerMethod, ViewDefiner<SVBoolExpr option>>, ModelError> =
        trial {
            // Make variable maps out of the global and local variable definitions.
            let! globals = makeVarMap collated.Globals
                           |> mapMessages (curry BadVar "shared")
            let! locals = makeVarMap collated.Locals
                          |> mapMessages (curry BadVar "thread-local")

            let desugaredMethods, unknownProtos =
                Starling.Lang.ViewDesugar.desugar locals collated.Methods

            let! vprotos =
                modelViewProtos (Seq.append collated.VProtos unknownProtos)

            let dctx =
                { Modeller.Definer.ViewProtos = vprotos
                  SharedVars = globals
                  Search = collated.Search }
            let! definer =
                collated.Constraints
                |> wrapMessages BadDefiner (Modeller.Definer.model dctx)

            let mctx =
                { ViewProtos = vprotos
                  SharedVars = globals
                  ThreadVars = locals }
            let! axioms =
                desugaredMethods
                |> Seq.map (modelMethod mctx)
                |> collect
                |> lift Map.ofSeq

            return
                { Globals = globals
                  Locals = locals
                  ViewDefs = definer
                  Semantics = coreSemantics
                  Axioms = axioms
                  ViewProtos = vprotos }
        }
