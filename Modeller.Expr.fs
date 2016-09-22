namespace Starling.Lang.Modeller

open Chessie.ErrorHandling

open Starling.Collections
open Starling.Utils
open Starling.Lang.AST
open Starling.Core.Expr
open Starling.Core.Var
open Starling.Core.Symbolic
open Starling.Core.TypeSystem


/// <summary>
///     The part of the modeller responsible for constructing expressions.
/// </summary>
module Expr =
    /// <summary>
    ///     Represents an error when converting an expression.
    /// </summary>
    type Error =
        // TODO(CaptainHayashi): more consistent constructor names
        /// A non-Boolean expression was found in a Boolean position.
        | ExprNotBoolean
        /// A non-Boolean variable was found in a Boolean position.
        | VarNotBoolean of var : LValue
        /// A non-integral expression was found in an integral position.
        | ExprNotInt
        /// A non-integral variable was found in an integral position.
        | VarNotInt of var : LValue
        /// A variable usage in the expression produced a `VarMapError`.
        | Var of var : LValue * err : VarMapError
        /// A symbolic expression appeared in an ambiguous position.
        | AmbiguousSym of sym : string


    /// <summary>
    ///     Models a Starling expression as an <c>Expr</c>.
    ///
    ///     <para>
    ///         Whenever we find a variable, we check the given environment
    ///         to make sure it both exists and is being used in a type-safe
    ///         manner.  Thus, this part of the modeller implements much of
    ///         Starling's type checking.
    ///     </para>
    ///     <para>
    ///         Since <c>modelExpr</c> and its Boolean and integral
    ///         equivalents are used to create expressions over both
    ///         <c>Var</c> and <c>MarkedVar</c>, we allow variable lookups
    ///         to be modified by a post-processing function.
    ///     </para>
    /// </summary>
    /// <param name="env">
    ///     The <c>VarMap</c> of variables bound where this expression
    ///     occurs.  Usually, but not always, these are the thread-local
    ///     variables.
    /// </param>
    /// <param name="varF">
    ///     A function to transform any variables after they are looked-up,
    ///     but before they are placed in the modelled expression.  Use this
    ///     to apply markers on variables, etc.
    /// </param>
    /// <typeparam name="var">
    ///     The type of variables in the <c>Expr</c>, achieved by
    ///     applying <paramref name="varF"/> to <c>Var</c>s.
    /// </typeparam>
    /// <returns>
    ///     A function taking <c>Expression</c>s.  This function will return
    ///     a <c>Result</c>, over <c>Expr.Error</c>, containing the modelled
    ///     <c>Expr</c> on success.  The exact type parameters of the
    ///     expression depend on <paramref name="varF"/>.
    /// </returns>
    let rec model
      (env : VarMap)
      (varF : Var -> 'var)
      (e : Expression)
      : Result<Expr<Sym<'var>>, Error> =
        match e.Node with
        (* First, if we have a variable, the type of expression is
           determined by the type of the variable.  If the variable is
           symbolic, then we have ambiguity. *)
            | LV v ->
                v
                |> wrapMessages Var (lookupVar env)
                |> lift
                       (Mapper.map
                            (Mapper.compose
                                 (Mapper.cmake (varF >> Reg))
                                 (Mapper.make AVar BVar)))
            | Symbolic (sym, exprs) ->
                fail (AmbiguousSym sym)
            (* We can use the active patterns above to figure out whether we
             * need to treat this expression as arithmetic or Boolean.
             *)
            | _ -> match e with
                    | ArithExp expr -> expr |> modelInt env varF |> lift Expr.Int
                    | BoolExp expr -> expr |> modelBool env varF |> lift Expr.Bool
                    | _ -> failwith "unreachable[modelExpr]"

    /// <summary>
    ///     Models a Starling Boolean expression as an <c>BoolExpr</c>.
    ///
    ///     <para>
    ///         See <c>modelExpr</c> for more information.
    ///     </para>
    /// </summary>
    /// <param name="env">
    ///     The <c>VarMap</c> of variables bound where this expression
    ///     occurs.  Usually, but not always, these are the thread-local
    ///     variables.
    /// </param>
    /// <param name="varF">
    ///     A function to transform any variables after they are looked-up,
    ///     but before they are placed in <c>AVar</c>.  Use this to apply
    ///     markers on variables, etc.
    /// </param>
    /// <typeparam name="var">
    ///     The type of variables in the <c>BoolExpr</c>, achieved by
    ///     applying <paramref name="varF"/> to <c>Var</c>s.
    /// </typeparam>
    /// <returns>
    ///     A function, taking <c>Expression</c>s previously judged as
    ///     Boolean.  This function will return a <c>Result</c>, over
    ///     <c>Expr.Error</c>, containing the modelled <c>BoolExpr</c> on
    ///     success.  The exact type parameters of the expression depend on
    ///     <paramref name="varF"/>.
    /// </returns>
    and modelBool
      (env : VarMap)
      (varF : Var -> 'var)
      : Expression -> Result<BoolExpr<Sym<'var>>, Error> =
        let mi = modelInt env varF
        let me = model env varF

        let rec mb e =
            match e.Node with
            | True -> BTrue |> ok
            | False -> BFalse |> ok
            | LV v ->
                (* Look-up the variable to ensure it a) exists and b) is of a
                 * Boolean type.
                 *)
                v
                |> wrapMessages Var (lookupVar env)
                |> bind (function
                         | Typed.Bool vn -> vn |> varF |> Reg |> BVar |> ok
                         | _ -> v |> VarNotBoolean |> fail)
            | Symbolic (sym, args) ->
                args
                |> List.map me
                |> collect
                |> lift (func sym >> Sym >> BVar)
            | BopExpr(BoolOp as op, l, r) ->
                match op with
                | ArithIn as o ->
                    lift2 (match o with
                           | Gt -> mkGt
                           | Ge -> mkGe
                           | Le -> mkLe
                           | Lt -> mkLt
                           | _ -> failwith "unreachable[modelBool::ArithIn]")
                          (mi l)
                          (mi r)
                | BoolIn as o ->
                    lift2 (match o with
                           | And -> mkAnd2
                           | Or -> mkOr2
                           | Imp -> mkImpl
                           | _ -> failwith "unreachable[modelBool::BoolIn]")
                          (mb l)
                          (mb r)
                | AnyIn as o ->
                    lift2 (match o with
                           | Eq -> mkEq
                           | Neq -> mkNeq
                           | _ -> failwith "unreachable[modelBool::AnyIn]")
                          (me l)
                          (me r)
            | _ -> fail ExprNotBoolean
        mb

    /// <summary>
    ///     Models a Starling integral expression as an <c>IntExpr</c>.
    ///
    ///     <para>
    ///         See <c>modelExpr</c> for more information.
    ///     </para>
    /// </summary>
    /// <param name="env">
    ///     The <c>VarMap</c> of variables bound where this expression
    ///     occurs.  Usually, but not always, these are the thread-local
    ///     variables.
    /// </param>
    /// <param name="varF">
    ///     A function to transform any variables after they are looked-up,
    ///     but before they are placed in <c>AVar</c>.  Use this to apply
    ///     markers on variables, etc.
    /// </param>
    /// <typeparam name="var">
    ///     The type of variables in the <c>IntExpr</c>, achieved by
    ///     applying <paramref name="varF"/> to <c>Var</c>s.
    /// </typeparam>
    /// <returns>
    ///     A function, taking <c>Expression</c>s previously judged as
    ///     integral.  This function will return a <c>Result</c>, over
    ///     <c>Expr.Error</c>, containing the modelled <c>IntExpr</c> on
    ///     success.  The exact type parameters of the expression depend on
    ///     <paramref name="varF"/>.
    /// </returns>
    and modelInt
      (env : VarMap)
      (varF : Var -> 'var)
      : Expression -> Result<IntExpr<Sym<'var>>, Error> =
        let me = model env varF

        let rec mi e =
            match e.Node with
            | Num i -> i |> AInt |> ok
            | LV v ->
                (* Look-up the variable to ensure it a) exists and b) is of an
                 * arithmetic type.
                 *)
                v
                |> wrapMessages Var (lookupVar env)
                |> bind (function
                         | Typed.Int vn -> vn |> varF |> Reg |> AVar |> ok
                         | _ -> v |> VarNotInt |> fail)
            | Symbolic (sym, args) ->
                args
                |> List.map me
                |> collect
                |> lift (func sym >> Sym >> AVar)
            | BopExpr(ArithOp as op, l, r) ->
                lift2 (match op with
                       | Mul -> mkMul2
                       | Div -> mkDiv
                       | Add -> mkAdd2
                       | Sub -> mkSub2
                       | _ -> failwith "unreachable[modelInt]")
                      (mi l)
                      (mi r)
            | _ -> fail ExprNotInt
        mi


    module Pretty =
        open Starling.Core.Pretty
        open Starling.Core.Symbolic.Pretty
        open Starling.Core.Var.Pretty
        open Starling.Lang.AST.Pretty

        /// Pretty-prints expression conversion errors.
        let printError : Error -> Doc =
            function
            | ExprNotBoolean ->
                "expression is not suitable for use in a Boolean position" |> String
            | VarNotBoolean lv ->
                fmt "lvalue '{0}' is not a suitable type for use in a Boolean expression" [ printLValue lv ]
            | ExprNotInt ->
                "expression is not suitable for use in an integral position" |> String
            | VarNotInt lv ->
                fmt "lvalue '{0}' is not a suitable type for use in an integral expression" [ printLValue lv ]
            | Var(var, err) -> wrapped "variable" (var |> printLValue) (err |> printVarMapError)
            | AmbiguousSym sym ->
                fmt
                    "symbolic var '{0}' has ambiguous type: \
                     place it inside an expression with non-symbolic components"
                    [ printSymbol sym ]
