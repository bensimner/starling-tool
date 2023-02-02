﻿/// <summary>
///    The abstract syntax tree for the Starling language.
/// </summary>
module Starling.Lang.AST

open Starling
open Starling.Collections
open Starling.Core.Symbolic
open Starling.Core.TypeSystem
open Starling.Core.Var.Types


/// <summary>
///     Types used in the AST.
/// </summary>
[<AutoOpen>]
module Types =
    /// A Boolean operator.
    type BinOp =
        | Mul // a * b
        | Div // a / b
        | Mod // a % b
        | Add // a + b
        | Sub // a - b
        | Gt // a > b
        | Ge // a >= b
        | Le // a <= b
        | Lt // a < b
        | Imp // a => b
        | Eq // a == b
        | Neq // a != b
        | And // a && b
        | Or // a || b

    /// A unary operator.
    type UnOp =
        | Neg // ! a

    /// An untyped, raw expression.
    /// These currently cover all languages, but this may change later.
    type Expression' =
        | True // true
        | False // false
        | Num of int64 // 42
        | Identifier of string // foobaz
        | Symbolic of Symbolic<Expression> // %{foo}(exprs)
        | BopExpr of BinOp * Expression * Expression // a BOP b
        | UopExpr of UnOp * Expression // UOP a
        | ArraySubscript of array : Expression * subscript : Expression
    and Expression = Node<Expression'>

    /// <summary>
    ///     A primitive command.
    /// </summary>
    type Prim' =
        | CompareAndSwap of
            src : Expression
            * test : Expression
            * dest : Expression // <CAS(a, b, c)>
        | Fetch of Expression * Expression * FetchMode // <a = b??>
        | Postfix of Expression * FetchMode // <a++> or <a-->
        | Assume of Expression // <assume(e)>
        | SymCommand of symbol : Symbolic<Expression> // %{xyz}(x, y)
        | Havoc of var : string // havoc var
    and Prim = Node<Prim'>

    /// <summary>
    ///     An atomic action.
    /// </summary>
    type Atomic' =
        /// <summary>An atomic primitive.</summary>
        | APrim of Prim
        /// <summary>
        ///     A failure command.
        ///     This is semantically equivalent to <c>AAssert False</c>.
        /// </summary>
        | AError
        /// <summary>An assertion.</summary>
        | AAssert of cond : Expression
        /// <summary>An atomic conditional.</summary>
        | ACond of
            cond : Expression
            * trueBranch : Atomic list
            * falseBranch : (Atomic list) option
    and Atomic = Node<Atomic'>

    /// <summary>
    ///     A view, annotated with additional syntax.
    ///
    ///     <para>
    ///         This is modelled as Starling's <c>ViewExpr</c>, which
    ///         cannot be <c>Unknown</c>.
    ///     </para>
    /// </summary>
    /// <typeparam name="view">
    ///     The type of view wrapped inside this expression.
    /// </typeparam>
    type Marked<'view> =
        /// <summary>
        ///     An unannotated view.
        /// </summary>
        | Unmarked of 'view
        /// <summary>
        ///     A ?-annotated view.
        /// </summary>
        | Questioned of 'view
        /// <summary>
        ///     An unknown view.
        /// </summary>
        | Unknown

    /// An AST func.
    type AFunc = Func<Expression>

    /// A function view definition
    type StrFunc = Func<string>

    /// <summary>
    ///     An AST type literal.
    ///     <para>
    ///         This is kept separate from the Starling type system to allow
    ///         it to become more expressive later on (eg typedefs).
    ///     </para>
    /// </summary>
    type TypeLiteral =
        /// <summary>An integer type.</summary>
        | TInt
        /// <summary>A Boolean type.</summary>
        | TBool
        /// <summary>An unknown, and probably user-defined, type.</summary>
        | TUser of name : string
        /// <summary>An array type.</summary>
        | TArray of length : int * contentT : TypeLiteral

    /// <summary>
    ///     An AST formal parameter declaration.
    /// </summary>
    type Param =
        { /// <summary>The type of the parameters.</summary>
          ParamType : TypeLiteral
          /// <summary>The names of the parameters.</summary>
          ParamName : string
        }

    /// A view prototype.
    type GeneralViewProto<'Param> =
        /// <summary>
        ///     A non-iterated view prototype; can be anonymous.
        /// </summary>
        | NoIterator of Func : Func<'Param> * IsAnonymous : bool
        /// <summary>
        ///     An iterated view prototype; cannot be anonymous
        /// </summary>
        | WithIterator of Func: Func<'Param>

    /// A view prototype with Param parameters.
    type ViewProto = GeneralViewProto<Param>

    /// A view as seen on the LHS of a ViewDef.
    type ViewSignature =
        | Unit
        | Join of ViewSignature * ViewSignature
        | Func of StrFunc
        | Iterated of StrFunc * string

    /// <summary>
    ///     An AST variable declaration.
    /// </summary>
    type VarDecl =
        { /// <summary>The type of the variables.</summary>
          VarType : TypeLiteral
          /// <summary>The names of the variables.</summary>
          VarNames : string list
        }

    /// A view.
    type View =
          /// <summary>The unit view, `emp`.</summary>
        | Unit
          /// <summary>The always-false view, `false`.</summary>
        | Falsehood
          /// <summary>A `*`-conjunction of two views.</summary>
        | Join of View * View
          /// <summary>An abstract-predicate view.</summary>
        | Func of AFunc
          /// <summary>A local view, `local { P }`.</summary>
        | Local of Expression
          /// <summary>A conditional view, `if P { V1 } [else { V2 }]`.</summary>
        | If of Expression * View * View option

    /// A set of primitives.
    type PrimSet<'Atomic> =
        { PreLocals: Prim list
          Atomics: 'Atomic list
          PostLocals: Prim list }

    /// A statement in the command language.
    type Command' =
        /// A view expression.
        | ViewExpr of Marked<View>
        /// <summary>A variable declaration.</summary>
        | VarDecl of VarDecl
        /// <summary>
        ///     A miracle command.
        ///     Miracles atomically establish their postcondition.
        /// </summary>
        | Miracle
        /// A set of sequentially composed primitives.
        | Prim of PrimSet<Atomic>
        /// An if-then-else statement, with optional else.
        /// If 'ifCond' is missing, then this is a nondeterministic choice.
        | If of ifCond : Expression option
              * thenBlock : Command list
              * elseBlock : Command list option
        /// A while loop.
        | While of Expression * Command list
        /// A do-while loop.
        | DoWhile of Command list
                   * Expression // do { b } while (e)
        /// A list of parallel-composed blocks.
        | Blocks of Command list list
    and Command = Node<Command'>

    /// A method.
    type Method<'cmd> =
        { Signature : Func<Param> // main (argv, argc) ...
          Body : 'cmd list } // ... { ... }

    /// <summary>A GRASShopper-specific directive.</summary>
    type GrasshopperPragma =
        | ///<summary>An include.</summary>
          Include of file : string

    /// <summary>
    ///     A directive for adding backend-specific information.
    /// </summary>
    type Pragma =
        { ///<summary>The key of the pragma.</summary>
          Key : string
          ///<summary>The value of the pragma.</summary>
          Value : string }

    /// A top-level item in a Starling script.
    type ScriptItem' =
        | Pragma of Pragma // pragma ...;
        | Typedef of TypeLiteral * string // typedef int Node;
        | SharedVars of VarDecl // shared int name1, name2, name3;
        | ThreadVars of VarDecl // thread int name1, name2, name3;
        | Method of Method<Command> // method main(argv, argc) { ... }
        | Search of int // search 0;
        | ViewProtos of ViewProto list // view name(int arg);
        | Constraint of ViewSignature * Expression option // constraint emp => true
        | Exclusive of List<StrFunc> // exclusive p(x), q(x), r(x)
        | Disjoint of List<StrFunc> // disjoint p(x), q(x), r(x)
        override this.ToString() = sprintf "%A" this
    and ScriptItem = Node<ScriptItem'>

/// <summary>
///     Pretty printers for the AST.
/// </summary>
module Pretty =
    open Starling.Collections.Func.Pretty
    open Starling.Core.Pretty
    open Starling.Core.Symbolic.Pretty
    open Starling.Core.TypeSystem.Pretty
    open Starling.Core.Var.Pretty

    /// <summary>
    ///     Hidden building-blocks for AST pretty-printers.
    /// </summary>
    module private Helpers =
        /// Pretty-prints blocks with the given indent level (in spaces).
        /// This does not include the curly braces.
        let printBlock (pCmd : 'Cmd -> Doc) (c : 'Cmd list) : Doc =
            ivsep (List.map (pCmd >> Indent) c)


    /// Pretty-prints Boolean operations.
    let printBinOp : BinOp -> Doc =
        function
        | Mul -> "*"
        | Div -> "/"
        | Mod -> "%"
        | Add -> "+"
        | Sub -> "-"
        | Gt -> ">"
        | Ge -> ">="
        | Le -> "<="
        | Lt -> "<"
        | Imp -> "=>"
        | Eq -> "=="
        | Neq -> "!="
        | And -> "&&"
        | Or -> "||"
        >> String >> syntax

    let printUnOp : UnOp -> Doc =
        function
        | Neg -> "!"
        >> String >> syntax

    /// Pretty-prints expressions.
    /// This is not guaranteed to produce an optimal expression.
    let rec printExpression' (expr : Expression') : Doc =
        match expr with
        | True -> String "true" |> syntaxLiteral
        | False -> String "false" |> syntaxLiteral
        | Num i -> i.ToString() |> String |> syntaxLiteral
        | Identifier x -> syntaxIdent (String x)
        | Symbolic sym -> printSymbolic sym
        | BopExpr(op, a, b) ->
            hsep [ printExpression a
                   printBinOp op
                   printExpression b ]
            |> parened
        | UopExpr(op, a) ->
            hsep [ printUnOp op
                   printExpression a ]
        | ArraySubscript (array, subscript) ->
            printExpression array <-> squared (printExpression subscript)
    and printExpression (x : Expression) : Doc = printExpression' x.Node
    /// <summary>
    ///     Pretty-prints a symbolic without interpolation.
    /// </summary>
    /// <param name="s">The symbolic to print.</param>
    /// <returns>
    ///     The <see cref="Doc"/> resulting from printing <paramref name="s"/>.
    /// </returns>
    and printSymbolic (s : Symbolic<Expression>) : Doc =
        String "%"
        <->
        braced (Starling.Core.Symbolic.Pretty.printSymbolic printExpression s)

    /// <summary>
    ///     Pretty-prints an if-then-else-like construct.
    /// </summary>
    /// <param name="pLeg">Pretty-printer for 'then'/'else' legs.</param>
    /// <param name="cond">The conditional to print.</param>
    /// <param name="thenLeg">The 'then' leg to print.</param>
    /// <param name="elseLeg">The optional 'else' leg to print.</param>
    /// <typeparam name="Leg">Type of 'then'/'else' leg items.</typeparam>
    /// <returns>
    ///     A <see cref="Doc"/> capturing the if-then-else form.
    /// </returns>
    let printITELike
        (pCond : 'Cond -> Doc)
        (pLeg : 'Leg -> Doc)
        (cond : 'Cond)
        (thenLeg : 'Leg)
        (elseLeg : 'Leg option)
        : Doc =
        syntaxStr "if"
        <+> pCond cond
        <+> braced (pLeg thenLeg)
        <+> (maybe
                Nop
                (fun e -> syntaxStr "else" <+> braced (pLeg e))
                    elseLeg)

    /// <summary>
    ///     Pretty-prints an if-then-else.
    /// </summary>
    /// <param name="pCond">Pretty-printer for conditions.</param>
    /// <param name="pCmd">Pretty-printer for commands.</param>
    /// <param name="cond">The conditional to print.</param>
    /// <param name="thenCmds">The 'then' leg to print.</param>
    /// <param name="elseCmds">The optional 'else' leg to print.</param>
    /// <typeparam name="Cmd">Type of commands</typeparam>
    /// <returns>
    ///     A <see cref="Doc"/> capturing the if-then-else form.
    /// </returns>
    let printITE
        (pCond : 'Cond -> Doc)
        (pCmd : 'Cmd -> Doc)
        (cond : 'Cond)
        (thenCmds : 'Cmd list)
        (elseCmds : ('Cmd list) option)
        : Doc =
            printITELike pCond (Helpers.printBlock pCmd) cond thenCmds elseCmds


    /// Pretty-prints views.
    let rec printView : View -> Doc =
        function
        | View.Func f -> printFunc printExpression f
        | View.Unit -> String "emp" |> syntaxView
        | View.Falsehood -> String "false" |> syntaxView
        | View.Join(l, r) -> binop "*" (printView l) (printView r)
        | View.If(e, l, r) -> printITELike printExpression printView e l r
        | View.Local l -> syntaxView (String "local") <+> braced (printExpression l)

    /// Pretty-prints marked view lines.
    let rec printMarkedView (pView : 'view -> Doc) : Marked<'view> -> Doc =
        function
        | Unmarked v -> pView v
        | Questioned v -> hjoin [ pView v ; String "?" |> syntaxView ]
        | Unknown -> String "?" |> syntaxView
        >> ssurround "{| " " |}"

    /// Pretty-prints view definitions.
    let rec printViewSignature : ViewSignature -> Doc =
        function
        | ViewSignature.Func f -> printFunc String f
        | ViewSignature.Unit -> String "emp" |> syntaxView
        | ViewSignature.Join(l, r) -> binop "*" (printViewSignature l) (printViewSignature r)
        | ViewSignature.Iterated(f, e) -> hsep [String "iter" |> syntaxView; hjoin [String "[" |> syntaxView; String e; String "]" |> syntaxView]; printFunc String f]

    /// Pretty-prints constraints.
    let printConstraint (view : ViewSignature) (def : Expression option) : Doc =
        hsep [ String "constraint" |> syntax
               printViewSignature view
               String "->" |> syntax
               (match def with
                | Some d -> printExpression d
                | None _ -> String "?" |> syntax) ]
        |> withSemi

    /// Pretty-prints exclusivity constraints.
    let printExclusive (xs : List<StrFunc>) : Doc =
        hsep ((String "exclusive") ::
              (List.map (printFunc String) xs))
        |> withSemi

    /// Pretty-prints exclusivity constraints.
    let printDisjoint (xs : List<StrFunc>) : Doc =
        hsep ((String "disjoint") ::
              (List.map (printFunc String) xs))
        |> withSemi

    /// Pretty-prints fetch modes.
    let printFetchMode : FetchMode -> Doc =
        function
        | Direct -> Nop
        | Increment -> String "++"
        | Decrement -> String "--"

    /// Pretty-prints local assignments.
    let printAssign (dest : Expression) (src : Expression) : Doc =
        equality (printExpression dest) (printExpression src)

    /// <summary>
    ///     Pretty-prints primitive actions.
    /// </summary>
    /// <param name="p">The <see cref="Prim'"/> to print.</param>
    /// <returns>
    ///     A <see cref="Doc"/> representing <paramref name="p"/>.
    /// </returns>
    let rec printPrim' (p : Prim') : Doc =
        match p with
        | CompareAndSwap(l, f, t) ->
            func "CAS" [ printExpression l
                         printExpression f
                         printExpression t ]
        | Fetch(l, r, m) ->
            equality
                (printExpression l)
                (hjoin [ printExpression r; printFetchMode m ])
        | Postfix(l, m) ->
            hjoin [ printExpression l; printFetchMode m ]
        | Assume e -> func "assume" [ printExpression e ]
        | SymCommand sym -> printSymbolic sym
        | Havoc var -> String "havoc" <+> String var
    and printPrim (x : Prim) : Doc = printPrim' x.Node

    /// <summary>
    ///     Pretty-prints atomic actions.
    /// </summary>
    /// <param name="a">The <see cref="Atomic'"/> to print.</param>
    /// <returns>
    ///     A <see cref="Doc"/> representing <paramref name="a"/>.
    /// </returns>
    let rec printAtomic' (a : Atomic') : Doc =
        match a with
        | APrim p -> printPrim p
        | AError -> syntaxStr "error"
        | AAssert e -> syntaxStr "assert" <+> parened (printExpression e)
        | ACond (cond = c; trueBranch = t; falseBranch = f) ->
            printITE printExpression printAtomic c t f
    and printAtomic (x : Atomic) : Doc = printAtomic' x.Node

    /// <summary>
    ///     Pretty-prints a type literal.
    /// </summary>
    /// <param name="lit">The <see cref="TypeLiteral"/> to print.</param>
    /// <returns>
    ///     A <see cref="Doc"/> representing the given type literal.
    /// </returns>
    let printTypeLiteral (lit : TypeLiteral) : Doc =
        let rec pl lit suffix =
            match lit with
            | TInt -> syntaxIdent (String ("int")) <-> suffix
            | TBool -> syntaxIdent (String ("bool")) <-> suffix
            | TUser s -> syntaxLiteral (String s) <-> suffix
            | TArray (len, contents) ->
                let lenSuffix = squared (String (sprintf "%d" len))
                pl contents (suffix <-> lenSuffix)
        pl lit Nop

    /// Pretty-prints parameters.
    let printParam (par : Param) : Doc =
        hsep
            [ printTypeLiteral par.ParamType
              syntaxLiteral (String par.ParamName) ]

    /// Pretty-prints a variable declaration, without semicolon.
    let printVarDecl (vs : VarDecl) : Doc =
        let vsp = commaSep (List.map printVar vs.VarNames)
        hsep [ printTypeLiteral vs.VarType; vsp ]

    /// Pretty-prints if-then-else conditions.
    let printCondition (cond : Expression option) : Doc =
        maybe (syntaxStr "*") printExpression cond

    /// Pretty-prints commands.
    let rec printCommand' (cmd : Command') : Doc =
        match cmd with
        (* The trick here is to make Prim [] appear as ;, but
           Prim [x; y; z] appear as x; y; z;, and to do the same with
           atomic lists. *)
        | Command'.Prim { PreLocals = ps; Atomics = ts; PostLocals = qs } ->
            seq { yield! Seq.map printPrim ps
                  yield (ts
                         |> Seq.map printAtomic
                         |> semiSep |> withSemi |> braced |> angled)
                  yield! Seq.map printPrim qs }
            |> semiSep |> withSemi
        | Command'.Miracle -> syntaxStr "..."
        | Command'.If(c, t, f) ->
            printITE printCondition printCommand c t f
        | Command'.While(c, b) ->
            hsep [ "while" |> String |> syntax
                   c |> printExpression |> parened
                   b |> Helpers.printBlock printCommand ]
        | Command'.DoWhile(b, c) ->
            hsep [ "do" |> String |> syntax
                   b |> Helpers.printBlock printCommand
                   "while" |> String |> syntax
                   c |> printExpression |> parened ]
            |> withSemi
        | Command'.Blocks bs ->
            bs
            |> List.map (Helpers.printBlock printCommand)
            |> hsepStr "||"
        | Command'.ViewExpr v -> printMarkedView printView v
        | Command'.VarDecl vs ->
            withSemi (syntaxStr "thread" <+> printVarDecl vs)
    and printCommand (x : Command) : Doc = printCommand' x.Node

    /// <summary>
    ///     Prints a command block.
    /// </summary>
    /// <param name="block">The block to print.</param>
    /// <returns>A <see cref="Doc"/> capturing <paramref name="block"/>.
    let printCommandBlock (block : Command list) : Doc =
        Helpers.printBlock printCommand block

    /// Pretty-prints methods.
    let printMethod (pCmd : 'cmd -> Doc)
                    ({ Signature = s; Body = b } : Method<'cmd>)
                    : Doc =
        hsep [ "method" |> String |> syntax
               printFunc (printParam >> syntaxIdent) s
               Helpers.printBlock pCmd b ]

    /// Pretty-prints a general view prototype.
    let printGeneralViewProto (pParam : 'Param -> Doc)(vp : GeneralViewProto<'Param>) : Doc =
        match vp with
        | NoIterator (Func = { Name = n; Params = ps }; IsAnonymous = _) ->
            func n (List.map pParam ps)
        | WithIterator (Func = { Name = n; Params = ps }) ->
            (String "iter")
            <+> func n (List.map pParam ps)

    /// Pretty-prints a view prototype.
    let printViewProtoList (vps : ViewProto list) : Doc =
        hsep [ syntax (String "view")
               commaSep (List.map (printGeneralViewProto printParam) vps) ]
        |> withSemi

    /// Pretty-prints a search directive.
    let printSearch (i : int) : Doc =
        hsep [ String "search" |> syntax
               sprintf "%d" i |> String ]

    /// Pretty-prints a script variable list of the given class.
    let printScriptVars (cls : string) (vs : VarDecl) : Doc =
        withSemi (hsep [ String cls |> syntax; printVarDecl vs ])

    /// <summary>Prints a pragma.</summary>
    /// <param name="pragma">The pragma to print.</summary>
    /// <returns>
    ///     A <see cref="Doc"/> for printing <paramref name="pragma"/>.
    /// </returns>
    let printPragma (pragma : Pragma) : Doc =
        String pragma.Key <+> braced (String pragma.Value)

    /// Pretty-prints script lines.
    let printScriptItem' (item : ScriptItem') : Doc =
        match item with
        | Pragma p -> withSemi (printPragma p)
        | Typedef (ty, name) ->
            withSemi (syntaxIdent (String "typedef") <+> printTypeLiteral ty <+> String name)
        | SharedVars vs -> printScriptVars "shared" vs
        | ThreadVars vs -> printScriptVars "thread" vs
        | Method m ->
            fun mdoc -> vsep [Nop; mdoc; Nop]
            <| printMethod printCommand m
        | ViewProtos v -> printViewProtoList v
        | Search i -> printSearch i
        | Constraint (view, def) -> printConstraint view def
        | Exclusive xs -> printExclusive xs
        | Disjoint xs -> printDisjoint xs
    let printScriptItem (x : ScriptItem) : Doc = printScriptItem' x.Node

    /// Pretty-prints scripts.
    /// each line on its own line
    let printScript (xs : ScriptItem list) : Doc =
        VSep (List.map printScriptItem xs, Nop)


(*
 * Expression classification
 *)

/// Active pattern classifying bops as to whether they create
/// arithmetic or Boolean expressions.
let (|ArithOp|BoolOp|) : BinOp -> Choice<unit, unit> =
    function
    | Mul | Div | Add | Sub | Mod -> ArithOp
    | Gt | Ge | Le | Lt | Imp -> BoolOp
    | Eq | Neq -> BoolOp
    | And | Or -> BoolOp

/// Active pattern classifying bops as to whether they take in
/// arithmetic, Boolean, or indeterminate operands.
let (|ArithIn|BoolIn|AnyIn|) : BinOp -> Choice<unit, unit, unit> =
    function
    | Mul | Div | Add | Sub | Mod -> ArithIn
    | Gt | Ge | Le | Lt -> ArithIn
    | Eq | Neq -> AnyIn
    | And | Or | Imp -> BoolIn

/// Active pattern classifying inner expressions as to whether they are
/// arithmetic, Boolean, or indeterminate.
let (|BoolExp'|ArithExp'|AnyExp'|) (e : Expression')
  : Choice<Expression', Expression', Expression'> =
    match e with
    | Identifier _ -> AnyExp' e
    | Symbolic _ -> AnyExp' e
    | ArraySubscript _ -> AnyExp' e
    | Num _ -> ArithExp' e
    | True | False -> BoolExp' e
    | BopExpr(BoolOp, _, _) | UopExpr(_) -> BoolExp' e
    | BopExpr(ArithOp, _, _) -> ArithExp' e

/// Active pattern classifying expressions as to whether they are
/// arithmetic, Boolean, or indeterminate.
let (|BoolExp|ArithExp|AnyExp|) (e : Expression)
  : Choice<Expression, Expression, Expression> =
    match e.Node with
    | BoolExp' _ -> BoolExp e
    | ArithExp' _ -> ArithExp e
    | AnyExp' _ -> AnyExp e

/// <summary>
///     Active pattern classifying expressions as lvalues or rvalues.
/// </summary>
let (|LValue|RValue|) (e : Expression) : Choice<Expression, Expression> =
    match e.Node with
    (* TODO(CaptainHayashi): symbolic lvalues?
       These, however, need a lot of thought as to what the framing semantics
       are. *)
    | Identifier _ | ArraySubscript _ -> LValue e
    | _ -> RValue e

(*
 * Misc
 *)
let emptyPosition : SourcePosition =
    { StreamName = ""; Line = 0L; Column = 0L; }
let freshNode (a : 'a) : Node<'a> =
  { Position = emptyPosition; Node = a }
let node (streamname : string)
         (line : int64)
         (column : int64)
         (a : 'a)
         : Node<'a> =
    { Position = { StreamName = streamname; Line = line; Column = column }; Node = a }
