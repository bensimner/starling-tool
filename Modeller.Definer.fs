namespace Starling.Lang.Modeller

open Chessie.ErrorHandling

open Starling.Collections
open Starling.Utils
open Starling.Lang
open Starling.Lang.AST
open Starling.Lang.Collator
open Starling.Lang.Modeller.Expr
open Starling.Lang.Modeller.View
open Starling.Core
open Starling.Core.Expr
open Starling.Core.TypeSystem
open Starling.Core.Model
open Starling.Core.Var
open Starling.Core.View
open Starling.Core.Symbolic


/// <summary>
///     The part of the modeller responsible for constructing definers.
/// </summary>
module Definer =
    /// <summary>
    ///     Internal context for the definer modeller.
    /// </summary>
    type Context =
        { /// <summary>
          ///     The environment of visible shared variables.
          /// </summary>
          SharedVars : VarMap
          /// <summary>
          ///     A definer containing the visible view prototypes.
          /// </summary>
          ViewProtos : FuncDefiner<ProtoInfo>
          /// <summary>
          ///     The search depth of this model.
          /// </summary>
          Search : int option }

    /// <summary>
    ///     Represents an error when creating a definer.
    /// </summary>
    type Error =
        /// The view definition in the constraint generated a `View.Error`.
        | CEView of vdef : AST.Types.ViewSignature * err : View.Error
        /// The expression in the constraint generated an `Expr.Error`.
        | CEExpr of expr : AST.Types.Expression * err : Expr.Error


    /// Models part of a view definition as a DFunc.
    let modelDFunc
      (protos : FuncDefiner<ProtoInfo>)
      (func : Func<Var>)
      : Result<Multiset<DFunc>, View.Error> =
        func
        |> lookupFunc protos
        |> lift (fun proto ->
                     dfunc func.Name (funcViewParMerge proto.Params func.Params)
                     |> Multiset.singleton)

    /// Tries to convert a view def into its model (multiset) form.
    let rec modelViewSignature (protos : FuncDefiner<ProtoInfo>) =
        function
        | ViewSignature.Unit -> ok Multiset.empty
        | ViewSignature.Func dfunc -> Multiset.map (fun f -> { Func = f; Iterator = None }) <!> (modelDFunc protos dfunc)
        | ViewSignature.Join(l, r) -> trial { let! lM = modelViewSignature protos l
                                              let! rM = modelViewSignature protos r
                                              return Multiset.append lM rM }
        | ViewSignature.Iterated(dfunc, e) ->
            let updateFunc (s : string) f = { Func = f; Iterator = Some (Int s) }
            let modelledDFunc = modelDFunc protos dfunc
            (Multiset.map (updateFunc e)) <!> modelledDFunc

    let makeIteratorMap : TypedVar option -> VarMap =
        function
        | None         -> Map.empty
        | Some (Int v) -> Map.add v (Type.Int ()) Map.empty
        | _            -> failwith "Iterator in iterated views must be Int type"

    /// Produces the environment created by interpreting the viewdef vds using the
    /// view prototype map vpm.
    let rec localEnvOfViewDef vds =
        vds
        |> Seq.ofList
        |> Seq.map (fun { Func = {Params = ps}; Iterator = it } -> makeVarMap ps >>= (combineMaps (makeIteratorMap it)))
        |> seqBind (fun xR s -> bind (combineMaps s) xR) Map.empty
        |> mapMessages Modeller.View.Error.BadVar

    /// Produces the variable environment for the constraint whose viewdef is v.
    let envOfViewDef : VarMap -> DView -> Result<VarMap, Modeller.View.Error> =
        fun svars -> localEnvOfViewDef >> bind (combineMaps svars >> mapMessages SVarConflict)

    /// Converts a single constraint to its model form.
    let modelViewDef
      ({ SharedVars = svars ; ViewProtos = vprotos } : Context)
      (av : ViewSignature, ad : Expression option)
      : Result<(DView * BoolExpr<Sym<Var>> option), Error> =
        trial {
            let! vms = wrapMessages CEView (modelViewSignature vprotos) av
            let  v = vms |> Multiset.toFlatList
            let! e = envOfViewDef svars v |> mapMessages (curry CEView av)
            let! d = (match ad with
                      | Some dad ->
                          dad
                          |> wrapMessages CEExpr (Modeller.Expr.modelBool e id)
                          |> lift Some
                      | None _ -> ok None)
            return (v, d)
        }

    /// <summary>
    ///     Checks whether a <c>DView</c> can be found in a definer.
    /// </summary>
    /// <param name="definer">
    ///     The existing definer.
    /// </param>
    /// <param name="dview">
    ///     The <c>DView</c> to check.
    /// </param>
    /// <returns>
    ///     <c>true</c> if the <c>DView</c> has been found in the definer.
    ///     This is a weak equality based on view names: see the remarks.
    /// </returns>
    /// <remarks>
    ///     <para>
    ///         We perform no sanity checking here.  It is assumed that, if the
    ///         view prototypes and defining views don't match, we will have
    ///         caught them in the main defining view modeller.
    ///     </para>
    /// </remarks>
    let inDefiner : ViewDefiner<SVBoolExpr option> -> DView -> bool =
        fun definer dview ->
            definer
            |> ViewDefiner.toSeq
            |> Seq.toList
            |> List.map fst
            |> List.exists
                   (fun view ->
                        if (List.length view = List.length dview)
                        then
                            List.forall2
                                (fun (vdfunc : IteratedContainer<DFunc, TypedVar>) (dfunc : IteratedContainer<DFunc, TypedVar>) -> vdfunc.Func.Name = dfunc.Func.Name)
                                view
                                dview
                        else false)

    /// <summary>
    ///     Converts a <c>DView</c> to an indefinite <c>ViewDef</c>.
    ///
    ///     <para>
    ///         This instantiates the <c>DView</c> with fresh parameter
    ///         names, and sets its definition to <c>None</c>.
    ///     </para>
    /// </summary>
    /// <param name="dview">
    ///     The <c>DView</c> to convert.
    /// </param>
    /// <returns>
    ///     An indefinite constraint over <paramref name="dview" />.
    /// </returns>
    let searchViewToConstraint
      (dview : DView)
      : (DView * SVBoolExpr option) =
        (* To ensure likewise-named parameters in separate DFuncs don't
           clash, append fresh identifiers to all of them.

           We don't use the parameter names anyway, so this is ok.

           Do _NOT_ make dview implicit, it causes freshGen () to evaluate only
           once for the entire function (!), ruining everything. *)
        let fg = freshGen ()

        let dview' =
            List.map
                (fun { Func = { Name = name; Params = ps }; Iterator = it } ->
                     let nps =
                         List.map
                             (fun p ->
                                 (withType
                                     (typeOf p)
                                        (sprintf "%s%A" (valueOf p) (getFresh fg))))
                             ps
                     { Func = { Name = name; Params = nps }; Iterator = it })
                dview

        (dview', None)

    /// <summary>
    ///     Generates all views of the given size, from the given funcs.
    /// </summary>
    /// <param name="depth">
    ///     The size of views to generate.
    /// </param>
    /// <param name="funcs">
    ///     The pool of <c>Func</c>s to use when building views.
    /// </param>
    /// <returns>
    ///     A set of all <c>View</c>s of maximum size <paramref name="depth" />,
    ///     whose <c>Func</c>s are taken from <paramref name="funcs" />
    /// </returns>
    let genAllViewsAt (depth : int) (funcs : DFunc seq) : Set<DView> =
        let rec f depth existing =
            match depth with
            // Multiset and set conversion removes duplicate views.
            // TODO(CaptainHayashi): remove the multiset conversion somehow.
            | 0 ->
                existing
                |> Seq.map (Multiset.ofFlatList >> Multiset.toFlatList)
                |> Set.ofSeq
            | n ->
                let existing' =
                    seq { yield []
                          for f in funcs do
                              for e in existing do
                                  yield {Iterator = None; Func = f} :: e }
                f (depth - 1) existing'
        f depth (Seq.singleton [])

    /// <summary>
    ///     Completes a viewdef list by generating indefinite constraints of size
    ///     <paramref name="depth" />.
    /// </summary>
    /// <param name="vprotos">
    ///     The map of view prototypes to use in the generated constraints.
    /// </param>
    /// <param name="depth">
    ///     The maximum view size to represent in the viewdef list.
    ///     A depth of 0 causes no new constraints to be generated.
    /// </param>
    /// <param name="viewdefs">
    ///     The existing viewdef list.
    /// </param>
    /// <returns>
    ///     If <paramref name="depth" /> is <c>None</c>, <paramref name="viewdefs" />.
    ///     Else, <paramref name="viewdefs" /> extended with indefinite
    ///     constraints for all views of size <paramref name="depth" />
    ///     generated from the views at <paramref name="vprotos" />.
    /// </returns>
    let addSearchDefs
      ({ ViewProtos = vprotos; Search = depth } : Context)
      (definer : ViewDefiner<BoolExpr<Sym<Var>> option>)
        : ViewDefiner<BoolExpr<Sym<Var>> option> =
        match depth with
        | None -> definer
        | Some n ->
            vprotos
            // Convert the definer back into a list of funcs.
            |> FuncDefiner.toSeq
            |> Seq.map fst
            // Then, generate the view that is the *-conjunction of all of the
            // view protos.
            |> genAllViewsAt n
            // Then, throw out any views that already exist in viewdefs...
            |> Set.filter (inDefiner definer >> not)
            // Finally, convert the view to a constraint.
            |> Set.toList
            |> Seq.map searchViewToConstraint
            // And add the result to the original definer.
            |> Seq.append (ViewDefiner.toSeq definer)
            |> ViewDefiner.ofSeq

    /// Extracts the view definitions from a CollatedScript, turning each into a
    /// ViewDef.
    let model
      (ctx : Context)
      (cs : (ViewSignature * Expression option) list)
      : Result<ViewDefiner<BoolExpr<Sym<Var>> option>, Error> =
        cs
        |> List.map (modelViewDef ctx)
        |> collect
        |> lift (addSearchDefs ctx)


    module Pretty =
        open Starling.Core.Pretty
        open Starling.Lang.AST.Pretty

        /// Pretty-prints constraint conversion errors.
        let printError : Error -> Doc =
            function
            | CEView(vdef, err) ->
                wrapped "view definition"
                    (printViewSignature vdef)
                    (Starling.Lang.Modeller.View.Pretty.printError err)
            | CEExpr(expr, err) ->
                wrapped "expression"
                    (printExpression expr)
                    (Starling.Lang.Modeller.Expr.Pretty.printError err)
