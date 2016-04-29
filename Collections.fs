/// <summary>
///     Collections used in Starling.
/// </summary>
module Starling.Collections

open Chessie.ErrorHandling
open Starling.Utils

/// <summary>
///     A function-like construct.
/// </summary>
/// <remarks>
///     <para>
///         A Func is a combination of a string name and list of parameters.
///         It generically represents any pattern <c>Name(p1, p2, .., pn)</c>
///         in Starling.
///     </para>
///     <para>
///         Examples of Func uses in Starling include function signatures and
///         calls, components of <see cref="T:Starling.Model">views</see>, and
///         Horn clause predicates.
///     </para>
/// </remarks>
/// <typeparam name="param">The type of parameters in the Func.</typeparam>
type Func<'param> =
    { /// The name of a Func.
      Name : string
      /// The parameters of a Func.
      Params : 'param list }

/// <summary>
///     Creates a new <c>Func</c>.
/// </summary>
/// <parameter name="name">
///     The name of the <c>Func</c>.
/// </parameter>
/// <parameter name="pars">
///     The parameters of the <c>Func</c>, as a sequence.
/// </parameter>
/// <returns>
///     A new <c>Func</c> with the given name and parameters.
/// </returns>
let func name pars = { Name = name; Params = List.ofSeq pars }

/// <summary>
///     A multiset, or ordered list.
/// </summary>
/// <typeparam name="item">
///     The type of items in the Multiset.
/// </typeparam>
type Multiset<'item> when 'item: comparison =
    | MSet of Map<'item, int>
    override this.ToString() = sprintf "%A" this


/// <summary>
///     Operations on multisets.
/// </summary>
/// <seealso cref="T:Starling.Collections.Multiset`1" />
module Multiset =
    (*
     * Construction
     *)

    /// <summary>
    ///     The empty multiset.
    /// </summary>
    let empty = MSet (Map.empty)

    /// <summary>
    ///     Adds an element n times to a multiset
    /// </summary>
    let addn (MSet ms) k m =
        let n = ms.TryFind k |> Option.fold (fun x y -> y) 0
        MSet (ms.Add (k, n+m))

    /// <summary>
    ///     Adds an element to a multiset
    /// </summary>
    let add ms k = addn ms k 1

    /// <summary>
    ///     Creates a multiset with the given flat sequence as its contents.
    /// </summary>
    /// <param name="xs">
    ///     The flat sequence to use to create the multiset.
    /// </param>
    /// <returns>
    ///     A multiset containing the given items.
    /// </returns>
    let ofFlatSeq xs =
        Seq.fold add empty xs

    /// <summary>
    ///     Creates a multiset with the given flat list as its contents.
    /// </summary>
    /// <param name="xs">
    ///     The flat list to use to create the multiset.
    /// </param>
    /// <returns>
    ///     A multiset containing the given items.
    /// </returns>
    let ofFlatList (xs : List<_>) =
        xs |> ofFlatSeq

    /// <summary>
    ///     Creates a multiset with one item.
    /// </summary>
    /// <param name="x">
    ///     The item to place in the multiset.
    /// </param>
    /// <returns>
    ///     A singleton multiset.
    /// </returns>
    let singleton x = add empty x


    (*
     * Destruction
     *)

    /// <summary>
    ///     Converts a multiset to a sorted, flattened sequence.
    /// </summary>
    /// <param name="ms">
    ///     The multiset to convert.
    /// </param>
    /// <returns>
    ///     The sorted, flattened sequence.
    /// </returns>
    let toFlatSeq (MSet ms) =
        ms
        |> Map.toSeq
        |> Seq.map (fun (k, amount) -> Seq.replicate amount k)
        |> Seq.concat

    /// <summary>
    ///     Converts a multiset to a sorted, flattened list.
    /// </summary>
    /// <param name="ms">
    ///     The multiset to convert.
    /// </param>
    /// <returns>
    ///     The sorted, flattened list.
    /// </returns>
    let toFlatList ms =
        ms
        |> toFlatSeq
        |> List.ofSeq

    /// <summary>
    ///     Converts a multiset to a set, removing duplicates.
    /// </summary>
    /// <param name="ms">
    ///     The multiset to convert.
    /// </param>
    /// <returns>
    ///     The set of items in the multiset.
    /// </returns>
    let toSet (MSet ms) =
        Map.fold (fun set k n -> Set.add k set) Set.empty ms

    (*
     * Operations
     *)

    /// <summary>
    ///     Takes the length of a multiset.
    /// </summary>
    /// <param name="mset">
    ///     The multiset to measure.
    /// </param>
    /// <returns>
    ///     The number of elements in <paramref name="_arg1" />.
    /// </returns>
    let length (MSet mset) =
        mset |> Map.fold (fun count _ n -> count + n) 0

    /// <summary>
    ///     Appends two multisets.
    /// </summary>
    /// <remarks>
    ///     Since multisets are ordered, the resulting multiset may not
    ///     necessarily be <c>xs</c> followed by <c>ys</c>.
    /// </remarks>
    ///
    /// <param name="xs">The first multiset to append.</param>
    /// <param name="ys">The second multiset to append.</param>
    ///
    /// <returns>
    ///     The result of appending <c>xs</c> to <c>ys</c>.
    /// </returns>
    let append xs (MSet ymap) =
        Map.fold addn xs ymap

    /// <summary>
    ///     Maps <c>f</c> over the unique items of a multiset, passing
    ///     an accumulator in some arbitrary order.
    /// </summary>
    /// <param name="f">
    ///     The function to map over the multiset.  This takes the
    ///     accumulator, the item, and the number of times that item
    ///     appears in the multiset.  It should return the new item.  It
    ///     is assumed the number of appearances does not change.
    /// </param>
    /// <param name="init">
    ///     The initial value of the accumulator.
    /// </param>
    /// <typeparam name="acc">
    ///     The type of the accumulator.
    /// </typeparam>
    /// <typeparam name="src">
    ///     The type of variables in the list to map.
    /// </typeparam>
    /// <typeparam name="dst">
    ///     The type of variables in the list after mapping.
    /// </typeparam>
    /// <returns>
    ///     The pair of the final value of the accumulator, and the
    ///     result of mapping <c>f</c> over the multiset.
    /// </returns>
    /// <remarks>
    ///     Since multisets are ordered, mapping can change the position of
    ///     items.
    /// </remarks>
    let mapAccum
      (f : 'acc -> 'src -> int -> ('acc * 'dst))
      (init : 'acc)
      (MSet ms : Multiset<'src>)
      : ('acc * Multiset<'dst>) =
        // TODO(CaptainHayashi): convert map to a similar abstraction.
        ms
        |> Map.toList
        |> mapAccumL
               (fun acc (src, num) ->
                   let acc', dst = f acc src num
                   (acc, (dst, num)))
               init
        |> pairMap id (Map.ofList >> MSet)

    /// <summary>
    ///     Maps <c>f</c> over a multiset.
    /// </summary>
    /// <remarks>
    ///     Since multisets are ordered, mapping can change the position of
    ///     items.
    /// </remarks>
    ///
    /// <param name="f">The function to map over the multiset.</param>
    ///
    /// <returns>
    ///     The result of mapping <c>f</c> over the multiset.
    /// </returns>
    let map f (MSet xs)=
        let rec repeat_add map k n =
            match n with
            | 0 -> map
            | n -> repeat_add (add map (f k)) k (n-1)
        //Note that this is used with side-effecting f, so must be called n times for each addition.
        Map.fold repeat_add empty xs

    /// Produces the power-multiset of a multiset, as a set of multisets.
    let power msm =
        (* Solve the problem using Boolean arithmetic on the index of the
         * powerset item.
         *)
        let ms = toFlatList msm
        seq {
            for i in 0..(1 <<< List.length ms) - 1 do
                yield (seq { 0..(List.length ms) - 1 } |> Seq.choose (fun j ->
                                                              let cnd : int = i &&& (1 <<< j)
                                                              if cnd <> 0 then Some ms.[j]
                                                              else None))
                      |> ofFlatSeq
        }
        |> Set.ofSeq

    /// <summary>
    ///     Collapses a multiset of results to a result on a multiset.
    /// </summary>
    /// <param name="_arg1">
    ///     The multiset to collect.
    /// </param>
    /// <typeparam name="item">
    ///     Type of items in the multiset.
    /// </typeparam>
    /// <typeparam name="err">
    ///     Type of errors in the result.
    /// </typeparam>
    /// <returns>
    ///     A result, containing the collected form of
    ///     <paramref name="_arg1" />.
    /// </returns>
    let collect
      (MSet ms : Multiset<Result<'item, 'err>>)
      : Result<Multiset<'item>, 'err> =
        // TODO(CaptainHayashi): unify with map?
        let rec itr tos fros warns : Result<Multiset<'item>, 'err> =
            match tos with
            | [] -> ok (MSet (Map.ofList fros))
            | ((Warn (x, ws), n)::xs) -> itr xs ((x, n)::fros) (ws@warns)
            | ((Pass x, n)::xs) -> itr xs ((x, n)::fros) warns
            | ((Fail e, n)::xs) -> Bad e
        itr (Map.toList ms) [] []


/// <summary>
///     Tests for collections.
/// </summary>
module Tests =
    open NUnit.Framework

    let tcd : obj[] -> TestCaseData = TestCaseData

    /// <summary>
    ///    NUnit tests for collections.
    /// </summary>
    type NUnit () =
        /// <summary>
        ///     Test cases for <c>Multiset.ofFlatList</c>.
        /// </summary>
        static member ListMultisets =
            [ TestCaseData([10; 23; 1; 85; 23; 1] : int list)
                 .Returns(([ (1, 2)
                             (10, 1)
                             (23, 2)
                             (85, 1) ]
                          |> Map.ofList |> MSet) : Multiset<int>)
                 .SetName("A populated list produces the expected multiset")
              TestCaseData([] : int list)
                 .Returns(MSet (Map.empty) : Multiset<int>)
                 .SetName("An empty list produces the empty multiset") ]

        /// <summary>
        ///     Tests <c>Multiset.ofFlatList</c>.
        /// </summary>
        [<TestCaseSource("ListMultisets")>]
        member x.``Multiset.ofFlatList creates correct multisets`` l =
            (Multiset.ofFlatList l) : Multiset<int>


        /// <summary>
        ///     Test cases for <c>Multiset.toFlatList</c>.
        /// </summary>
        static member MultisetLists =
            [ TestCaseData(MSet (Map.ofList [ (1, 2)
                                              (10, 1)
                                              (23, 2)
                                              (85, 1) ] ) : Multiset<int>)
                 .Returns([1; 1; 10; 23; 23; 85] : int list)
                 .SetName("A populated multiset produces the expected list")
              TestCaseData(MSet (Map.empty) : Multiset<int>)
                 .Returns([] : int list)
                 .SetName("An empty multiset produces the empty list") ]

        /// <summary>
        ///     Tests <c>Multiset.toFlatList</c>.
        /// </summary>
        [<TestCaseSource("MultisetLists")>]
        member x.``Multiset.toFlatList creates correct lists`` ms =
            (Multiset.toFlatList ms) : int list


        /// <summary>
        ///     Test cases for <c>Multiset.append</c>.
        /// </summary>
        static member MultisetAppends =
            [ (tcd [| (Multiset.empty : Multiset<int>)
                      (Multiset.empty : Multiset<int>) |])
                 .Returns(MSet (Map.empty) : Multiset<int>)
                 .SetName("Appending two empty msets yields the empty mset")
              (tcd [| (Multiset.ofFlatList [1; 2; 3] : Multiset<int>)
                      (Multiset.empty : Multiset<int>) |])
                 .Returns(MSet (Map.ofList [ (1, 1) ; (2, 1) ; (3, 1) ] )
                               : Multiset<int>)
                 .SetName("Appending x and an empty mset yields x")
              (tcd [| (Multiset.empty : Multiset<int>)
                      (Multiset.ofFlatList [4; 5] : Multiset<int>) |])
                 .Returns(MSet (Map.ofList [ (4, 1) ; (5, 1) ] )
                               : Multiset<int>)
                 .SetName("Appending an empty mset and x yields x")
              (tcd [| (Multiset.ofFlatList [1; 2; 3; 4; 5] : Multiset<int>)
                      (Multiset.ofFlatList [2; 4; 4; 5; 6] : Multiset<int>) |])
                 .Returns(MSet (Map.ofList [ (1, 1)
                                             (2, 2)
                                             (3, 1)
                                             (4, 3)
                                             (5, 2)
                                             (6, 1) ]) : Multiset<int>)
                 .SetName("Appending two overlapping msets works as expected")
              (tcd [| (Multiset.ofFlatList [1; 3; 5] : Multiset<int>)
                      (Multiset.ofFlatList [2; 4; 6] : Multiset<int>) |])
                 .Returns(MSet (Map.ofList [ (1, 1)
                                             (2, 1)
                                             (3, 1)
                                             (4, 1)
                                             (5, 1)
                                             (6, 1) ]) : Multiset<int>)
                 .SetName("Appending two disjoint msets works as expected") ]

        /// <summary>
        ///     Tests <c>Multiset.append</c>.
        /// </summary>
        [<TestCaseSource("MultisetAppends")>]
        member x.``Multiset.append appends multisets correctly`` a b =
            (Multiset.append a b) : Multiset<int>


        /// <summary>
        ///     Test cases for <c>Multiset.length</c>.
        /// </summary>
        static member MultisetLength =
            [ (tcd [| (Multiset.empty : Multiset<int>) |])
                 .Returns(0)
                 .SetName("The empty mset contains 0 items")
              (tcd [| (Multiset.ofFlatList [ 1 ; 2 ; 3 ] : Multiset<int>) |])
                 .Returns(3)
                 .SetName("A disjoint mset's length is the number of items")
              (tcd [| (Multiset.ofFlatList [ 1 ; 2 ; 3 ; 2 ; 3 ] : Multiset<int>) |])
                 .Returns(5)
                 .SetName("A non-disjoint mset's length is correct") ]

        /// <summary>
        ///     Tests <c>Multiset.length</c>.
        /// </summary>
        [<TestCaseSource("MultisetLength")>]
        member x.``Multiset.length takes multiset length correctly`` (a : Multiset<int>) =
            Multiset.length a
