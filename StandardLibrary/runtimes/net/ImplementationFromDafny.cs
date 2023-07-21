// Dafny program <stdin> compiled into C#
// To recompile, you will need the libraries
//     System.Runtime.Numerics.dll System.Collections.Immutable.dll
// but the 'dotnet' tool in net6.0 should pick those up automatically.
// Optionally, you may want to include compiler switches like
//     /debug /nowarn:162,164,168,183,219,436,1717,1718

using System;
using System.Numerics;
using System.Collections;
[assembly: DafnyAssembly.DafnySourceAttribute(@"// dafny 4.1.0.0
// Command Line Options: -stdin -noVerify -vcsCores:2 -compileTarget:cs -spillTargetCode:3 -compile:0 -optimizeErasableDatatypeWrapper:0 -quantifierSyntax:3 -unicodeChar:0 -functionSyntax:3 -useRuntimeLib -out runtimes/net/ImplementationFromDafny
// <stdin>


module {:extern ""DafnyLibraries""} {:options ""-functionSyntax:4""} DafnyLibraries {

  import opened Wrappers
  trait {:termination false} MutableMapTrait<K(==), V(==)> {
    function method content(): map<K, V>
      reads this
      decreases {this}

    method Put(k: K, v: V)
      modifies this
      ensures this.content() == old(this.content())[k := v]
      ensures k in old(this.content()).Keys ==> this.content().Values + {old(this.content())[k]} == old(this.content()).Values + {v}
      ensures k !in old(this.content()).Keys ==> this.content().Values == old(this.content()).Values + {v}

    function method Keys(): (keys: set<K>)
      reads this
      ensures keys == this.content().Keys
      decreases {this}

    predicate method HasKey(k: K)
      reads this
      ensures HasKey(k) <==> k in this.content().Keys
      decreases {this}

    function method Values(): (values: set<V>)
      reads this
      ensures values == this.content().Values
      decreases {this}

    function method Items(): (items: set<(K, V)>)
      reads this
      ensures items == this.content().Items
      ensures items == set k: K {:trigger this.content()[k]} {:trigger k in this.content().Keys} | k in this.content().Keys :: (k, this.content()[k])
      decreases {this}

    function method Select(k: K): (v: V)
      requires this.HasKey(k)
      reads this
      ensures v in this.content().Values
      ensures this.content()[k] == v
      decreases {this}

    method Remove(k: K)
      modifies this
      ensures this.content() == old(this.content()) - {k}
      ensures k in old(this.content()).Keys ==> this.content().Values + {old(this.content())[k]} == old(this.content()).Values

    function method Size(): (size: int)
      reads this
      ensures size == |this.content().Items|
      decreases {this}
  }

  class {:extern} MutableMap<K(==), V(==)> extends MutableMapTrait<K, V> {
    constructor {:extern} ()
      ensures this.content() == map[]

    function method {:extern} content(): map<K, V>
      reads this
      decreases {this}

    method {:extern} Put(k: K, v: V)
      modifies this
      ensures this.content() == old(this.content())[k := v]
      ensures k in old(this.content()).Keys ==> this.content().Values + {old(this.content())[k]} == old(this.content()).Values + {v}
      ensures k !in old(this.content()).Keys ==> this.content().Values == old(this.content()).Values + {v}

    function method {:extern} Keys(): (keys: set<K>)
      reads this
      ensures keys == this.content().Keys
      decreases {this}

    predicate method {:extern} HasKey(k: K)
      reads this
      ensures HasKey(k) <==> k in this.content().Keys
      decreases {this}

    function method {:extern} Values(): (values: set<V>)
      reads this
      ensures values == this.content().Values
      decreases {this}

    function method {:extern} Items(): (items: set<(K, V)>)
      reads this
      ensures items == this.content().Items
      ensures items == set k: K {:trigger this.content()[k]} {:trigger k in this.content().Keys} | k in this.content().Keys :: (k, this.content()[k])
      decreases {this}

    function method {:extern} Select(k: K): (v: V)
      requires this.HasKey(k)
      reads this
      ensures v in this.content().Values
      ensures this.content()[k] == v
      decreases {this}

    function method SelectOpt(k: K): (o: Option<V>)
      reads this
      ensures o.Some? ==> this.HasKey(k) && o.value in this.content().Values && this.content()[k] == o.value
      ensures o.None? ==> !this.HasKey(k)
      decreases {this}
    {
      if this.HasKey(k) then
        Some(this.Select(k))
      else
        None
    }

    method {:extern} Remove(k: K)
      modifies this
      ensures this.content() == old(this.content()) - {k}
      ensures k in old(this.content()).Keys ==> this.content().Values + {old(this.content())[k]} == old(this.content()).Values

    function method {:extern} Size(): (size: int)
      reads this
      ensures size == |this.content().Items|
      decreases {this}
  }
}

module {:options ""-functionSyntax:4""} Wrappers {
  datatype Option<+T> = None | Some(value: T) {
    function method ToResult(): Result<T, string>
      decreases this
    {
      match this
      case Some(v) =>
        Success(v)
      case None() =>
        Failure(""Option is None"")
    }

    function method ToResult'<R>(error: R): Result<T, R>
      decreases this
    {
      match this
      case Some(v) =>
        Success(v)
      case None() =>
        Failure(error)
    }

    function method UnwrapOr(default: T): T
      decreases this
    {
      match this
      case Some(v) =>
        v
      case None() =>
        default
    }

    predicate method IsFailure()
      decreases this
    {
      None?
    }

    function method PropagateFailure<U>(): Option<U>
      requires None?
      decreases this
    {
      None
    }

    function method Extract(): T
      requires Some?
      decreases this
    {
      value
    }
  }

  datatype Result<+T, +R> = Success(value: T) | Failure(error: R) {
    function method ToOption(): Option<T>
      decreases this
    {
      match this
      case Success(s) =>
        Some(s)
      case Failure(e) =>
        None()
    }

    function method UnwrapOr(default: T): T
      decreases this
    {
      match this
      case Success(s) =>
        s
      case Failure(e) =>
        default
    }

    predicate method IsFailure()
      decreases this
    {
      Failure?
    }

    function method PropagateFailure<U>(): Result<U, R>
      requires Failure?
      decreases this
    {
      Failure(this.error)
    }

    function method MapFailure<NewR>(reWrap: R -> NewR): Result<T, NewR>
      decreases this
    {
      match this
      case Success(s) =>
        Success(s)
      case Failure(e) =>
        Failure(reWrap(e))
    }

    function method Extract(): T
      requires Success?
      decreases this
    {
      value
    }
  }

  datatype Outcome<E> = Pass | Fail(error: E) {
    predicate method IsFailure()
      decreases this
    {
      Fail?
    }

    function method PropagateFailure<U>(): Result<U, E>
      requires Fail?
      decreases this
    {
      Failure(this.error)
    }
  }

  function method Need<E>(condition: bool, error: E): (result: Outcome<E>)
    decreases condition
  {
    if condition then
      Pass
    else
      Fail(error)
  }
}

module Actions {

  import opened Wrappers

  import opened Seq
  datatype ActionInvoke<A, R> = ActionInvoke(input: A, output: R)

  trait {:termination false} Action<A, R> {
    method Invoke(a: A, ghost attemptsState: seq<ActionInvoke<A, R>>) returns (r: R)
      requires Invariant()
      modifies Modifies
      ensures Invariant()
      ensures Ensures(a, r, attemptsState)
      decreases Modifies

    predicate Invariant()
      reads Modifies
      decreases Modifies

    predicate Ensures(a: A, r: R, attemptsState: seq<ActionInvoke<A, R>>)
      reads Modifies
      decreases Modifies

    ghost const Modifies: set<object>
  }

  trait {:termination false} ActionWithResult<A, R, E> extends Action<A, Result<R, E>> {
    method Invoke(a: A, ghost attemptsState: seq<ActionInvoke<A, Result<R, E>>>) returns (r: Result<R, E>)
      requires Invariant()
      modifies Modifies
      ensures Invariant()
      ensures Ensures(a, r, attemptsState)
      decreases Modifies
  }

  trait {:termination false} DeterministicAction<A, R> {
    method Invoke(a: A) returns (r: R)
      ensures Ensures(a, r)

    predicate Ensures(a: A, r: R)
  }

  trait {:termination false} DeterministicActionWithResult<A, R, E> extends DeterministicAction<A, Result<R, E>> {
    method Invoke(a: A) returns (r: Result<R, E>)
      ensures Ensures(a, r)
  }

  method DeterministicMap<A, R>(action: DeterministicAction<A, R>, s: seq<A>) returns (res: seq<R>)
    ensures |s| == |res|
    ensures forall i: int {:trigger res[i]} {:trigger s[i]} :: true && 0 <= i < |s| ==> action.Ensures(s[i], res[i])
    decreases action, s
  {
    var rs := [];
    for i: int := 0 to |s|
      invariant |s[..i]| == |rs|
      invariant forall j: int {:trigger rs[j]} {:trigger s[j]} :: true && 0 <= j < i ==> action.Ensures(s[j], rs[j])
    {
      var r := action.Invoke(s[i]);
      rs := rs + [r];
    }
    return rs;
  }

  method DeterministicMapWithResult<A, R, E>(action: DeterministicActionWithResult<A, R, E>, s: seq<A>) returns (res: Result<seq<R>, E>)
    ensures res.Success? ==> |s| == |res.value|
    ensures res.Success? ==> forall i: int {:trigger res.value[i]} {:trigger s[i]} :: true && 0 <= i < |s| ==> action.Ensures(s[i], Success(res.value[i]))
    decreases action, s
  {
    var rs := [];
    for i: int := 0 to |s|
      invariant |s[..i]| == |rs|
      invariant forall j: int {:trigger rs[j]} {:trigger s[j]} :: true && 0 <= j < i ==> action.Ensures(s[j], Success(rs[j]))
    {
      var r :- action.Invoke(s[i]);
      rs := rs + [r];
    }
    return Success(rs);
  }

  method DeterministicFlatMap<A, R>(action: DeterministicAction<A, seq<R>>, s: seq<A>) returns (res: seq<R>)
    ensures forall i: A {:trigger i in s} :: i in s ==> exists fm: seq<R> {:trigger action.Ensures(i, fm)} :: action.Ensures(i, fm) && forall k: R {:trigger k in res} {:trigger k in fm} | k in fm :: k in res
    decreases action, s
  {
    ghost var parts := [];
    var rs := [];
    for i: int := 0 to |s|
      invariant |s[..i]| == |parts|
      invariant forall j: int {:trigger parts[j]} {:trigger s[j]} :: (true && 0 <= j < i ==> action.Ensures(s[j], parts[j])) && (true && 0 <= j < i ==> forall b: R {:trigger b in rs} {:trigger b in parts[j]} | b in parts[j] :: b in rs)
    {
      var r := action.Invoke(s[i]);
      rs := rs + r;
      parts := parts + [r];
    }
    return rs;
  }

  method DeterministicFlatMapWithResult<A, R, E>(action: DeterministicActionWithResult<A, seq<R>, E>, s: seq<A>)
      returns (res: Result<seq<R>, E>, ghost parts: seq<seq<R>>)
    ensures res.Success? ==> |s| == |parts| && res.value == Flatten(parts) && forall i: int {:trigger parts[i]} {:trigger s[i]} :: (0 <= i < |s| ==> action.Ensures(s[i], Success(parts[i]))) && (0 <= i < |s| ==> multiset(parts[i]) <= multiset(res.value))
    decreases action, s
  {
    parts := [];
    var rs := [];
    for i: int := 0 to |s|
      invariant |s[..i]| == |parts|
      invariant forall j: int {:trigger parts[j]} {:trigger s[j]} :: (true && 0 <= j < i ==> action.Ensures(s[j], Success(parts[j]))) && (true && 0 <= j < i ==> multiset(parts[j]) <= multiset(rs))
      invariant Flatten(parts) == rs
    {
      var r :- action.Invoke(s[i]);
      rs := rs + r;
      LemmaFlattenConcat(parts, [r]);
      parts := parts + [r];
    }
    return Success(rs), parts;
  }

  method Filter<A>(action: DeterministicAction<A, bool>, s: seq<A>) returns (res: seq<A>)
    ensures |s| >= |res|
    ensures forall j: A {:trigger action.Ensures(j, true)} {:trigger j in s} {:trigger j in res} :: (j in res ==> j in s) && (j in res ==> action.Ensures(j, true))
    decreases action, s
  {
    var rs := [];
    for i: int := 0 to |s|
      invariant |s[..i]| >= |rs|
      invariant forall j: A {:trigger action.Ensures(j, true)} {:trigger j in s} {:trigger j in rs} :: (j in rs ==> j in s) && (j in rs ==> action.Ensures(j, true))
    {
      var r := action.Invoke(s[i]);
      if r {
        rs := rs + [s[i]];
      }
    }
    return rs;
  }

  method FilterWithResult<A, E>(action: DeterministicActionWithResult<A, bool, E>, s: seq<A>) returns (res: Result<seq<A>, E>)
    ensures res.Success? ==> |s| >= |res.value| && forall j: A {:trigger action.Ensures(j, Success(true))} {:trigger j in s} {:trigger j in res.value} :: (j in res.value ==> j in s) && (j in res.value ==> action.Ensures(j, Success(true)))
    decreases action, s
  {
    var rs := [];
    for i: int := 0 to |s|
      invariant |s[..i]| >= |rs|
      invariant forall j: A {:trigger action.Ensures(j, Success(true))} {:trigger j in s} {:trigger j in rs} :: (j in rs ==> j in s) && (j in rs ==> action.Ensures(j, Success(true)))
    {
      var r :- action.Invoke(s[i]);
      if r {
        rs := rs + [s[i]];
      }
    }
    return Success(rs);
  }

  method ReduceToSuccess<A, B, E>(action: ActionWithResult<A, B, E>, s: seq<A>)
      returns (res: Result<B, seq<E>>, ghost attemptsState: seq<ActionInvoke<A, Result<B, E>>>)
    requires 0 < |s|
    requires action.Invariant()
    modifies action.Modifies
    ensures 0 < |attemptsState| <= |s|
    ensures forall i: int {:trigger s[i]} {:trigger attemptsState[i]} | 0 <= i < |attemptsState| :: attemptsState[i].input == s[i]
    ensures action.Invariant()
    ensures if res.Success? then Last(attemptsState).output.Success? && Last(attemptsState).output.value == res.value && action.Ensures(Last(attemptsState).input, Last(attemptsState).output, DropLast(attemptsState)) && forall i: int {:trigger attemptsState[i]} | 0 <= i < |DropLast(attemptsState)| :: attemptsState[i].output.Failure? else |attemptsState| == |s| && forall i: int {:trigger attemptsState[i]} | 0 <= i < |attemptsState| :: attemptsState[i].output.Failure?
    decreases action.Modifies
  {
    var attemptedResults := [];
    attemptsState := [];
    for i: int := 0 to |s|
      invariant |s[..i]| == |attemptsState| == |attemptedResults|
      invariant forall j: int {:trigger attemptedResults[j]} {:trigger s[j]} {:trigger attemptsState[j]} | 0 <= j < |attemptsState| :: attemptsState[j].input == s[j] && attemptsState[j].output.Failure? && attemptedResults[j] == attemptsState[j].output
      invariant action.Invariant()
    {
      var attempt := action.Invoke(s[i], attemptsState);
      attemptsState := attemptsState + [ActionInvoke(s[i], attempt)];
      attemptedResults := attemptedResults + [attempt];
      if attempt.Success? {
        return Success(attempt.value), attemptsState;
      }
    }
    res := Failure(Seq.Map(pluckErrors, attemptedResults));
  }

  function method pluckErrors<B, E>(r: Result<B, E>): (e: E)
    requires r.Failure?
    ensures r.error == e
    decreases r
  {
    r.error
  }
}

module {:options ""-functionSyntax:4""} Seq {

  import opened Wrappers

  import opened MergeSort

  import opened Relations

  import Math
  function method First<T>(xs: seq<T>): T
    requires |xs| > 0
    decreases xs
  {
    xs[0]
  }

  function method DropFirst<T>(xs: seq<T>): seq<T>
    requires |xs| > 0
    decreases xs
  {
    xs[1..]
  }

  function method Last<T>(xs: seq<T>): T
    requires |xs| > 0
    decreases xs
  {
    xs[|xs| - 1]
  }

  function method DropLast<T>(xs: seq<T>): seq<T>
    requires |xs| > 0
    decreases xs
  {
    xs[..|xs| - 1]
  }

  lemma LemmaLast<T>(xs: seq<T>)
    requires |xs| > 0
    ensures DropLast(xs) + [Last(xs)] == xs
    decreases xs
  {
  }

  lemma LemmaAppendLast<T>(xs: seq<T>, ys: seq<T>)
    requires 0 < |ys|
    ensures Last(xs + ys) == Last(ys)
    decreases xs, ys
  {
  }

  lemma LemmaConcatIsAssociative<T>(xs: seq<T>, ys: seq<T>, zs: seq<T>)
    ensures xs + (ys + zs) == xs + ys + zs
    decreases xs, ys, zs
  {
  }

  lemma IndexingImpliesMembership<T>(p: T -> bool, xs: seq<T>)
    requires forall i: int {:trigger xs[i]} | 0 <= i < |xs| :: p(xs[i])
    ensures forall t: T {:trigger p(t)} {:trigger t in xs} | t in xs :: p(t)
    decreases xs
  {
  }

  lemma MembershipImpliesIndexing<T>(p: T -> bool, xs: seq<T>)
    requires forall t: T {:trigger p(t)} {:trigger t in xs} | t in xs :: p(t)
    ensures forall i: int {:trigger xs[i]} | 0 <= i < |xs| :: p(xs[i])
    decreases xs
  {
  }

  predicate IsPrefix<T>(xs: seq<T>, ys: seq<T>)
    ensures IsPrefix(xs, ys) ==> |xs| <= |ys| && xs == ys[..|xs|]
    decreases xs, ys
  {
    xs <= ys
  }

  predicate IsSuffix<T>(xs: seq<T>, ys: seq<T>)
    decreases xs, ys
  {
    |xs| <= |ys| &&
    xs == ys[|ys| - |xs|..]
  }

  lemma LemmaSplitAt<T>(xs: seq<T>, pos: nat)
    requires pos < |xs|
    ensures xs[..pos] + xs[pos..] == xs
    decreases xs, pos
  {
  }

  lemma LemmaElementFromSlice<T>(xs: seq<T>, xs': seq<T>, a: int, b: int, pos: nat)
    requires 0 <= a <= b <= |xs|
    requires xs' == xs[a .. b]
    requires a <= pos < b
    ensures pos - a < |xs'|
    ensures xs'[pos - a] == xs[pos]
    decreases xs, xs', a, b, pos
  {
  }

  lemma LemmaSliceOfSlice<T>(xs: seq<T>, s1: int, e1: int, s2: int, e2: int)
    requires 0 <= s1 <= e1 <= |xs|
    requires 0 <= s2 <= e2 <= e1 - s1
    ensures xs[s1 .. e1][s2 .. e2] == xs[s1 + s2 .. s1 + e2]
    decreases xs, s1, e1, s2, e2
  {
  }

  method ToArray<T>(xs: seq<T>) returns (a: array<T>)
    ensures fresh(a)
    ensures a.Length == |xs|
    ensures forall i: int {:trigger xs[i]} {:trigger a[i]} :: 0 <= i < |xs| ==> a[i] == xs[i]
    decreases xs
  {
    a := new T[|xs|] ((i: int) requires 0 <= i < |xs| => xs[i]);
  }

  function method {:opaque} {:fuel 0, 0} ToSet<T>(xs: seq<T>): set<T>
    decreases xs
  {
    set x: T {:trigger x in xs} | x in xs
  }

  lemma LemmaCardinalityOfSet<T>(xs: seq<T>)
    ensures |ToSet(xs)| <= |xs|
    decreases xs
  {
  }

  lemma LemmaCardinalityOfEmptySetIs0<T>(xs: seq<T>)
    ensures |ToSet(xs)| == 0 <==> |xs| == 0
    decreases xs
  {
  }

  predicate {:opaque} {:fuel 0, 0} HasNoDuplicates<T>(xs: seq<T>)
    decreases xs
  {
    forall i: int, j: int {:trigger xs[j], xs[i]} :: 
      0 <= i < |xs| &&
      0 <= j < |xs| &&
      i != j ==>
        xs[i] != xs[j]
  }

  lemma {:timeLimitMultiplier 3} /*{:_timeLimit 30}*/ LemmaNoDuplicatesInConcat<T>(xs: seq<T>, ys: seq<T>)
    requires HasNoDuplicates(xs)
    requires HasNoDuplicates(ys)
    requires multiset(xs) !! multiset(ys)
    ensures HasNoDuplicates(xs + ys)
    decreases xs, ys
  {
  }

  lemma LemmaCardinalityOfSetNoDuplicates<T>(xs: seq<T>)
    requires HasNoDuplicates(xs)
    ensures |ToSet(xs)| == |xs|
    decreases xs
  {
  }

  lemma LemmaNoDuplicatesCardinalityOfSet<T>(xs: seq<T>)
    requires |ToSet(xs)| == |xs|
    ensures HasNoDuplicates(xs)
    decreases xs
  {
  }

  lemma LemmaMultisetHasNoDuplicates<T>(xs: seq<T>)
    requires HasNoDuplicates(xs)
    ensures forall x: T {:trigger multiset(xs)[x]} | x in multiset(xs) :: multiset(xs)[x] == 1
    decreases xs
  {
  }

  function method {:opaque} {:fuel 0, 0} IndexOf<T(==)>(xs: seq<T>, v: T): (i: nat)
    requires v in xs
    ensures i < |xs| && xs[i] == v
    ensures forall j: int {:trigger xs[j]} :: 0 <= j < i ==> xs[j] != v
    decreases xs
  {
    if xs[0] == v then
      0
    else
      1 + IndexOf(xs[1..], v)
  }

  function method {:opaque} {:fuel 0, 0} IndexOfOption<T(==)>(xs: seq<T>, v: T): (o: Option<nat>)
    ensures if o.Some? then o.value < |xs| && xs[o.value] == v && forall j: int {:trigger xs[j]} :: 0 <= j < o.value ==> xs[j] != v else v !in xs
    decreases xs
  {
    if |xs| == 0 then
      None()
    else if xs[0] == v then
      Some(0)
    else
      var o': Option<nat> := IndexOfOption(xs[1..], v); if o'.Some? then Some(o'.value + 1) else None()
  }

  function method {:opaque} {:fuel 0, 0} LastIndexOf<T(==)>(xs: seq<T>, v: T): (i: nat)
    requires v in xs
    ensures i < |xs| && xs[i] == v
    ensures forall j: int {:trigger xs[j]} :: i < j < |xs| ==> xs[j] != v
    decreases xs
  {
    if xs[|xs| - 1] == v then
      |xs| - 1
    else
      LastIndexOf(xs[..|xs| - 1], v)
  }

  function method {:opaque} {:fuel 0, 0} LastIndexOfOption<T(==)>(xs: seq<T>, v: T): (o: Option<nat>)
    ensures if o.Some? then o.value < |xs| && xs[o.value] == v && forall j: int {:trigger xs[j]} :: o.value < j < |xs| ==> xs[j] != v else v !in xs
    decreases xs
  {
    if |xs| == 0 then
      None()
    else if xs[|xs| - 1] == v then
      Some(|xs| - 1)
    else
      LastIndexOfOption(xs[..|xs| - 1], v)
  }

  function method {:opaque} {:fuel 0, 0} Remove<T>(xs: seq<T>, pos: nat): (ys: seq<T>)
    requires pos < |xs|
    ensures |ys| == |xs| - 1
    ensures forall i: int {:trigger ys[i], xs[i]} | 0 <= i < pos :: ys[i] == xs[i]
    ensures forall i: int {:trigger ys[i]} | pos <= i < |xs| - 1 :: ys[i] == xs[i + 1]
    decreases xs, pos
  {
    xs[..pos] + xs[pos + 1..]
  }

  function method {:opaque} {:fuel 0, 0} RemoveValue<T(==)>(xs: seq<T>, v: T): (ys: seq<T>)
    ensures v !in xs ==> xs == ys
    ensures v in xs ==> |multiset(ys)| == |multiset(xs)| - 1
    ensures v in xs ==> multiset(ys)[v] == multiset(xs)[v] - 1
    ensures HasNoDuplicates(xs) ==> HasNoDuplicates(ys) && ToSet(ys) == ToSet(xs) - {v}
    decreases xs
  {
    reveal HasNoDuplicates();
    reveal ToSet();
    if v !in xs then
      xs
    else
      var i: nat := IndexOf(xs, v); assert xs == xs[..i] + [v] + xs[i + 1..]; xs[..i] + xs[i + 1..]
  }

  function method {:opaque} {:fuel 0, 0} Insert<T>(xs: seq<T>, a: T, pos: nat): seq<T>
    requires pos <= |xs|
    ensures |Insert(xs, a, pos)| == |xs| + 1
    ensures forall i: int {:trigger Insert(xs, a, pos)[i], xs[i]} :: 0 <= i < pos ==> Insert(xs, a, pos)[i] == xs[i]
    ensures forall i: int {:trigger xs[i]} :: pos <= i < |xs| ==> Insert(xs, a, pos)[i + 1] == xs[i]
    ensures Insert(xs, a, pos)[pos] == a
    ensures multiset(Insert(xs, a, pos)) == multiset(xs) + multiset{a}
    decreases xs, pos
  {
    assert xs == xs[..pos] + xs[pos..];
    xs[..pos] + [a] + xs[pos..]
  }

  function method {:opaque} {:fuel 0, 0} Reverse<T>(xs: seq<T>): (ys: seq<T>)
    ensures |ys| == |xs|
    ensures forall i: int {:trigger ys[i]} {:trigger xs[|xs| - i - 1]} :: 0 <= i < |xs| ==> ys[i] == xs[|xs| - i - 1]
    decreases xs
  {
    if xs == [] then
      []
    else
      [xs[|xs| - 1]] + Reverse(xs[0 .. |xs| - 1])
  }

  function method {:opaque} {:fuel 0, 0} Repeat<T>(v: T, length: nat): (xs: seq<T>)
    ensures |xs| == length
    ensures forall i: nat {:trigger xs[i]} | i < |xs| :: xs[i] == v
    decreases length
  {
    if length == 0 then
      []
    else
      [v] + Repeat(v, length - 1)
  }

  function method {:opaque} {:fuel 0, 0} Unzip<A, B>(xs: seq<(A, B)>): (seq<A>, seq<B>)
    ensures |Unzip(xs).0| == |Unzip(xs).1| == |xs|
    ensures forall i: int {:trigger Unzip(xs).0[i]} {:trigger Unzip(xs).1[i]} :: 0 <= i < |xs| ==> (Unzip(xs).0[i], Unzip(xs).1[i]) == xs[i]
    decreases xs
  {
    if |xs| == 0 then
      ([], [])
    else
      var (a: seq<A>, b: seq<B>) := Unzip(DropLast(xs)); (a + [Last(xs).0], b + [Last(xs).1])
  }

  function method {:opaque} {:fuel 0, 0} Zip<A, B>(xs: seq<A>, ys: seq<B>): seq<(A, B)>
    requires |xs| == |ys|
    ensures |Zip(xs, ys)| == |xs|
    ensures forall i: int {:trigger Zip(xs, ys)[i]} :: 0 <= i < |Zip(xs, ys)| ==> Zip(xs, ys)[i] == (xs[i], ys[i])
    ensures Unzip(Zip(xs, ys)).0 == xs
    ensures Unzip(Zip(xs, ys)).1 == ys
    decreases xs, ys
  {
    if |xs| == 0 then
      []
    else
      Zip(DropLast(xs), DropLast(ys)) + [(Last(xs), Last(ys))]
  }

  lemma /*{:_induction xs}*/ LemmaZipOfUnzip<A, B>(xs: seq<(A, B)>)
    ensures Zip(Unzip(xs).0, Unzip(xs).1) == xs
    decreases xs
  {
  }

  function method {:opaque} {:fuel 0, 0} Max(xs: seq<int>): int
    requires 0 < |xs|
    ensures forall k: int {:trigger k in xs} :: k in xs ==> Max(xs) >= k
    ensures Max(xs) in xs
    decreases xs
  {
    assert xs == [xs[0]] + xs[1..];
    if |xs| == 1 then
      xs[0]
    else
      Math.Max(xs[0], Max(xs[1..]))
  }

  lemma /*{:_induction xs, ys}*/ LemmaMaxOfConcat(xs: seq<int>, ys: seq<int>)
    requires 0 < |xs| && 0 < |ys|
    ensures Max(xs + ys) >= Max(xs)
    ensures Max(xs + ys) >= Max(ys)
    ensures forall i: int {:trigger i in [Max(xs + ys)]} :: i in xs + ys ==> Max(xs + ys) >= i
    decreases xs, ys
  {
  }

  function method {:opaque} {:fuel 0, 0} Min(xs: seq<int>): int
    requires 0 < |xs|
    ensures forall k: int {:trigger k in xs} :: k in xs ==> Min(xs) <= k
    ensures Min(xs) in xs
    decreases xs
  {
    assert xs == [xs[0]] + xs[1..];
    if |xs| == 1 then
      xs[0]
    else
      Math.Min(xs[0], Min(xs[1..]))
  }

  lemma /*{:_induction xs, ys}*/ LemmaMinOfConcat(xs: seq<int>, ys: seq<int>)
    requires 0 < |xs| && 0 < |ys|
    ensures Min(xs + ys) <= Min(xs)
    ensures Min(xs + ys) <= Min(ys)
    ensures forall i: int {:trigger i in xs + ys} :: i in xs + ys ==> Min(xs + ys) <= i
    decreases xs, ys
  {
  }

  lemma /*{:_induction xs}*/ LemmaSubseqMax(xs: seq<int>, from: nat, to: nat)
    requires from < to <= |xs|
    ensures Max(xs[from .. to]) <= Max(xs)
    decreases xs, from, to
  {
  }

  lemma /*{:_induction xs}*/ LemmaSubseqMin(xs: seq<int>, from: nat, to: nat)
    requires from < to <= |xs|
    ensures Min(xs[from .. to]) >= Min(xs)
    decreases xs, from, to
  {
  }

  function method Flatten<T>(xs: seq<seq<T>>): seq<T>
    decreases |xs|
  {
    if |xs| == 0 then
      []
    else
      xs[0] + Flatten(xs[1..])
  }

  lemma /*{:_induction xs, ys}*/ LemmaFlattenConcat<T>(xs: seq<seq<T>>, ys: seq<seq<T>>)
    ensures Flatten(xs + ys) == Flatten(xs) + Flatten(ys)
    decreases xs, ys
  {
  }

  function method FlattenReverse<T>(xs: seq<seq<T>>): seq<T>
    decreases |xs|
  {
    if |xs| == 0 then
      []
    else
      FlattenReverse(DropLast(xs)) + Last(xs)
  }

  lemma /*{:_induction xs, ys}*/ LemmaFlattenReverseConcat<T>(xs: seq<seq<T>>, ys: seq<seq<T>>)
    ensures FlattenReverse(xs + ys) == FlattenReverse(xs) + FlattenReverse(ys)
    decreases xs, ys
  {
  }

  lemma /*{:_induction xs}*/ LemmaFlattenAndFlattenReverseAreEquivalent<T>(xs: seq<seq<T>>)
    ensures Flatten(xs) == FlattenReverse(xs)
    decreases xs
  {
  }

  lemma /*{:_induction xs}*/ LemmaFlattenLengthGeSingleElementLength<T>(xs: seq<seq<T>>, i: int)
    requires 0 <= i < |xs|
    ensures |FlattenReverse(xs)| >= |xs[i]|
    decreases xs, i
  {
  }

  lemma /*{:_induction xs}*/ LemmaFlattenLengthLeMul<T>(xs: seq<seq<T>>, j: int)
    requires forall i: int {:trigger xs[i]} | 0 <= i < |xs| :: |xs[i]| <= j
    ensures |FlattenReverse(xs)| <= |xs| * j
    decreases xs, j
  {
  }

  function method {:opaque} {:fuel 0, 0} Map<T, R>(f: T ~> R, xs: seq<T>): (result: seq<R>)
    requires forall i: int {:trigger xs[i]} :: 0 <= i < |xs| ==> f.requires(xs[i])
    reads set i: int, o: object? {:trigger o in f.reads(xs[i])} | 0 <= i < |xs| && o in f.reads(xs[i]) :: o
    ensures |result| == |xs|
    ensures forall i: int {:trigger result[i]} :: 0 <= i < |xs| ==> result[i] == f(xs[i])
    decreases set i: int, o: object? {:trigger o in f.reads(xs[i])} | 0 <= i < |xs| && o in f.reads(xs[i]) :: o, xs
  {
    seq(|xs|, (i: int) requires 0 <= i < |xs| && f.requires(xs[i]) reads set i: int, o: object? {:trigger o in f.reads(xs[i])} | 0 <= i < |xs| && o in f.reads(xs[i]) :: o => f(xs[i]))
  }

  function method {:opaque} {:fuel 0, 0} MapWithResult<T, R, E>(f: T ~> Result<R, E>, xs: seq<T>): (result: Result<seq<R>, E>)
    requires forall i: int {:trigger xs[i]} :: 0 <= i < |xs| ==> f.requires(xs[i])
    reads set i: int, o: object? {:trigger o in f.reads(xs[i])} | 0 <= i < |xs| && o in f.reads(xs[i]) :: o
    ensures result.Success? ==> |result.value| == |xs| && forall i: int {:trigger result.value[i]} {:trigger xs[i]} :: (0 <= i < |xs| ==> f(xs[i]).Success?) && (0 <= i < |xs| ==> result.value[i] == f(xs[i]).value)
    decreases set i: int, o: object? {:trigger o in f.reads(xs[i])} | 0 <= i < |xs| && o in f.reads(xs[i]) :: o, xs
  {
    if |xs| == 0 then
      Success([])
    else
      var head: R :- f(xs[0]); var tail: seq<R> :- MapWithResult(f, xs[1..]); Success([head] + tail)
  }

  lemma {:opaque} LemmaMapDistributesOverConcat<T, R>(f: T ~> R, xs: seq<T>, ys: seq<T>)
    requires forall i: int {:trigger xs[i]} :: 0 <= i < |xs| ==> f.requires(xs[i])
    requires forall j: int {:trigger ys[j]} :: 0 <= j < |ys| ==> f.requires(ys[j])
    ensures Map(f, xs + ys) == Map(f, xs) + Map(f, ys)
    decreases xs, ys
  {
  }

  function method {:opaque} {:fuel 0, 0} Filter<T>(f: T ~> bool, xs: seq<T>): (result: seq<T>)
    requires forall i: int {:trigger xs[i]} :: 0 <= i < |xs| ==> f.requires(xs[i])
    reads set i: int, o: object? {:trigger o in f.reads(xs[i])} | 0 <= i < |xs| && o in f.reads(xs[i]) :: o
    ensures |result| <= |xs|
    ensures forall i: nat {:trigger result[i]} :: i < |result| && f.requires(result[i]) ==> f(result[i])
    decreases set i: int, o: object? {:trigger o in f.reads(xs[i])} | 0 <= i < |xs| && o in f.reads(xs[i]) :: o, xs
  {
    if |xs| == 0 then
      []
    else
      (if f(xs[0]) then [xs[0]] else []) + Filter(f, xs[1..])
  }

  lemma {:opaque} /*{:_induction f, xs, ys}*/ LemmaFilterDistributesOverConcat<T>(f: T ~> bool, xs: seq<T>, ys: seq<T>)
    requires forall i: int {:trigger xs[i]} :: 0 <= i < |xs| ==> f.requires(xs[i])
    requires forall j: int {:trigger ys[j]} :: 0 <= j < |ys| ==> f.requires(ys[j])
    ensures Filter(f, xs + ys) == Filter(f, xs) + Filter(f, ys)
    decreases xs, ys
  {
  }

  function method {:opaque} {:fuel 0, 0} FoldLeft<A, T>(f: (A, T) -> A, init: A, xs: seq<T>): A
    decreases xs
  {
    if |xs| == 0 then
      init
    else
      FoldLeft(f, f(init, xs[0]), xs[1..])
  }

  lemma {:opaque} /*{:_induction f, xs, ys}*/ LemmaFoldLeftDistributesOverConcat<A, T>(f: (A, T) -> A, init: A, xs: seq<T>, ys: seq<T>)
    requires 0 <= |xs + ys|
    ensures FoldLeft(f, init, xs + ys) == FoldLeft(f, FoldLeft(f, init, xs), ys)
    decreases xs, ys
  {
  }

  predicate InvFoldLeft<A(!new), B(!new)>(inv: (B, seq<A>) -> bool, stp: (B, A, B) -> bool)
  {
    forall x: A, xs: seq<A>, b: B, b': B {:trigger stp(b, x, b'), [x] + xs} :: 
      inv(b, [x] + xs) &&
      stp(b, x, b') ==>
        inv(b', xs)
  }

  lemma /*{:_induction f, xs}*/ LemmaInvFoldLeft<A, B>(inv: (B, seq<A>) -> bool, stp: (B, A, B) -> bool, f: (B, A) -> B, b: B, xs: seq<A>)
    requires InvFoldLeft(inv, stp)
    requires forall b: B, a: A {:trigger f(b, a)} :: stp(b, a, f(b, a))
    requires inv(b, xs)
    ensures inv(FoldLeft(f, b, xs), [])
    decreases xs
  {
  }

  function method {:opaque} {:fuel 0, 0} FoldRight<A, T>(f: (T, A) -> A, xs: seq<T>, init: A): A
    decreases xs
  {
    if |xs| == 0 then
      init
    else
      f(xs[0], FoldRight(f, xs[1..], init))
  }

  lemma {:opaque} /*{:_induction f, xs, ys}*/ LemmaFoldRightDistributesOverConcat<A, T>(f: (T, A) -> A, init: A, xs: seq<T>, ys: seq<T>)
    requires 0 <= |xs + ys|
    ensures FoldRight(f, xs + ys, init) == FoldRight(f, xs, FoldRight(f, ys, init))
    decreases xs, ys
  {
  }

  predicate InvFoldRight<A(!new), B(!new)>(inv: (seq<A>, B) -> bool, stp: (A, B, B) -> bool)
  {
    forall x: A, xs: seq<A>, b: B, b': B {:trigger [x] + xs, stp(x, b, b')} :: 
      inv(xs, b) &&
      stp(x, b, b') ==>
        inv([x] + xs, b')
  }

  lemma /*{:_induction f, xs}*/ LemmaInvFoldRight<A, B>(inv: (seq<A>, B) -> bool, stp: (A, B, B) -> bool, f: (A, B) -> B, b: B, xs: seq<A>)
    requires InvFoldRight(inv, stp)
    requires forall a: A, b: B {:trigger f(a, b)} :: stp(a, b, f(a, b))
    requires inv([], b)
    ensures inv(xs, FoldRight(f, xs, b))
    decreases xs
  {
  }

  function FlatMap<T, R>(f: T ~> seq<R>, xs: seq<T>): (result: seq<R>)
    requires forall i: int {:trigger xs[i]} :: 0 <= i < |xs| ==> f.requires(xs[i])
    reads set i: int, o: object? {:trigger o in f.reads(xs[i])} | 0 <= i < |xs| && o in f.reads(xs[i]) :: o
    decreases set i: int, o: object? {:trigger o in f.reads(xs[i])} | 0 <= i < |xs| && o in f.reads(xs[i]) :: o, xs
  {
    Flatten(Map(f, xs))
  } by method {
    result := [];
    ghost var unflattened: seq<seq<R>> := [];
    for i: int := |xs| downto 0
      invariant unflattened == Map(f, xs[i..])
      invariant result == Flatten(unflattened)
    {
      var next := f(xs[i]);
      unflattened := [next] + unflattened;
      result := next + result;
    }
  }

  function SetToSeqSpec<T>(s: set<T>): (xs: seq<T>)
    ensures multiset(s) == multiset(xs)
    decreases s
  {
    if s == {} then
      []
    else
      ghost var x: T :| x in s; [x] + SetToSeqSpec(s - {x})
  }

  method SetToSeq<T>(s: set<T>) returns (xs: seq<T>)
    ensures multiset(s) == multiset(xs)
    decreases s
  {
    xs := [];
    var left: set<T> := s;
    while left != {}
      invariant multiset(left) + multiset(xs) == multiset(s)
      decreases left
    {
      var x :| x in left;
      left := left - {x};
      xs := xs + [x];
    }
  }

  lemma SortedUnique<T>(xs: seq<T>, ys: seq<T>, R: (T, T) -> bool)
    requires SortedBy(xs, R)
    requires SortedBy(ys, R)
    requires TotalOrdering(R)
    requires multiset(xs) == multiset(ys)
    ensures xs == ys
    decreases xs, ys
  {
  }

  function SetToSortedSeq<T>(s: set<T>, R: (T, T) -> bool): (xs: seq<T>)
    requires TotalOrdering(R)
    ensures multiset(s) == multiset(xs)
    ensures SortedBy(xs, R)
    decreases s
  {
    MergeSortBy(SetToSeqSpec(s), R)
  } by method {
    xs := SetToSeq(s);
    xs := MergeSortBy(xs, R);
    SortedUnique(xs, SetToSortedSeq(s, R), R);
  }

  module {:options ""-functionSyntax:4""} MergeSort {

    import opened Relations
    function method MergeSortBy<T>(a: seq<T>, lessThanOrEq: (T, T) -> bool): (result: seq<T>)
      requires TotalOrdering(lessThanOrEq)
      ensures multiset(a) == multiset(result)
      ensures SortedBy(result, lessThanOrEq)
      decreases a
    {
      if |a| <= 1 then
        a
      else
        var splitIndex: int := |a| / 2; var left: seq<T>, right: seq<T> := a[..splitIndex], a[splitIndex..]; assert a == left + right; var leftSorted: seq<T> := MergeSortBy(left, lessThanOrEq); var rightSorted: seq<T> := MergeSortBy(right, lessThanOrEq); MergeSortedWith(leftSorted, rightSorted, lessThanOrEq)
    }

    function method {:tailrecursion} MergeSortedWith<T>(left: seq<T>, right: seq<T>, lessThanOrEq: (T, T) -> bool): (result: seq<T>)
      requires SortedBy(left, lessThanOrEq)
      requires SortedBy(right, lessThanOrEq)
      requires TotalOrdering(lessThanOrEq)
      ensures multiset(left + right) == multiset(result)
      ensures SortedBy(result, lessThanOrEq)
      decreases left, right
    {
      if |left| == 0 then
        right
      else if |right| == 0 then
        left
      else if lessThanOrEq(left[0], right[0]) then
        LemmaNewFirstElementStillSortedBy(left[0], MergeSortedWith(left[1..], right, lessThanOrEq), lessThanOrEq);
        assert left == [left[0]] + left[1..];
        [left[0]] + MergeSortedWith(left[1..], right, lessThanOrEq)
      else
        LemmaNewFirstElementStillSortedBy(right[0], MergeSortedWith(left, right[1..], lessThanOrEq), lessThanOrEq); assert right == [right[0]] + right[1..]; [right[0]] + MergeSortedWith(left, right[1..], lessThanOrEq)
    }
  }
}

module {:options ""-functionSyntax:4""} Math {
  function method Min(a: int, b: int): int
    decreases a, b
  {
    if a < b then
      a
    else
      b
  }

  function method Max(a: int, b: int): int
    decreases a, b
  {
    if a < b then
      b
    else
      a
  }

  function method Abs(a: int): (a': int)
    ensures a' >= 0
    decreases a
  {
    if a >= 0 then
      a
    else
      -a
  }
}

module {:options ""-functionSyntax:4""} Relations {
  predicate Reflexive<T(!new)>(R: (T, T) -> bool)
  {
    forall x: T {:trigger R(x, x)} :: 
      R(x, x)
  }

  predicate Irreflexive<T(!new)>(R: (T, T) -> bool)
  {
    forall x: T {:trigger R(x, x)} :: 
      !R(x, x)
  }

  predicate AntiSymmetric<T(!new)>(R: (T, T) -> bool)
  {
    forall x: T, y: T {:trigger R(y, x)} {:trigger R(x, y)} :: 
      R(x, y) &&
      R(y, x) ==>
        x == y
  }

  predicate Symmetric<T(!new)>(R: (T, T) -> bool)
  {
    forall x: T, y: T {:trigger R(y, x)} {:trigger R(x, y)} :: 
      R(x, y) <==> R(y, x)
  }

  predicate Connected<T(!new)>(R: (T, T) -> bool)
  {
    forall x: T, y: T {:trigger R(y, x)} {:trigger R(x, y)} :: 
      x != y ==>
        R(x, y) || R(y, x)
  }

  predicate StronglyConnected<T(!new)>(R: (T, T) -> bool)
  {
    forall x: T, y: T {:trigger R(y, x)} {:trigger R(x, y)} :: 
      R(x, y) || R(y, x)
  }

  predicate Transitive<T(!new)>(R: (T, T) -> bool)
  {
    forall x: T, y: T, z: T {:trigger R(x, z), R(y, z)} {:trigger R(y, z), R(x, y)} :: 
      R(x, y) &&
      R(y, z) ==>
        R(x, z)
  }

  predicate TotalOrdering<T(!new)>(R: (T, T) -> bool)
  {
    Reflexive(R) &&
    AntiSymmetric(R) &&
    Transitive(R) &&
    StronglyConnected(R)
  }

  predicate StrictTotalOrdering<T(!new)>(R: (T, T) -> bool)
  {
    Irreflexive(R) &&
    AntiSymmetric(R) &&
    Transitive(R) &&
    Connected(R)
  }

  predicate PreOrdering<T(!new)>(R: (T, T) -> bool)
  {
    Reflexive(R) &&
    Transitive(R)
  }

  predicate PartialOrdering<T(!new)>(R: (T, T) -> bool)
  {
    Reflexive(R) &&
    Transitive(R) &&
    AntiSymmetric(R)
  }

  predicate EquivalenceRelation<T(!new)>(R: (T, T) -> bool)
  {
    Reflexive(R) &&
    Symmetric(R) &&
    Transitive(R)
  }

  predicate SortedBy<T>(a: seq<T>, lessThan: (T, T) -> bool)
    decreases a
  {
    forall i: int, j: int {:trigger a[j], a[i]} | 0 <= i < j < |a| :: 
      lessThan(a[i], a[j])
  }

  predicate IsLeast<T>(R: (T, T) -> bool, min: T, s: set<T>)
    decreases s
  {
    min in s &&
    forall x: T {:trigger R(min, x)} {:trigger x in s} | x in s :: 
      R(min, x)
  }

  predicate IsMinimal<T>(R: (T, T) -> bool, min: T, s: set<T>)
    decreases s
  {
    min in s &&
    forall x: T {:trigger R(min, x)} {:trigger R(x, min)} {:trigger x in s} | x in s && R(x, min) :: 
      R(min, x)
  }

  predicate IsGreatest<T>(R: (T, T) -> bool, max: T, s: set<T>)
    decreases s
  {
    max in s &&
    forall x: T {:trigger R(x, max)} {:trigger x in s} | x in s :: 
      R(x, max)
  }

  predicate IsMaximal<T>(R: (T, T) -> bool, max: T, s: set<T>)
    decreases s
  {
    max in s &&
    forall x: T {:trigger R(x, max)} {:trigger R(max, x)} {:trigger x in s} | x in s && R(max, x) :: 
      R(x, max)
  }

  lemma LemmaNewFirstElementStillSortedBy<T>(x: T, s: seq<T>, lessThan: (T, T) -> bool)
    requires SortedBy(s, lessThan)
    requires |s| == 0 || lessThan(x, s[0])
    requires TotalOrdering(lessThan)
    ensures SortedBy([x] + s, lessThan)
    decreases s
  {
  }
}

module Base64 {

  import opened Wrappers

  import opened UInt = StandardLibrary.UInt
  newtype index = x: int
    | 0 <= x < 64

  newtype uint24 = x: int
    | 0 <= x < 16777216

  predicate method IsBase64Char(c: char)
    decreases c
  {
    c == '+' || c == '/' || '0' <= c <= '9' || 'A' <= c <= 'Z' || 'a' <= c <= 'z'
  }

  predicate method IsUnpaddedBase64String(s: string)
    decreases s
  {
    |s| % 4 == 0 &&
    forall k: char {:trigger IsBase64Char(k)} {:trigger k in s} :: 
      k in s ==>
        IsBase64Char(k)
  }

  function method IndexToChar(i: index): (c: char)
    ensures IsBase64Char(c)
    decreases i
  {
    if i == 63 then
      '/'
    else if i == 62 then
      '+'
    else if 52 <= i <= 61 then
      (i - 4) as char
    else if 26 <= i <= 51 then
      i as char + 71 as char
    else
      i as char + 65 as char
  }

  function method CharToIndex(c: char): (i: index)
    requires IsBase64Char(c)
    ensures IndexToChar(i) == c
    decreases c
  {
    if c == '/' then
      63
    else if c == '+' then
      62
    else if '0' <= c <= '9' then
      (c + 4 as char) as index
    else if 'a' <= c <= 'z' then
      (c - 71 as char) as index
    else
      (c - 65 as char) as index
  }

  lemma CharToIndexToChar(x: char)
    requires IsBase64Char(x)
    ensures IndexToChar(CharToIndex(x)) == x
    decreases x
  {
  }

  lemma IndexToCharToIndex(x: index)
    ensures CharToIndex(IndexToChar(x)) == x
    decreases x
  {
  }

  function method UInt24ToSeq(x: uint24): (ret: seq<uint8>)
    ensures |ret| == 3
    ensures ret[0] as uint24 * 65536 + ret[1] as uint24 * 256 + ret[2] as uint24 == x
    decreases x
  {
    var b0: uint8 := (x / 65536) as uint8;
    var x0: uint24 := x - b0 as uint24 * 65536;
    var b1: uint8 := (x0 / 256) as uint8;
    var b2: uint8 := (x0 % 256) as uint8;
    [b0, b1, b2]
  }

  function method SeqToUInt24(s: seq<uint8>): (x: uint24)
    requires |s| == 3
    ensures UInt24ToSeq(x) == s
    decreases s
  {
    s[0] as uint24 * 65536 + s[1] as uint24 * 256 + s[2] as uint24
  }

  lemma UInt24ToSeqToUInt24(x: uint24)
    ensures SeqToUInt24(UInt24ToSeq(x)) == x
    decreases x
  {
  }

  lemma SeqToUInt24ToSeq(s: seq<uint8>)
    requires |s| == 3
    ensures UInt24ToSeq(SeqToUInt24(s)) == s
    decreases s
  {
  }

  function method UInt24ToIndexSeq(x: uint24): (ret: seq<index>)
    ensures |ret| == 4
    ensures ret[0] as uint24 * 262144 + ret[1] as uint24 * 4096 + ret[2] as uint24 * 64 + ret[3] as uint24 == x
    decreases x
  {
    var b0: index := (x / 262144) as index;
    var x0: uint24 := x - b0 as uint24 * 262144;
    var b1: index := (x0 / 4096) as index;
    var x1: uint24 := x0 - b1 as uint24 * 4096;
    var b2: index := (x1 / 64) as index;
    var b3: index := (x1 % 64) as index;
    [b0, b1, b2, b3]
  }

  function method {:vcs_split_on_every_assert} IndexSeqToUInt24(s: seq<index>): (x: uint24)
    requires |s| == 4
    ensures UInt24ToIndexSeq(x) == s
    decreases s
  {
    s[0] as uint24 * 262144 + s[1] as uint24 * 4096 + s[2] as uint24 * 64 + s[3] as uint24
  }

  lemma UInt24ToIndexSeqToUInt24(x: uint24)
    ensures IndexSeqToUInt24(UInt24ToIndexSeq(x)) == x
    decreases x
  {
  }

  lemma IndexSeqToUInt24ToIndexSeq(s: seq<index>)
    requires |s| == 4
    ensures UInt24ToIndexSeq(IndexSeqToUInt24(s)) == s
    decreases s
  {
  }

  function method DecodeBlock(s: seq<index>): (ret: seq<uint8>)
    requires |s| == 4
    ensures |ret| == 3
    ensures UInt24ToIndexSeq(SeqToUInt24(ret)) == s
    decreases s
  {
    UInt24ToSeq(IndexSeqToUInt24(s))
  }

  function method EncodeBlock(s: seq<uint8>): (ret: seq<index>)
    requires |s| == 3
    ensures |ret| == 4
    ensures UInt24ToSeq(IndexSeqToUInt24(ret)) == s
    ensures DecodeBlock(ret) == s
    decreases s
  {
    UInt24ToIndexSeq(SeqToUInt24(s))
  }

  lemma EncodeDecodeBlock(s: seq<uint8>)
    requires |s| == 3
    ensures DecodeBlock(EncodeBlock(s)) == s
    decreases s
  {
  }

  lemma DecodeEncodeBlock(s: seq<index>)
    requires |s| == 4
    ensures EncodeBlock(DecodeBlock(s)) == s
    decreases s
  {
  }

  function method DecodeRecursively(s: seq<index>): (b: seq<uint8>)
    requires |s| % 4 == 0
    ensures |b| == |s| / 4 * 3
    ensures |b| % 3 == 0
    ensures |b| == 0 ==> |s| == 0
    ensures |b| != 0 ==> EncodeBlock(b[..3]) == s[..4]
    decreases |s|
  {
    if |s| == 0 then
      []
    else
      DecodeBlock(s[..4]) + DecodeRecursively(s[4..])
  }

  function method EncodeRecursively(b: seq<uint8>): (s: seq<index>)
    requires |b| % 3 == 0
    ensures |s| == |b| / 3 * 4
    ensures |s| % 4 == 0
    ensures DecodeRecursively(s) == b
    decreases b
  {
    if |b| == 0 then
      []
    else
      EncodeBlock(b[..3]) + EncodeRecursively(b[3..])
  }

  lemma /*{:_induction s}*/ DecodeEncodeRecursively(s: seq<index>)
    requires |s| % 4 == 0
    ensures EncodeRecursively(DecodeRecursively(s)) == s
    decreases s
  {
  }

  lemma /*{:_induction b}*/ EncodeDecodeRecursively(b: seq<uint8>)
    requires |b| % 3 == 0
    ensures DecodeRecursively(EncodeRecursively(b)) == b
    decreases b
  {
  }

  function method FromCharsToIndices(s: seq<char>): (b: seq<index>)
    requires forall k: char {:trigger IsBase64Char(k)} {:trigger k in s} :: k in s ==> IsBase64Char(k)
    ensures |b| == |s|
    ensures forall k: int {:trigger s[k]} {:trigger b[k]} :: 0 <= k < |b| ==> IndexToChar(b[k]) == s[k]
    decreases s
  {
    seq(|s|, (i: int) requires 0 <= i < |s| => CharToIndex(s[i]))
  }

  function method FromIndicesToChars(b: seq<index>): (s: seq<char>)
    ensures forall k: char {:trigger IsBase64Char(k)} {:trigger k in s} :: k in s ==> IsBase64Char(k)
    ensures |s| == |b|
    ensures forall k: int {:trigger b[k]} {:trigger s[k]} :: 0 <= k < |s| ==> CharToIndex(s[k]) == b[k]
    ensures FromCharsToIndices(s) == b
    decreases b
  {
    seq(|b|, (i: int) requires 0 <= i < |b| => IndexToChar(b[i]))
  }

  lemma FromCharsToIndicesToChars(s: seq<char>)
    requires forall k: char {:trigger IsBase64Char(k)} {:trigger k in s} :: k in s ==> IsBase64Char(k)
    ensures FromIndicesToChars(FromCharsToIndices(s)) == s
    decreases s
  {
  }

  lemma FromIndicesToCharsToIndices(b: seq<index>)
    ensures FromCharsToIndices(FromIndicesToChars(b)) == b
    decreases b
  {
  }

  function method DecodeUnpadded(s: seq<char>): (b: seq<uint8>)
    requires IsUnpaddedBase64String(s)
    ensures |b| == |s| / 4 * 3
    ensures |b| % 3 == 0
    decreases s
  {
    DecodeRecursively(FromCharsToIndices(s))
  }

  function method EncodeUnpadded(b: seq<uint8>): (s: seq<char>)
    requires |b| % 3 == 0
    ensures IsUnpaddedBase64String(s)
    ensures |s| == |b| / 3 * 4
    ensures DecodeUnpadded(s) == b
    ensures |s| % 4 == 0
    decreases b
  {
    FromIndicesToChars(EncodeRecursively(b))
  }

  lemma EncodeDecodeUnpadded(b: seq<uint8>)
    requires |b| % 3 == 0
    ensures DecodeUnpadded(EncodeUnpadded(b)) == b
    decreases b
  {
  }

  lemma DecodeEncodeUnpadded(s: seq<char>)
    requires |s| % 4 == 0
    requires IsUnpaddedBase64String(s)
    ensures EncodeUnpadded(DecodeUnpadded(s)) == s
    decreases s
  {
  }

  predicate method Is1Padding(s: seq<char>)
    decreases s
  {
    |s| == 4 &&
    IsBase64Char(s[0]) &&
    IsBase64Char(s[1]) &&
    IsBase64Char(s[2]) &&
    CharToIndex(s[2]) % 4 == 0 &&
    s[3] == '='
  }

  function method Decode1Padding(s: seq<char>): (b: seq<uint8>)
    requires Is1Padding(s)
    ensures |b| == 2
    decreases s
  {
    var d: seq<uint8> := DecodeBlock([CharToIndex(s[0]), CharToIndex(s[1]), CharToIndex(s[2]), 0]);
    [d[0], d[1]]
  }

  function method Encode1Padding(b: seq<uint8>): (s: seq<char>)
    requires |b| == 2
    ensures Is1Padding(s)
    ensures Decode1Padding(s) == b
    ensures |s| % 4 == 0
    decreases b
  {
    var e: seq<index> := EncodeBlock([b[0], b[1], 0]);
    [IndexToChar(e[0]), IndexToChar(e[1]), IndexToChar(e[2]), '=']
  }

  lemma DecodeEncode1Padding(s: seq<char>)
    requires Is1Padding(s)
    ensures Encode1Padding(Decode1Padding(s)) == s
    decreases s
  {
  }

  lemma EncodeDecode1Padding(b: seq<uint8>)
    requires |b| == 2
    ensures Decode1Padding(Encode1Padding(b)) == b
    decreases b
  {
  }

  predicate method Is2Padding(s: seq<char>)
    decreases s
  {
    |s| == 4 &&
    IsBase64Char(s[0]) &&
    IsBase64Char(s[1]) &&
    CharToIndex(s[1]) % 16 == 0 &&
    s[2] == '=' &&
    s[3] == '='
  }

  function method Decode2Padding(s: seq<char>): (b: seq<uint8>)
    requires Is2Padding(s)
    ensures |b| == 1
    decreases s
  {
    var d: seq<uint8> := DecodeBlock([CharToIndex(s[0]), CharToIndex(s[1]), 0, 0]);
    [d[0]]
  }

  function method Encode2Padding(b: seq<uint8>): (s: seq<char>)
    requires |b| == 1
    ensures Is2Padding(s)
    ensures Decode2Padding(s) == b
    ensures |s| % 4 == 0
    decreases b
  {
    var e: seq<index> := EncodeBlock([b[0], 0, 0]);
    [IndexToChar(e[0]), IndexToChar(e[1]), '=', '=']
  }

  lemma DecodeEncode2Padding(s: seq<char>)
    requires Is2Padding(s)
    ensures Encode2Padding(Decode2Padding(s)) == s
    decreases s
  {
  }

  lemma EncodeDecode2Padding(b: seq<uint8>)
    requires |b| == 1
    ensures Decode2Padding(Encode2Padding(b)) == b
    decreases b
  {
  }

  predicate method IsBase64String(s: string)
    decreases s
  {
    var finalBlockStart: int := |s| - 4;
    |s| % 4 == 0 &&
    (IsUnpaddedBase64String(s) || (IsUnpaddedBase64String(s[..finalBlockStart]) && (Is1Padding(s[finalBlockStart..]) || Is2Padding(s[finalBlockStart..]))))
  }

  function method DecodeValid(s: seq<char>): (b: seq<uint8>)
    requires IsBase64String(s)
    decreases s
  {
    if s == [] then
      []
    else
      var finalBlockStart: int := |s| - 4; var prefix: seq<char>, suffix: seq<char> := s[..finalBlockStart], s[finalBlockStart..]; if Is1Padding(suffix) then DecodeUnpadded(prefix) + Decode1Padding(suffix) else if Is2Padding(suffix) then DecodeUnpadded(prefix) + Decode2Padding(suffix) else DecodeUnpadded(s)
  }

  lemma AboutDecodeValid(s: seq<char>, b: seq<uint8>)
    requires IsBase64String(s) && b == DecodeValid(s)
    ensures 4 <= |s| ==> ghost var finalBlockStart: int := |s| - 4; ghost var prefix: seq<char>, suffix: seq<char> := s[..finalBlockStart], s[finalBlockStart..]; (Is1Padding(suffix) ==> |b| % 3 == 2) && (Is2Padding(suffix) ==> |b| % 3 == 1) && (!Is1Padding(suffix) && !Is2Padding(suffix) ==> |b| % 3 == 0)
    decreases s, b
  {
  }

  lemma Mod3(x: nat, k: nat, n: nat)
    requires 0 <= k < 3 && n == 3 * x + k
    ensures n % 3 == k
    decreases x, k, n
  {
  }

  function method Decode(s: seq<char>): (b: Result<seq<uint8>, string>)
    ensures IsBase64String(s) ==> b.Success?
    ensures !IsBase64String(s) ==> b.Failure?
    decreases s
  {
    if IsBase64String(s) then
      Success(DecodeValid(s))
    else
      Failure(""The encoding is malformed"")
  }

  predicate StringIs7Bit(s: string)
    decreases s
  {
    forall i: int {:trigger s[i]} :: 
      0 <= i < |s| ==>
        s[i] < 128 as char
  }

  lemma ConcatMod4Sequences<T>(s: seq<T>, t: seq<T>)
    requires |s| % 4 == 0
    requires |t| % 4 == 0
    ensures |s + t| % 4 == 0
    decreases s, t
  {
  }

  function method {:vcs_split_on_every_assert} Encode(b: seq<uint8>): (s: seq<char>)
    ensures StringIs7Bit(s)
    ensures |s| % 4 == 0
    ensures IsBase64String(s)
    decreases b
  {
    if |b| % 3 == 0 then
      var s: seq<char> := EncodeUnpadded(b);
      assert |s| % 4 == 0;
      s
    else if |b| % 3 == 1 then
      assert |b| >= 1;
      var s1: seq<char>, s2: seq<char> := EncodeUnpadded(b[..|b| - 1]), Encode2Padding(b[|b| - 1..]);
      ConcatMod4Sequences(s1, s2);
      var s: seq<char> := s1 + s2;
      assert |s| % 4 == 0;
      s
    else
      assert |b| % 3 == 2; assert |b| >= 2; var s1: seq<char>, s2: seq<char> := EncodeUnpadded(b[..|b| - 2]), Encode1Padding(b[|b| - 2..]); ConcatMod4Sequences(s1, s2); var s: seq<char> := s1 + s2; assert |s| % 4 == 0; s
  }

  lemma EncodeLengthExact(b: seq<uint8>)
    ensures ghost var s: seq<char> := Encode(b); (|b| % 3 == 0 ==> |s| == |b| / 3 * 4) && (|b| % 3 != 0 ==> |s| == |b| / 3 * 4 + 4)
    decreases b
  {
  }

  lemma EncodeLengthBound(b: seq<uint8>)
    ensures ghost var s: seq<char> := Encode(b); |s| <= |b| / 3 * 4 + 4
    decreases b
  {
  }
}

module StandardLibrary {

  import opened Wrappers

  import opened U = UInt
  lemma SeqTakeAppend<A>(s: seq<A>, i: int)
    requires 0 <= i < |s|
    ensures s[..i] + [s[i]] == s[..i + 1]
    decreases s, i
  {
  }

  function method {:tailrecursion} Join<T>(ss: seq<seq<T>>, joiner: seq<T>): (s: seq<T>)
    requires 0 < |ss|
    decreases ss, joiner
  {
    if |ss| == 1 then
      ss[0]
    else
      ss[0] + joiner + Join(ss[1..], joiner)
  }

  function method {:tailrecursion} Split<T(==)>(s: seq<T>, delim: T): (res: seq<seq<T>>)
    ensures delim !in s ==> res == [s]
    ensures s == [] ==> res == [[]]
    ensures 0 < |res|
    ensures forall i: int {:trigger res[i]} :: 0 <= i < |res| ==> delim !in res[i]
    ensures Join(res, [delim]) == s
    decreases |s|
  {
    var i: Option<nat> := FindIndexMatching(s, delim, 0);
    if i.Some? then
      [s[..i.value]] + Split(s[i.value + 1..], delim)
    else
      [s]
  }

  function method {:tailrecursion} SplitOnce<T(==)>(s: seq<T>, delim: T): (res: (seq<T>, seq<T>))
    requires delim in s
    ensures res.0 + [delim] + res.1 == s
    ensures !(delim in res.0)
    decreases s
  {
    var i: Option<nat> := FindIndexMatching(s, delim, 0);
    assert i.Some?;
    (s[..i.value], s[i.value + 1..])
  }

  function method {:tailrecursion} SplitOnce?<T(==)>(s: seq<T>, delim: T): (res: Option<(seq<T>, seq<T>)>)
    ensures res.Some? ==> res.value.0 + [delim] + res.value.1 == s
    ensures res.None? ==> !(delim in s)
    ensures res.Some? ==> !(delim in res.value.0)
    decreases s
  {
    var i: nat :- FindIndexMatching(s, delim, 0); Some((s[..i], s[i + 1..]))
  }

  lemma /*{:_induction s}*/ WillSplitOnDelim<T>(s: seq<T>, delim: T, prefix: seq<T>)
    requires |prefix| < |s|
    requires forall i: int {:trigger s[i]} {:trigger prefix[i]} :: 0 <= i < |prefix| ==> prefix[i] == s[i]
    requires delim !in prefix && s[|prefix|] == delim
    ensures Split(s, delim) == [prefix] + Split(s[|prefix| + 1..], delim)
    decreases s, prefix
  {
  }

  lemma /*{:_induction s}*/ WillNotSplitWithOutDelim<T>(s: seq<T>, delim: T)
    requires delim !in s
    ensures Split(s, delim) == [s]
    decreases s
  {
  }

  lemma FindIndexMatchingLocatesElem<T>(s: seq<T>, c: T, start: nat, elemIndex: nat)
    requires start <= elemIndex <= |s|
    requires forall i: int {:trigger s[i]} :: start <= i < elemIndex ==> s[i] != c
    requires elemIndex == |s| || s[elemIndex] == c
    ensures FindIndexMatching(s, c, start) == if elemIndex == |s| then None else Some(elemIndex)
    decreases elemIndex - start
  {
  }

  function method FindIndexMatching<T(==)>(s: seq<T>, c: T, i: nat): (index: Option<nat>)
    requires i <= |s|
    ensures index.Some? ==> i <= index.value < |s| && s[index.value] == c && c !in s[i .. index.value]
    ensures index.None? ==> c !in s[i..]
    decreases |s| - i
  {
    FindIndex(s, (x: T) => x == c, i)
  }

  function method {:tailrecursion} FindIndex<T>(s: seq<T>, f: T -> bool, i: nat): (index: Option<nat>)
    requires i <= |s|
    ensures index.Some? ==> i <= index.value < |s| && f(s[index.value]) && forall j: int {:trigger s[j]} :: i <= j < index.value ==> !f(s[j])
    ensures index.None? ==> forall j: int {:trigger s[j]} :: i <= j < |s| ==> !f(s[j])
    decreases |s| - i
  {
    if i == |s| then
      None
    else if f(s[i]) then
      Some(i)
    else
      FindIndex(s, f, i + 1)
  }

  function method {:tailrecursion} Filter<T>(s: seq<T>, f: T -> bool): (res: seq<T>)
    ensures forall i: int {:trigger s[i]} :: 0 <= i < |s| && f(s[i]) ==> s[i] in res
    ensures forall i: int {:trigger res[i]} :: (0 <= i < |res| ==> res[i] in s) && (0 <= i < |res| ==> f(res[i]))
    ensures |res| <= |s|
    decreases s
  {
    if |s| == 0 then
      []
    else if f(s[0]) then
      [s[0]] + Filter(s[1..], f)
    else
      Filter(s[1..], f)
  }

  lemma /*{:_induction s, s', f}*/ FilterIsDistributive<T>(s: seq<T>, s': seq<T>, f: T -> bool)
    ensures Filter(s + s', f) == Filter(s, f) + Filter(s', f)
    decreases s, s'
  {
  }

  function method Min(a: int, b: int): int
    decreases a, b
  {
    if a < b then
      a
    else
      b
  }

  function method Fill<T>(value: T, n: nat): seq<T>
    ensures |Fill(value, n)| == n
    ensures forall i: int {:trigger Fill(value, n)[i]} :: 0 <= i < n ==> Fill(value, n)[i] == value
    decreases n
  {
    seq(n, (_ /* _v0 */: int) => value)
  }

  method SeqToArray<T>(s: seq<T>) returns (a: array<T>)
    ensures fresh(a)
    ensures a.Length == |s|
    ensures forall i: int {:trigger s[i]} {:trigger a[i]} :: 0 <= i < |s| ==> a[i] == s[i]
    decreases s
  {
    a := new T[|s|] ((i: int) requires 0 <= i < |s| => s[i]);
  }

  lemma SeqPartsMakeWhole<T>(s: seq<T>, i: nat)
    requires 0 <= i <= |s|
    ensures s[..i] + s[i..] == s
    decreases s, i
  {
  }

  predicate method LexicographicLessOrEqual<T(==)>(a: seq<T>, b: seq<T>, less: (T, T) -> bool)
    decreases a, b
  {
    exists k: int {:trigger LexicographicLessOrEqualAux(a, b, less, k)} :: 
      0 <= k <= |a| &&
      LexicographicLessOrEqualAux(a, b, less, k)
  }

  predicate method LexicographicLessOrEqualAux<T(==)>(a: seq<T>, b: seq<T>, less: (T, T) -> bool, lengthOfCommonPrefix: nat)
    requires 0 <= lengthOfCommonPrefix <= |a|
    decreases a, b, lengthOfCommonPrefix
  {
    lengthOfCommonPrefix <= |b| &&
    (forall i: int {:trigger b[i]} {:trigger a[i]} :: 
      0 <= i < lengthOfCommonPrefix ==>
        a[i] == b[i]) &&
    (lengthOfCommonPrefix == |a| || (lengthOfCommonPrefix < |b| && less(a[lengthOfCommonPrefix], b[lengthOfCommonPrefix])))
  }

  predicate Trichotomous<T(!new)>(less: (T, T) -> bool)
  {
    (forall x: T, y: T {:trigger less(y, x)} {:trigger less(x, y)} :: 
      less(x, y) || x == y || less(y, x)) &&
    (forall x: T, y: T {:trigger less(y, x)} {:trigger less(x, y)} :: 
      less(x, y) &&
      less(y, x) ==>
        false) &&
    forall x: T, y: T {:trigger less(x, y)} :: 
      less(x, y) ==>
        x != y
  }

  predicate Transitive<T(!new)>(R: (T, T) -> bool)
  {
    forall x: T, y: T, z: T {:trigger R(x, z), R(y, z)} {:trigger R(y, z), R(x, y)} :: 
      R(x, y) &&
      R(y, z) ==>
        R(x, z)
  }

  lemma UInt8LessIsTrichotomousTransitive()
    ensures Trichotomous(UInt8Less)
    ensures Transitive(UInt8Less)
  {
  }

  lemma LexIsReflexive<T>(a: seq<T>, less: (T, T) -> bool)
    ensures LexicographicLessOrEqual(a, a, less)
    decreases a
  {
  }

  lemma LexIsAntisymmetric<T>(a: seq<T>, b: seq<T>, less: (T, T) -> bool)
    requires Trich: Trichotomous(less)
    requires LexicographicLessOrEqual(a, b, less)
    requires LexicographicLessOrEqual(b, a, less)
    ensures a == b
    decreases a, b
  {
  }

  lemma LexIsTransitive<T>(a: seq<T>, b: seq<T>, c: seq<T>, less: (T, T) -> bool)
    requires Transitive(less)
    requires LexicographicLessOrEqual(a, b, less)
    requires LexicographicLessOrEqual(b, c, less)
    ensures LexicographicLessOrEqual(a, c, less)
    decreases a, b, c
  {
  }

  lemma LexIsTotal<T>(a: seq<T>, b: seq<T>, less: (T, T) -> bool)
    requires Trich: Trichotomous(less)
    ensures LexicographicLessOrEqual(a, b, less) || LexicographicLessOrEqual(b, a, less)
    decreases a, b
  {
  }

  function method {:tailrecursion} SetToOrderedSequence<T(==,!new)>(s: set<seq<T>>, less: (T, T) -> bool): (q: seq<seq<T>>)
    requires Trichotomous(less) && Transitive(less)
    ensures |s| == |q|
    ensures forall i: int {:trigger q[i]} :: 0 <= i < |q| ==> q[i] in s
    ensures forall k: seq<T> {:trigger k in q} {:trigger k in s} :: k in s ==> k in q
    ensures forall i: int, _t#0: int {:trigger q[i], q[_t#0]} | _t#0 == i - 1 :: 0 < i && i < |q| ==> LexicographicLessOrEqual(q[_t#0], q[i], less)
    ensures forall i: int, j: int {:trigger q[j], q[i]} | 0 <= i < j < |q| :: q[i] != q[j]
    decreases s
  {
    if s == {} then
      []
    else
      ThereIsAMinimum(s, less); assert forall a: seq<T>, b: seq<T> {:trigger IsMinimum(b, s, less), IsMinimum(a, s, less)} :: IsMinimum(a, s, less) && IsMinimum(b, s, less) ==> a == b by {
    forall a: seq<T>, b: seq<T> | IsMinimum(a, s, less) && IsMinimum(b, s, less) {
      MinimumIsUnique(a, b, s, less);
    }
  } var a: seq<T> :| a in s && IsMinimum(a, s, less); [a] + SetToOrderedSequence(s - {a}, less)
  }

  predicate method IsMinimum<T(==)>(a: seq<T>, s: set<seq<T>>, less: (T, T) -> bool)
    decreases a, s
  {
    a in s &&
    forall z: seq<T> {:trigger LexicographicLessOrEqual(a, z, less)} {:trigger z in s} :: 
      z in s ==>
        LexicographicLessOrEqual(a, z, less)
  }

  lemma ThereIsAMinimum<T>(s: set<seq<T>>, less: (T, T) -> bool)
    requires s != {}
    requires Trichotomous(less) && Transitive(less)
    ensures exists a: seq<T> {:trigger IsMinimum(a, s, less)} :: IsMinimum(a, s, less)
    decreases s
  {
  }

  lemma MinimumIsUnique<T>(a: seq<T>, b: seq<T>, s: set<seq<T>>, less: (T, T) -> bool)
    requires IsMinimum(a, s, less) && IsMinimum(b, s, less)
    requires Trichotomous(less)
    ensures a == b
    decreases a, b, s
  {
  }

  lemma FindMinimum<T>(s: set<seq<T>>, less: (T, T) -> bool) returns (a: seq<T>)
    requires s != {}
    requires Trichotomous(less) && Transitive(less)
    ensures IsMinimum(a, s, less)
    decreases s
  {
  }

  module UInt {

    import BoundedInts
    type uint8 = BoundedInts.uint8

    type uint16 = BoundedInts.uint16

    type uint32 = BoundedInts.uint32

    type uint64 = BoundedInts.uint64

    type int32 = BoundedInts.int32

    type int64 = BoundedInts.int64

    type seq16<T> = s: seq<T>
      | HasUint16Len(s)

    type Uint8Seq16 = seq16<uint8>

    type seq32<T> = s: seq<T>
      | HasUint32Len(s)

    type Uint8Seq32 = seq32<uint8>

    type seq64<T> = s: seq<T>
      | HasUint64Len(s)

    type Uint8Seq64 = seq64<uint8>

    const UINT16_LIMIT := BoundedInts.UINT16_MAX as int + 1
    const UINT32_LIMIT := BoundedInts.UINT32_MAX as int + 1
    const UINT64_LIMIT := BoundedInts.UINT64_MAX as int + 1
    const INT32_MAX_LIMIT := BoundedInts.INT32_MAX as int
    const INT64_MAX_LIMIT := BoundedInts.INT64_MAX as int

    predicate method UInt8Less(a: uint8, b: uint8)
      decreases a, b
    {
      a < b
    }

    predicate method HasUint16Len<T>(s: seq<T>)
      decreases s
    {
      |s| < UINT16_LIMIT
    }

    predicate method HasUint32Len<T>(s: seq<T>)
      decreases s
    {
      |s| < UINT32_LIMIT
    }

    predicate method HasUint64Len<T>(s: seq<T>)
      decreases s
    {
      |s| < UINT64_LIMIT
    }

    function method UInt16ToSeq(x: uint16): (ret: seq<uint8>)
      ensures |ret| == 2
      ensures 256 * ret[0] as uint16 + ret[1] as uint16 == x
      decreases x
    {
      var b0: uint8 := (x / 256) as uint8;
      var b1: uint8 := (x % 256) as uint8;
      [b0, b1]
    }

    function method SeqToUInt16(s: seq<uint8>): (x: uint16)
      requires |s| == 2
      ensures UInt16ToSeq(x) == s
      ensures x >= 0
      decreases s
    {
      var x0: BoundedInts.uint16 := s[0] as uint16 * 256;
      x0 + s[1] as uint16
    }

    lemma UInt16SeqSerializeDeserialize(x: uint16)
      ensures SeqToUInt16(UInt16ToSeq(x)) == x
      decreases x
    {
    }

    lemma UInt16SeqDeserializeSerialize(s: seq<uint8>)
      requires |s| == 2
      ensures UInt16ToSeq(SeqToUInt16(s)) == s
      decreases s
    {
    }

    function method UInt32ToSeq(x: uint32): (ret: seq<uint8>)
      ensures |ret| == 4
      ensures 16777216 * ret[0] as uint32 + 65536 * ret[1] as uint32 + 256 * ret[2] as uint32 + ret[3] as uint32 == x
      decreases x
    {
      var b0: uint8 := (x / 16777216) as uint8;
      var x0: BoundedInts.uint32 := x - b0 as uint32 * 16777216;
      var b1: uint8 := (x0 / 65536) as uint8;
      var x1: BoundedInts.uint32 := x0 - b1 as uint32 * 65536;
      var b2: uint8 := (x1 / 256) as uint8;
      var b3: uint8 := (x1 % 256) as uint8;
      [b0, b1, b2, b3]
    }

    function method SeqToUInt32(s: seq<uint8>): (x: uint32)
      requires |s| == 4
      ensures UInt32ToSeq(x) == s
      decreases s
    {
      var x0: BoundedInts.uint32 := s[0] as uint32 * 16777216;
      var x1: BoundedInts.uint32 := x0 + s[1] as uint32 * 65536;
      var x2: BoundedInts.uint32 := x1 + s[2] as uint32 * 256;
      x2 + s[3] as uint32
    }

    lemma UInt32SeqSerializeDeserialize(x: uint32)
      ensures SeqToUInt32(UInt32ToSeq(x)) == x
      decreases x
    {
    }

    lemma UInt32SeqDeserializeSerialize(s: seq<uint8>)
      requires |s| == 4
      ensures UInt32ToSeq(SeqToUInt32(s)) == s
      decreases s
    {
    }

    function method UInt64ToSeq(x: uint64): (ret: seq<uint8>)
      ensures |ret| == 8
      ensures 72057594037927936 * ret[0] as uint64 + 281474976710656 * ret[1] as uint64 + 1099511627776 * ret[2] as uint64 + 4294967296 * ret[3] as uint64 + 16777216 * ret[4] as uint64 + 65536 * ret[5] as uint64 + 256 * ret[6] as uint64 + ret[7] as uint64 == x
      decreases x
    {
      var b0: uint8 := (x / 72057594037927936) as uint8;
      var x0: BoundedInts.uint64 := x - b0 as uint64 * 72057594037927936;
      var b1: uint8 := (x0 / 281474976710656) as uint8;
      var x1: BoundedInts.uint64 := x0 - b1 as uint64 * 281474976710656;
      var b2: uint8 := (x1 / 1099511627776) as uint8;
      var x2: BoundedInts.uint64 := x1 - b2 as uint64 * 1099511627776;
      var b3: uint8 := (x2 / 4294967296) as uint8;
      var x3: BoundedInts.uint64 := x2 - b3 as uint64 * 4294967296;
      var b4: uint8 := (x3 / 16777216) as uint8;
      var x4: BoundedInts.uint64 := x3 - b4 as uint64 * 16777216;
      var b5: uint8 := (x4 / 65536) as uint8;
      var x5: BoundedInts.uint64 := x4 - b5 as uint64 * 65536;
      var b6: uint8 := (x5 / 256) as uint8;
      var b7: uint8 := (x5 % 256) as uint8;
      [b0, b1, b2, b3, b4, b5, b6, b7]
    }

    function method SeqToUInt64(s: seq<uint8>): (x: uint64)
      requires |s| == 8
      ensures UInt64ToSeq(x) == s
      decreases s
    {
      var x0: BoundedInts.uint64 := s[0] as uint64 * 72057594037927936;
      var x1: BoundedInts.uint64 := x0 + s[1] as uint64 * 281474976710656;
      var x2: BoundedInts.uint64 := x1 + s[2] as uint64 * 1099511627776;
      var x3: BoundedInts.uint64 := x2 + s[3] as uint64 * 4294967296;
      var x4: BoundedInts.uint64 := x3 + s[4] as uint64 * 16777216;
      var x5: BoundedInts.uint64 := x4 + s[5] as uint64 * 65536;
      var x6: BoundedInts.uint64 := x5 + s[6] as uint64 * 256;
      var x: BoundedInts.uint64 := x6 + s[7] as uint64;
      UInt64SeqSerialize(x, s);
      x
    }

    lemma UInt64SeqSerialize(x: uint64, s: seq<uint8>)
      requires |s| == 8
      requires 72057594037927936 * s[0] as uint64 + 281474976710656 * s[1] as uint64 + 1099511627776 * s[2] as uint64 + 4294967296 * s[3] as uint64 + 16777216 * s[4] as uint64 + 65536 * s[5] as uint64 + 256 * s[6] as uint64 + s[7] as uint64 == x
      ensures UInt64ToSeq(x) == s
      decreases x, s
    {
    }

    lemma UInt64SeqSerializeDeserialize(x: uint64)
      ensures SeqToUInt64(UInt64ToSeq(x)) == x
      decreases x
    {
    }

    lemma UInt64SeqDeserializeSerialize(s: seq<uint8>)
      requires |s| == 8
      ensures UInt64ToSeq(SeqToUInt64(s)) == s
      decreases s
    {
    }

    function SeqToNat(s: seq<uint8>): nat
      decreases s
    {
      if s == [] then
        0
      else
        ghost var finalIndex: int := |s| - 1; SeqToNat(s[..finalIndex]) * 256 + s[finalIndex] as nat
    }

    lemma /*{:_induction s}*/ SeqToNatZeroPrefix(s: seq<uint8>)
      ensures SeqToNat(s) == SeqToNat([0] + s)
      decreases s
    {
    }

    lemma /*{:_induction s}*/ SeqWithUInt32Suffix(s: seq<uint8>, n: nat)
      requires n < UINT32_LIMIT
      requires 4 <= |s|
      requires ghost var suffixStartIndex: int := |s| - 4; s[suffixStartIndex..] == UInt32ToSeq(n as uint32) && forall i: int {:trigger s[i]} :: 0 <= i < suffixStartIndex ==> s[i] == 0
      ensures SeqToNat(s) == n
      decreases s, n
    {
    }
  }

  module String {

    export
      provides Int2String, Base10Int2String

    const Base10: seq<char> := ['0', '1', '2', '3', '4', '5', '6', '7', '8', '9']

    function method Int2Digits(n: int, base: int): (digits: seq<int>)
      requires base > 1
      requires n >= 0
      ensures forall d: int {:trigger d in digits} | d in digits :: 0 <= d && d < base
      decreases n
    {
      if n == 0 then
        []
      else
        assert n > 0; assert base > 1; assert n < base * n; assert n / base < n; Int2Digits(n / base, base) + [n % base]
    }

    function method Digits2String(digits: seq<int>, chars: seq<char>): string
      requires forall d: int {:trigger d in digits} | d in digits :: 0 <= d && d < |chars|
      decreases digits, chars
    {
      if digits == [] then
        """"
      else
        assert digits[0] in digits; assert forall d: int {:trigger d in digits} {:trigger d in digits[1..]} | d in digits[1..] :: d in digits; [chars[digits[0]]] + Digits2String(digits[1..], chars)
    }

    function method Int2String(n: int, chars: seq<char>): string
      requires |chars| > 1
      decreases n, chars
    {
      var base: int := |chars|;
      if n == 0 then
        ""0""
      else if n > 0 then
        Digits2String(Int2Digits(n, base), chars)
      else
        ""-"" + Digits2String(Int2Digits(-n, base), chars)
    }

    function method Base10Int2String(n: int): string
      decreases n
    {
      Int2String(n, Base10)
    }
  }
}

module {:options ""-functionSyntax:4""} BoundedInts {
  newtype uint8 = x: int
    | 0 <= x < TWO_TO_THE_8

  newtype uint16 = x: int
    | 0 <= x < TWO_TO_THE_16

  newtype uint32 = x: int
    | 0 <= x < TWO_TO_THE_32

  newtype uint64 = x: int
    | 0 <= x < TWO_TO_THE_64

  newtype int8 = x: int
    | -128 <= x < 128

  newtype int16 = x: int
    | -32768 <= x < 32768

  newtype int32 = x: int
    | -2147483648 <= x < 2147483648

  newtype int64 = x: int
    | -9223372036854775808 <= x < 9223372036854775808

  newtype nat8 = x: int
    | 0 <= x < 128

  newtype nat16 = x: int
    | 0 <= x < 32768

  newtype nat32 = x: int
    | 0 <= x < 2147483648

  newtype nat64 = x: int
    | 0 <= x < 9223372036854775808

  type byte = uint8

  type bytes = seq<byte>

  newtype opt_byte = c: int
    | -1 <= c < TWO_TO_THE_8

  const TWO_TO_THE_0: int := 1
  const TWO_TO_THE_1: int := 2
  const TWO_TO_THE_2: int := 4
  const TWO_TO_THE_4: int := 16
  const TWO_TO_THE_5: int := 32
  const TWO_TO_THE_8: int := 256
  const TWO_TO_THE_16: int := 65536
  const TWO_TO_THE_24: int := 16777216
  const TWO_TO_THE_32: int := 4294967296
  const TWO_TO_THE_40: int := 1099511627776
  const TWO_TO_THE_48: int := 281474976710656
  const TWO_TO_THE_56: int := 72057594037927936
  const TWO_TO_THE_64: int := 18446744073709551616
  const TWO_TO_THE_128: int := 340282366920938463463374607431768211456
  const TWO_TO_THE_256: int := 115792089237316195423570985008687907853269984665640564039457584007913129639936
  const TWO_TO_THE_512: int := 13407807929942597099574024998205846127479365820592393377723561443721764030073546976801874298166903427690031858186486050853753882811946569946433649006084096
  const UINT8_MAX: uint8 := 255
  const UINT16_MAX: uint16 := 65535
  const UINT32_MAX: uint32 := 4294967295
  const UINT64_MAX: uint64 := 18446744073709551615
  const INT8_MIN: int8 := -128
  const INT8_MAX: int8 := 127
  const INT16_MIN: int16 := -32768
  const INT16_MAX: int16 := 32767
  const INT32_MIN: int32 := -2147483648
  const INT32_MAX: int32 := 2147483647
  const INT64_MIN: int64 := -9223372036854775808
  const INT64_MAX: int64 := 9223372036854775807
  const NAT8_MAX: nat8 := 127
  const NAT16_MAX: nat16 := 32767
  const NAT32_MAX: nat32 := 2147483647
  const NAT64_MAX: nat64 := 9223372036854775807
}

module Base64Lemmas {

  import opened StandardLibrary

  import opened Wrappers

  import opened UInt = StandardLibrary.UInt

  import opened Base64
  lemma DecodeValidEncodeEmpty(s: seq<char>)
    requires s == []
    ensures Encode(DecodeValid(s)) == s
    decreases s
  {
  }

  lemma DecodeValidEncodeUnpadded(s: seq<char>)
    requires IsBase64String(s)
    requires |s| >= 4
    requires !Is1Padding(s[|s| - 4..])
    requires !Is2Padding(s[|s| - 4..])
    ensures Encode(DecodeValid(s)) == s
    decreases s
  {
  }

  lemma DecodeValidUnpaddedPartialFrom1PaddedSeq(s: seq<char>)
    requires IsBase64String(s)
    requires |s| >= 4
    requires Is1Padding(s[|s| - 4..])
    ensures DecodeValid(s)[..|DecodeValid(s)| - 2] == DecodeUnpadded(s[..|s| - 4])
    decreases s
  {
  }

  lemma DecodeValid1PaddedPartialFrom1PaddedSeq(s: seq<char>)
    requires IsBase64String(s)
    requires |s| >= 4
    requires Is1Padding(s[|s| - 4..])
    ensures DecodeValid(s)[|DecodeValid(s)| - 2..] == Decode1Padding(s[|s| - 4..])
    decreases s
  {
  }

  lemma {:vcs_split_on_every_assert} DecodeValidEncode1Padding(s: seq<char>)
    requires IsBase64String(s)
    requires |s| >= 4
    requires Is1Padding(s[|s| - 4..])
    ensures Encode(DecodeValid(s)) == s
    decreases s
  {
  }

  lemma DecodeValidUnpaddedPartialFrom2PaddedSeq(s: seq<char>)
    requires IsBase64String(s)
    requires |s| >= 4
    requires Is2Padding(s[|s| - 4..])
    ensures DecodeValid(s)[..|DecodeValid(s)| - 1] == DecodeUnpadded(s[..|s| - 4])
    decreases s
  {
  }

  lemma DecodeValid2PaddedPartialFrom2PaddedSeq(s: seq<char>)
    requires IsBase64String(s)
    requires |s| >= 4
    requires Is2Padding(s[|s| - 4..])
    ensures DecodeValid(s)[|DecodeValid(s)| - 1..] == Decode2Padding(s[|s| - 4..])
    decreases s
  {
  }

  lemma {:vcs_split_on_every_assert} DecodeValidEncode2Padding(s: seq<char>)
    requires IsBase64String(s)
    requires |s| >= 4
    requires Is2Padding(s[|s| - 4..])
    ensures Encode(DecodeValid(s)) == s
    decreases s
  {
  }

  lemma DecodeValidEncode(s: seq<char>)
    requires IsBase64String(s)
    ensures Encode(DecodeValid(s)) == s
    decreases s
  {
  }

  lemma {:vcs_split_on_every_assert} EncodeDecodeValid(b: seq<uint8>)
    ensures DecodeValid(Encode(b)) == b
    decreases b
  {
  }

  lemma EncodeDecodeValid0(b: seq<uint8>)
    requires |b| % 3 == 0
    ensures DecodeValid(Encode(b)) == b
    decreases b
  {
  }

  lemma EncodeDecodeValid1(b: seq<uint8>)
    requires |b| % 3 == 1
    ensures DecodeValid(Encode(b)) == b
    decreases b
  {
  }

  lemma EncodeDecodeValid2(b: seq<uint8>)
    requires |b| % 3 == 2
    ensures DecodeValid(Encode(b)) == b
    decreases b
  {
  }

  lemma DecodeEncode(s: seq<char>)
    requires IsBase64String(s)
    ensures Encode(Decode(s).value) == s
    decreases s
  {
  }

  lemma EncodeDecode(b: seq<uint8>)
    ensures Decode(Encode(b)) == Success(b)
    decreases b
  {
  }
}

module {:extern ""ConcurrentCall""} ConcurrentCall {

  import opened StandardLibrary

  import opened Wrappers

  import opened UInt = StandardLibrary.UInt
  trait {:termination false} Callee {
    ghost var Modifies: set<object>

    predicate ValidState()
      reads this
      decreases {this}

    method call(nameonly serialPos: uint32, nameonly concurrentPos: uint32)
      requires ValidState()
      modifies Modifies
      ensures ValidState()
      decreases serialPos, concurrentPos
  }

  method {:extern ""ConcurrentCall""} ConcurrentCall(nameonly callee: Callee, nameonly serialIters: uint32, nameonly concurrentIters: uint32)
    decreases callee, serialIters, concurrentIters
}

module FloatCompare {

  import opened Wrappers

  import opened StandardLibrary
  newtype CompareType = x: int
    | -1 <= x <= 1

  const Less: CompareType := -1
  const Equal: CompareType := 0
  const Greater: CompareType := 1

  function method {:tailrecursion} StrToIntInner(s: string, acc: int := 0): int
    decreases s, acc
  {
    if |s| == 0 then
      acc
    else if '0' <= s[0] <= '9' then
      StrToIntInner(s[1..], acc * 10 + s[0] as int - '0' as int)
    else
      StrToIntInner(s[1..], acc)
  }

  function method {:tailrecursion} SkipLeadingSpace(val: string): (ret: string)
    ensures |ret| == 0 || ret[0] > ' '
    decreases val
  {
    if |val| > 0 && val[0] <= ' ' then
      SkipLeadingSpace(val[1..])
    else
      val
  }

  function method {:tailrecursion} StrToInt(s: string, acc: int := 0): int
    decreases s, acc
  {
    var tmp: string := SkipLeadingSpace(s);
    if |tmp| == 0 then
      0
    else if tmp[0] == '-' then
      -StrToIntInner(s)
    else
      StrToIntInner(s)
  }

  function method SplitE(x: string): Option<(string, string)>
    decreases x
  {
    var parts: Option<(seq<char>, seq<char>)> := SplitOnce?(x, 'e');
    if parts.Some? then
      parts
    else
      SplitOnce?(x, 'E')
  }

  function method SplitExp(x: string): (string, int)
    decreases x
  {
    var parts: Option<(string, string)> := SplitE(x);
    if parts.Some? then
      (parts.value.0, StrToInt(parts.value.1))
    else
      (x, 0)
  }

  function method {:tailrecursion} SkipLeadingZeros(val: string): (ret: string)
    ensures |ret| == 0 || ret[0] != '0'
    decreases val
  {
    if |val| > 0 && val[0] == '0' then
      SkipLeadingZeros(val[1..])
    else
      val
  }

  function method {:tailrecursion} SkipTrailingZeros(val: string): (ret: string)
    ensures |ret| == 0 || ret[|ret| - 1] != '0'
    decreases val
  {
    if |val| > 0 && val[|val| - 1] == '0' then
      SkipTrailingZeros(val[..|val| - 1])
    else
      val
  }

  function method SplitDot(x: string): (string, string)
    decreases x
  {
    var parts: Option<(seq<char>, seq<char>)> := SplitOnce?(x, '.');
    if parts.Some? then
      (SkipLeadingZeros(parts.value.0), SkipTrailingZeros(parts.value.1))
    else
      (SkipLeadingZeros(x), """")
  }

  function method StrCmp(x: string, y: string): (ret: CompareType)
    decreases x, y
  {
    if |x| == 0 && |y| == 0 then
      0
    else if |x| == 0 then
      -1
    else if |y| == 0 then
      1
    else if x[0] < y[0] then
      -1
    else if x[0] > y[0] then
      1
    else
      StrCmp(x[1..], y[1..])
  }

  lemma /*{:_induction x, y}*/ StrCmpSymmetric(x: string, y: string)
    ensures StrCmp(x, y) == -StrCmp(y, x)
    decreases x, y
  {
  }

  function method AppendZeros(x: string, newLength: nat): (ret: string)
    requires |x| < newLength
    ensures |ret| == newLength
    decreases x, newLength
  {
    x + seq(newLength - |x|, (i: int) => '0')
  }

  function method CompareFloatInner(x: string, y: string): (ret: CompareType)
    decreases x, y
  {
    var xParts: (string, int) := SplitExp(x);
    var yParts: (string, int) := SplitExp(y);
    var xNum: (string, string) := SplitDot(xParts.0);
    var yNum: (string, string) := SplitDot(yParts.0);
    var xDigits: string := SkipLeadingZeros(xNum.0 + xNum.1);
    var yDigits: string := SkipLeadingZeros(yNum.0 + yNum.1);
    var xExp: int := xParts.1 - |xNum.1|;
    var yExp: int := yParts.1 - |yNum.1|;
    var logX: int := xExp + |xDigits|;
    var logY: int := yExp + |yDigits|;
    if logX > logY then
      1
    else if logY > logX then
      -1
    else if |xDigits| < |yDigits| then
      StrCmp(AppendZeros(xDigits, |yDigits|), yDigits)
    else if |yDigits| < |xDigits| then
      StrCmp(xDigits, AppendZeros(yDigits, |xDigits|))
    else
      StrCmp(xDigits, yDigits)
  }

  predicate method IsNegative(x: string)
    decreases x
  {
    |x| > 0 &&
    x[0] == '-'
  }

  function method SkipLeadingPlus(x: string): string
    decreases x
  {
    if 0 < |x| && x[0] == '+' then
      x[1..]
    else
      x
  }

  predicate method IsZero(x: string)
    decreases x
  {
    if |x| == 0 then
      true
    else if x[0] == '0' || x[0] == '.' then
      IsZero(x[1..])
    else if '1' <= x[0] <= '9' then
      false
    else
      true
  }

  function method RecognizeZero(x: string): string
    decreases x
  {
    if IsNegative(x) then
      if IsZero(x[1..]) then
        ""0""
      else
        x
    else if IsZero(x) then
      ""0""
    else
      x
  }

  function method CleanNumber(x: string): string
    decreases x
  {
    RecognizeZero(SkipLeadingPlus(SkipLeadingSpace(x)))
  }

  function method CompareFloat(x: string, y: string): (ret: CompareType)
    decreases x, y
  {
    var x: string := CleanNumber(x);
    var y: string := CleanNumber(y);
    if IsNegative(x) && IsNegative(y) then
      CompareFloatInner(y[1..], x[1..])
    else if IsNegative(x) then
      -1
    else if IsNegative(y) then
      1
    else
      CompareFloatInner(x, y)
  }
}

module HexStrings {

  import opened Wrappers

  import opened StandardLibrary

  import opened UInt = StandardLibrary.UInt
  type HexString = x: string
    | IsHexString(x)

  type LooseHexString = x: string
    | IsLooseHexString(x)

  function method HexChar(x: uint8): (res: char)
    requires x < 16
    ensures '0' <= res <= '9' || 'a' <= res <= 'f'
    ensures IsHexChar(res)
    decreases x
  {
    if x < 10 then
      '0' + x as char
    else
      'a' + (x - 10) as char
  }

  predicate method IsLooseHexChar(ch: char)
    decreases ch
  {
    '0' <= ch <= '9' || 'a' <= ch <= 'f' || 'A' <= ch <= 'F'
  }

  predicate method IsHexChar(ch: char)
    decreases ch
  {
    '0' <= ch <= '9' || 'a' <= ch <= 'f'
  }

  lemma PlainIsLooseChar(ch: char)
    requires IsHexChar(ch)
    ensures IsLooseHexChar(ch)
    decreases ch
  {
  }

  lemma PlainIsLooseString(s: string)
    requires IsHexString(s)
    ensures IsLooseHexString(s)
    decreases s
  {
  }

  predicate method IsHexString(s: string)
    decreases s
  {
    forall ch: char {:trigger IsHexChar(ch)} {:trigger ch in s} | ch in s :: 
      IsHexChar(ch)
  }

  predicate method IsLooseHexString(s: string)
    decreases s
  {
    forall ch: char {:trigger IsLooseHexChar(ch)} {:trigger ch in s} | ch in s :: 
      IsLooseHexChar(ch)
  }

  function method HexVal(ch: char): (res: uint8)
    requires IsLooseHexChar(ch)
    ensures 0 <= res < 16
    decreases ch
  {
    if '0' <= ch <= '9' then
      ch as uint8 - '0' as uint8
    else if 'a' <= ch <= 'f' then
      ch as uint8 - 'a' as uint8 + 10
    else
      assert 'A' <= ch <= 'F'; ch as uint8 - 'A' as uint8 + 10
  }

  lemma HexCharRoundTrip(ch: char)
    requires IsHexChar(ch)
    ensures HexChar(HexVal(ch)) == ch
    decreases ch
  {
  }

  lemma HexValRoundTrip(x: uint8)
    requires x < 16
    ensures HexVal(HexChar(x)) == x
    decreases x
  {
  }

  function method HexStr(x: uint8): (ret: string)
    ensures |ret| == 2
    decreases x
  {
    if x < 16 then
      var res: seq<char> := ['0', HexChar(x)];
      res
    else
      var res: seq<char> := [HexChar((x / 16) as uint8), HexChar((x % 16) as uint8)]; res
  }

  function method HexValue(x: string): (ret: uint8)
    requires |x| == 2
    requires IsLooseHexChar(x[0]) && IsLooseHexChar(x[1])
    decreases x
  {
    HexVal(x[0]) * 16 + HexVal(x[1])
  }

  lemma HexValueRoundTrip(x: uint8)
    ensures HexValue(HexStr(x)) == x
    decreases x
  {
  }

  lemma HexStrRoundTrip(x: string)
    requires |x| == 2
    requires IsHexChar(x[0]) && IsHexChar(x[1])
    ensures HexStr(HexValue(x)) == x
    decreases x
  {
  }

  function method {:tailrecursion} ToHexString(val: seq<uint8>): (ret: HexString)
    ensures |ret| == 2 * |val|
    decreases val
  {
    if |val| == 0 then
      []
    else
      HexStr(val[0]) + ToHexString(val[1..])
  }

  function method FromHexString(data: LooseHexString): (ret: seq<uint8>)
    ensures |ret| == (|data| + 1) / 2
    decreases data
  {
    if |data| == 0 then
      []
    else if |data| % 2 == 1 then
      [HexVal(data[0])] + FromHexString(data[1..])
    else
      [HexValue(data[..2])] + FromHexString(data[2..])
  }

  lemma /*{:_induction s}*/ ToHexStringRoundTrip(s: string)
    requires IsHexString(s)
    requires |s| % 2 == 0
    ensures ToHexString(FromHexString(s)) == s
    decreases s
  {
  }

  lemma /*{:_induction x}*/ FromHexStringRoundTrip(x: seq<uint8>)
    ensures FromHexString(ToHexString(x)) == x
    decreases x
  {
  }

  lemma EmptyHexStrings()
    ensures ToHexString([]) == """"
    ensures FromHexString("""") == []
  {
  }
}

module {:extern ""SortedSets""} SortedSets {

  import opened StandardLibrary

  import Seq
  method {:extern ""SetToOrderedSequence""} ComputeSetToOrderedSequence<T(==)>(s: set<seq<T>>, less: (T, T) -> bool) returns (res: seq<seq<T>>)
    requires Trichotomous(less) && Transitive(less)
    ensures res == SetToOrderedSequence(s, less)
    decreases s

  function method {:extern ""SetToOrderedSequence2""} ComputeSetToOrderedSequence2<T(==)>(s: set<seq<T>>, less: (T, T) -> bool): (res: seq<seq<T>>)
    requires Trichotomous(less) && Transitive(less)
    ensures res == SetToOrderedSequence(s, less)
    ensures Seq.HasNoDuplicates(res)
    ensures forall k: seq<T> {:trigger k in s} {:trigger k in res} | k in res :: k in s
    ensures forall k: seq<T> {:trigger k in res} {:trigger k in s} | k in s :: k in res
    ensures |res| == |s|
    decreases s

  function method {:extern ""SetToSequence""} ComputeSetToSequence<T(==)>(s: set<T>): (res: seq<T>)
    ensures Seq.HasNoDuplicates(res)
    ensures forall k: T {:trigger k in s} {:trigger k in res} | k in res :: k in s
    ensures forall k: T {:trigger k in res} {:trigger k in s} | k in s :: k in res
    ensures |res| == |s|
    decreases s
}

module Sorting {

  export
    reveals Reflexive, AntiSymmetric, Connected, TotalOrdering, LexicographicByteSeqBelow, LexicographicByteSeqBelowAux
    provides AboutLexicographicByteSeqBelow, SelectionSort, StandardLibrary, UInt


  import StandardLibrary

  import opened UInt = StandardLibrary.UInt
  predicate Reflexive<T(!new)>(R: (T, T) -> bool)
  {
    forall x: T {:trigger R(x, x)} :: 
      R(x, x)
  }

  predicate AntiSymmetric<T(!new)>(R: (T, T) -> bool)
  {
    forall x: T, y: T {:trigger R(y, x)} {:trigger R(x, y)} :: 
      R(x, y) &&
      R(y, x) ==>
        x == y
  }

  predicate Connected<T(!new)>(R: (T, T) -> bool)
  {
    forall x: T, y: T {:trigger R(y, x)} {:trigger R(x, y)} :: 
      R(x, y) || R(y, x)
  }

  predicate TotalOrdering<T(!new)>(R: (T, T) -> bool)
  {
    Reflexive(R) &&
    AntiSymmetric(R) &&
    StandardLibrary.Transitive(R) &&
    Connected(R)
  }

  predicate method LexicographicByteSeqBelow(x: seq<uint8>, y: seq<uint8>)
    decreases x, y
  {
    LexicographicByteSeqBelowAux(x, y, 0)
  }

  predicate method LexicographicByteSeqBelowAux(x: seq<uint8>, y: seq<uint8>, n: nat)
    requires n <= |x| && n <= |y|
    decreases |x| - n
  {
    n == |x| || (n != |y| && x[n] < y[n]) || (n != |y| && x[n] == y[n] && LexicographicByteSeqBelowAux(x, y, n + 1))
  }

  lemma AboutLexicographicByteSeqBelow()
    ensures TotalOrdering(LexicographicByteSeqBelow)
  {
  }

  lemma /*{:_induction x, n}*/ AboutLexicographicByteSeqBelowAux_Reflexive(x: seq<uint8>, n: nat)
    requires n <= |x|
    ensures LexicographicByteSeqBelowAux(x, x, n)
    decreases |x| - n
  {
  }

  lemma /*{:_induction x, y, n}*/ AboutLexicographicByteSeqBelowAux_AntiSymmetric(x: seq<uint8>, y: seq<uint8>, n: nat)
    requires n <= |x| && n <= |y|
    requires x[..n] == y[..n]
    requires LexicographicByteSeqBelowAux(x, y, n) && LexicographicByteSeqBelowAux(y, x, n)
    ensures x == y
    decreases |x| - n
  {
  }

  lemma /*{:_induction x, y, z, n}*/ AboutLexicographicByteSeqBelowAux_Transitive(x: seq<uint8>, y: seq<uint8>, z: seq<uint8>, n: nat)
    requires n <= |x| && n <= |y| && n <= |z|
    requires LexicographicByteSeqBelowAux(x, y, n) && LexicographicByteSeqBelowAux(y, z, n)
    ensures LexicographicByteSeqBelowAux(x, z, n)
    decreases |x| - n
  {
  }

  lemma /*{:_induction x, y, n}*/ AboutLexicographicByteSeqBelowAux_Connected(x: seq<uint8>, y: seq<uint8>, n: nat)
    requires n <= |x| && n <= |y|
    ensures LexicographicByteSeqBelowAux(x, y, n) || LexicographicByteSeqBelowAux(y, x, n)
    decreases |x| - n
  {
  }

  method {:vcs_split_on_every_assert} SelectionSort<Data>(a: array<Data>, below: (Data, Data) -> bool)
    requires StandardLibrary.Transitive(below)
    requires Connected(below)
    modifies a
    ensures multiset(a[..]) == old(multiset(a[..]))
    ensures forall i: int, j: int {:trigger a[j], a[i]} :: 0 <= i < j < a.Length ==> below(a[i], a[j])
    decreases a
  {
    var m := 0;
    while m < a.Length
      invariant 0 <= m <= a.Length
      invariant multiset(a[..]) == old(multiset(a[..]))
      invariant forall i: int, j: int {:trigger a[j], a[i]} :: 0 <= i < j < m ==> below(a[i], a[j])
      invariant forall i: int, j: int {:trigger a[j], a[i]} :: 0 <= i < m <= j < a.Length ==> below(a[i], a[j])
      decreases a.Length - m
    {
      var mindex, n := m, m + 1;
      while n < a.Length
        invariant m <= mindex < n <= a.Length
        invariant forall i: int {:trigger a[i]} :: m <= i < n ==> below(a[mindex], a[i])
        decreases a.Length - n
      {
        if !below(a[mindex], a[n]) {
          mindex := n;
        }
        n := n + 1;
      }
      a[m], a[mindex] := a[mindex], a[m];
      m := m + 1;
    }
  }
}

module Streams {

  import opened Wrappers

  import opened UInt = StandardLibrary.UInt
  class SeqReader<T> {
    ghost var Repr: set<object>
    const data: seq<T>
    var pos: nat

    predicate Valid()
      reads this, Repr
      ensures Valid() ==> this in Repr
      decreases Repr + {this}
    {
      this in Repr &&
      pos <= |data|
    }

    constructor (s: seq<T>)
      ensures pos == 0
      ensures data[..] == s
      ensures Valid() && fresh(Repr)
      decreases s
    {
      data := s;
      pos := 0;
      Repr := {this};
    }

    method ReadElements(n: nat) returns (elems: seq<T>)
      requires Valid()
      requires n + pos <= |data|
      modifies `pos
      ensures n == 0 ==> elems == []
      ensures n > 0 ==> elems == data[old(pos)..][..n]
      ensures pos == old(pos) + n
      ensures Valid()
      decreases n
    {
      elems := data[pos..][..n];
      pos := pos + n;
      return elems;
    }

    method ReadExact(n: nat) returns (res: Result<seq<T>, string>)
      requires Valid()
      modifies `pos
      ensures n + old(pos) <= |data| <==> res.Success?
      ensures res.Success? ==> |res.value| == n
      ensures res.Success? ==> pos == old(pos) + n
      ensures res.Success? ==> res.value == data[old(pos) .. old(pos) + n]
      ensures res.Failure? ==> n > |data| - pos
      ensures res.Failure? ==> pos == old(pos)
      ensures Valid()
      decreases n
    {
      if n > |data| - pos {
        return Failure(""IO Error: Not enough elements left on stream."");
      } else {
        var elements := ReadElements(n);
        return Success(elements);
      }
    }
  }

  class ByteReader {
    ghost var Repr: set<object>
    const reader: SeqReader<uint8>

    predicate Valid()
      reads this, Repr
      ensures Valid() ==> this in Repr
      decreases Repr + {this}
    {
      this in Repr &&
      reader in Repr &&
      reader.Repr <= Repr &&
      this !in reader.Repr &&
      reader.Valid()
    }

    constructor (s: seq<uint8>)
      ensures reader.data == s
      ensures reader.pos == 0
      ensures Valid() && fresh(Repr)
      decreases s
    {
      var mr := new SeqReader<uint8>(s);
      reader := mr;
      Repr := {this} + mr.Repr;
    }

    method ReadByte() returns (res: Result<uint8, string>)
      requires Valid()
      modifies reader`pos
      ensures res.Failure? ==> |reader.data| - reader.pos < 1
      ensures res.Failure? ==> unchanged(reader)
      ensures res.Success? ==> reader.pos == old(reader.pos) + 1
      ensures old(reader.pos) + 1 <= |reader.data| <==> res.Success?
      ensures res.Success? ==> res.value == reader.data[old(reader.pos)]
      ensures Valid()
    {
      var bytes :- reader.ReadExact(1);
      assert |bytes| == 1;
      return Success(bytes[0]);
    }

    method ReadBytes(n: nat) returns (res: Result<seq<uint8>, string>)
      requires Valid()
      modifies reader`pos
      ensures res.Failure? ==> |reader.data| - reader.pos < n
      ensures res.Failure? ==> unchanged(reader)
      ensures res.Success? ==> |res.value| == n
      ensures res.Success? && |res.value| == 0 ==> unchanged(reader)
      ensures res.Success? ==> reader.pos == old(reader.pos) + n
      ensures old(reader.pos) + n <= |reader.data| <==> res.Success?
      ensures res.Success? ==> res.value == reader.data[old(reader.pos) .. old(reader.pos) + n]
      ensures Valid()
      decreases n
    {
      var bytes :- reader.ReadExact(n);
      assert |bytes| == n;
      return Success(bytes);
    }

    method ReadUInt16() returns (res: Result<uint16, string>)
      requires Valid()
      modifies reader`pos
      ensures res.Failure? ==> |reader.data| - reader.pos < 2
      ensures res.Failure? ==> unchanged(reader)
      ensures res.Success? ==> reader.pos == old(reader.pos) + 2
      ensures old(reader.pos) + 2 <= |reader.data| <==> res.Success?
      ensures res.Success? ==> res.value == SeqToUInt16(reader.data[old(reader.pos) .. old(reader.pos) + 2])
      ensures Valid()
    {
      var bytes :- reader.ReadExact(2);
      assert |bytes| == 2;
      var n := SeqToUInt16(bytes);
      return Success(n);
    }

    method ReadUInt32() returns (res: Result<uint32, string>)
      requires Valid()
      modifies reader`pos
      ensures Valid()
      ensures res.Failure? ==> unchanged(reader)
      ensures res.Success? ==> reader.pos == old(reader.pos) + 4 && UInt32ToSeq(res.value) == reader.data[old(reader.pos) .. reader.pos]
    {
      var bytes :- reader.ReadExact(4);
      assert |bytes| == 4;
      var n := SeqToUInt32(bytes);
      UInt32SeqDeserializeSerialize(bytes);
      return Success(n);
    }

    method ReadUInt64() returns (res: Result<uint64, string>)
      requires Valid()
      modifies reader`pos
      ensures res.Failure? ==> |reader.data| - reader.pos < 8
      ensures res.Failure? ==> unchanged(reader)
      ensures res.Success? ==> reader.pos == old(reader.pos) + 8
      ensures old(reader.pos) + 8 <= |reader.data| <==> res.Success?
      ensures res.Success? ==> res.value == SeqToUInt64(reader.data[old(reader.pos) .. old(reader.pos) + 8])
      ensures Valid()
    {
      var bytes :- reader.ReadExact(8);
      assert |bytes| == 8;
      var n := SeqToUInt64(bytes);
      return Success(n);
    }

    method IsDoneReading() returns (b: bool)
      requires Valid()
      ensures (b && |reader.data| - reader.pos == 0) || (!b && |reader.data| - reader.pos > 0)
      ensures Valid()
    {
      return |reader.data| == reader.pos;
    }

    method GetSizeRead() returns (n: nat)
      requires Valid()
      ensures n == reader.pos
      ensures Valid()
    {
      return reader.pos;
    }
  }

  class SeqWriter<T> {
    ghost var Repr: set<object>
    var data: seq<T>

    predicate Valid()
      reads this, Repr
      ensures Valid() ==> this in Repr
      decreases Repr + {this}
    {
      this in Repr
    }

    constructor ()
      ensures data == []
      ensures Valid() && fresh(Repr)
    {
      data := [];
      Repr := {this};
    }

    method WriteElements(elems: seq<T>) returns (n: nat)
      requires Valid()
      modifies `data
      ensures n == |data| - |old(data)| == |elems|
      ensures |elems| == 0 ==> data == old(data)
      ensures |elems| > 0 ==> data == old(data) + elems
      ensures elems == data[|data| - |elems|..]
      ensures Valid()
      decreases elems
    {
      data := data + elems;
      return |elems|;
    }
  }

  class ByteWriter {
    ghost var Repr: set<object>
    const writer: SeqWriter<uint8>

    predicate Valid()
      reads this, Repr
      ensures Valid() ==> this in Repr
      decreases Repr + {this}
    {
      this in Repr &&
      writer in Repr &&
      writer.Repr <= Repr &&
      this !in writer.Repr &&
      writer.Valid()
    }

    constructor ()
      ensures writer.data == []
      ensures Valid() && fresh(Repr)
    {
      var mw := new SeqWriter<uint8>();
      writer := mw;
      Repr := {this} + mw.Repr;
    }

    method WriteByte(n: uint8) returns (r: nat)
      requires Valid()
      modifies writer`data
      ensures writer.data == old(writer.data) + [n]
      ensures r == 1
      ensures Valid()
      decreases n
    {
      r := writer.WriteElements([n]);
    }

    method WriteBytes(s: seq<uint8>) returns (r: nat)
      requires Valid()
      modifies writer`data
      ensures writer.data == old(writer.data) + s
      ensures r == |s|
      ensures Valid()
      decreases s
    {
      r := writer.WriteElements(s);
    }

    method WriteUInt16(n: uint16) returns (r: nat)
      requires Valid()
      modifies writer`data
      ensures writer.data == old(writer.data) + UInt16ToSeq(n)
      ensures r == 2
      ensures Valid()
      decreases n
    {
      r := writer.WriteElements(UInt16ToSeq(n));
    }

    method WriteUInt32(n: uint32) returns (r: nat)
      requires Valid()
      modifies writer`data
      ensures writer.data == old(writer.data) + UInt32ToSeq(n)
      ensures r == 4
      ensures Valid()
      decreases n
    {
      r := writer.WriteElements(UInt32ToSeq(n));
    }

    function method GetDataWritten(): (s: seq<uint8>)
      requires Valid()
      reads Repr
      ensures s == writer.data
      ensures Valid()
      decreases Repr
    {
      writer.data
    }

    function method GetSizeWritten(): (n: nat)
      requires Valid()
      reads Repr
      ensures n == |writer.data|
      ensures Valid()
      decreases Repr
    {
      |writer.data|
    }
  }
}

module {:extern ""Time""} Time {

  import opened StandardLibrary

  import opened Wrappers

  import opened UInt = StandardLibrary.UInt
  method {:extern ""CurrentRelativeTime""} GetCurrent() returns (res: int64)
    ensures res >= 0

  function method {:extern ""GetCurrentTimeStamp""} GetCurrentTimeStamp(): (res: Result<string, string>)
}

module {:extern ""UTF8""} UTF8 {

  import opened Wrappers

  import opened UInt = StandardLibrary.UInt
  type ValidUTF8Bytes = i: seq<uint8>
    | ValidUTF8Seq(i)
    witness []

  function method {:extern ""Encode""} Encode(s: string): (res: Result<ValidUTF8Bytes, string>)
    ensures IsASCIIString(s) ==> res.Success? && |res.value| == |s|
    ensures res.Success? ==> Decode(res.value).Success? && Decode(res.value).value == s
    decreases s

  function method {:extern ""Decode""} Decode(b: seq<uint8>): (res: Result<string, string>)
    ensures res.Success? ==> ValidUTF8Seq(b)
    decreases b

  predicate method IsASCIIString(s: string)
    decreases s
  {
    forall i: int {:trigger s[i]} :: 
      0 <= i < |s| ==>
        s[i] as int < 128
  }

  function method {:opaque} {:tailrecursion} {:fuel 0, 0} EncodeAscii(s: string): (ret: ValidUTF8Bytes)
    requires IsASCIIString(s)
    ensures |s| == |ret|
    ensures forall i: int {:trigger ret[i]} {:trigger s[i]} | 0 <= i < |s| :: s[i] as uint8 == ret[i]
    decreases s
  {
    if |s| == 0 then
      []
    else
      var x: seq<BoundedInts.uint8> := [s[0] as uint8]; assert ValidUTF8Seq(x); ValidUTF8Concat(x, EncodeAscii(s[1..])); x + EncodeAscii(s[1..])
  }

  lemma /*{:_induction x, y}*/ EncodeAsciiUnique2(x: string, y: string)
    requires IsASCIIString(x) && IsASCIIString(y)
    requires x != y
    ensures EncodeAscii(x) != EncodeAscii(y)
    decreases x, y
  {
  }

  lemma {:opaque} EncodeAsciiUnique()
    ensures forall x: string, y: string {:trigger EncodeAscii(y), EncodeAscii(x)} {:trigger EncodeAscii(y), IsASCIIString(x)} {:trigger EncodeAscii(x), IsASCIIString(y)} {:trigger IsASCIIString(y), IsASCIIString(x)} :: IsASCIIString(x) && IsASCIIString(y) && x != y ==> EncodeAscii(x) != EncodeAscii(y)
  {
  }

  predicate method Uses1Byte(s: seq<uint8>)
    requires |s| >= 1
    decreases s
  {
    0 <= s[0] <= 127
  }

  predicate method Uses2Bytes(s: seq<uint8>)
    requires |s| >= 2
    decreases s
  {
    194 <= s[0] <= 223 &&
    128 <= s[1] <= 191
  }

  predicate method Uses3Bytes(s: seq<uint8>)
    requires |s| >= 3
    decreases s
  {
    (s[0] == 224 && 160 <= s[1] <= 191 && 128 <= s[2] <= 191) || (225 <= s[0] <= 236 && 128 <= s[1] <= 191 && 128 <= s[2] <= 191) || (s[0] == 237 && 128 <= s[1] <= 159 && 128 <= s[2] <= 191) || (238 <= s[0] <= 239 && 128 <= s[1] <= 191 && 128 <= s[2] <= 191)
  }

  predicate method Uses4Bytes(s: seq<uint8>)
    requires |s| >= 4
    decreases s
  {
    (s[0] == 240 && 144 <= s[1] <= 191 && 128 <= s[2] <= 191 && 128 <= s[3] <= 191) || (241 <= s[0] <= 243 && 128 <= s[1] <= 191 && 128 <= s[2] <= 191 && 128 <= s[3] <= 191) || (s[0] == 244 && 128 <= s[1] <= 143 && 128 <= s[2] <= 191 && 128 <= s[3] <= 191)
  }

  predicate method {:tailrecursion} ValidUTF8Range(a: seq<uint8>, lo: nat, hi: nat)
    requires lo <= hi <= |a|
    decreases hi - lo
  {
    if lo == hi then
      true
    else
      var r: seq<BoundedInts.uint8> := a[lo .. hi]; if Uses1Byte(r) then ValidUTF8Range(a, lo + 1, hi) else if 2 <= |r| && Uses2Bytes(r) then ValidUTF8Range(a, lo + 2, hi) else if 3 <= |r| && Uses3Bytes(r) then ValidUTF8Range(a, lo + 3, hi) else if 4 <= |r| && Uses4Bytes(r) then ValidUTF8Range(a, lo + 4, hi) else false
  }

  lemma /*{:_induction a, b, c, lo, hi}*/ ValidUTF8Embed(a: seq<uint8>, b: seq<uint8>, c: seq<uint8>, lo: nat, hi: nat)
    requires lo <= hi <= |b|
    ensures ValidUTF8Range(b, lo, hi) == ValidUTF8Range(a + b + c, |a| + lo, |a| + hi)
    decreases hi - lo
  {
  }

  predicate method ValidUTF8Seq(s: seq<uint8>)
    decreases s
  {
    ValidUTF8Range(s, 0, |s|)
  }

  lemma ValidUTF8Concat(s: seq<uint8>, t: seq<uint8>)
    requires ValidUTF8Seq(s) && ValidUTF8Seq(t)
    ensures ValidUTF8Seq(s + t)
    decreases s, t
  {
  }
}

module {:extern ""UUID""} UUID {

  import opened Wrappers

  import opened UInt = StandardLibrary.UInt
  function method {:extern ""ToByteArray""} ToByteArray(s: string): (res: Result<seq<uint8>, string>)
    ensures res.Success? ==> |res.value| == 16
    ensures res.Success? ==> FromByteArray(res.value).Success? && FromByteArray(res.value).value == s
    decreases s

  function method {:extern ""FromByteArray""} FromByteArray(b: seq<uint8>): (res: Result<string, string>)
    requires |b| == 16
    decreases b

  method {:extern ""GenerateUUID""} GenerateUUID() returns (res: Result<string, string>)
    ensures res.Success? ==> 0 < |res.value|
}

module {:options ""-functionSyntax:4""} Mul {

  import MulINL = MulInternalsNonlinear

  import opened MulInternals
  lemma LemmaMulIsMulRecursive(x: int, y: int)
    ensures x * y == MulRecursive(x, y)
    decreases x, y
  {
  }

  lemma LemmaMulIsMulRecursiveAuto()
    ensures forall x: int, y: int {:trigger MulRecursive(x, y)} :: x * y == MulRecursive(x, y)
  {
  }

  lemma /*{:_induction x, y}*/ LemmaMulIsMulPos(x: int, y: int)
    requires x >= 0
    ensures x * y == MulPos(x, y)
    decreases x, y
  {
  }

  lemma LemmaMulBasics(x: int)
    ensures 0 * x == 0
    ensures x * 0 == 0
    ensures 1 * x == x
    ensures x * 1 == x
    decreases x
  {
  }

  lemma LemmaMulBasicsAuto()
    ensures forall x: int {:trigger 0 * x} :: 0 * x == 0
    ensures forall x: int {:trigger x * 0} :: x * 0 == 0
    ensures forall x: int {:trigger 1 * x} :: 1 * x == x
    ensures forall x: int {:trigger x * 1} :: x * 1 == x
  {
  }

  lemma LemmaMulNonzero(x: int, y: int)
    ensures x * y != 0 <==> x != 0 && y != 0
    decreases x, y
  {
  }

  lemma LemmaMulNonzeroAuto()
    ensures forall x: int, y: int {:trigger x * y} :: x * y != 0 <==> x != 0 && y != 0
  {
  }

  lemma LemmaMulByZeroIsZeroAuto()
    ensures forall x: int {:trigger 0 * x} {:trigger x * 0} :: x * 0 == 0 * x && 0 * x == 0
  {
  }

  lemma LemmaMulIsAssociative(x: int, y: int, z: int)
    ensures x * y * z == x * y * z
    decreases x, y, z
  {
  }

  lemma LemmaMulIsAssociativeAuto()
    ensures forall x: int, y: int, z: int {:trigger x * y * z} {:trigger x * y * z} :: x * y * z == x * y * z
  {
  }

  lemma LemmaMulIsCommutative(x: int, y: int)
    ensures x * y == y * x
    decreases x, y
  {
  }

  lemma LemmaMulIsCommutativeAuto()
    ensures forall x: int, y: int {:trigger x * y} :: x * y == y * x
  {
  }

  lemma LemmaMulOrdering(x: int, y: int)
    requires x != 0
    requires y != 0
    requires 0 <= x * y
    ensures x * y >= x && x * y >= y
    decreases x, y
  {
  }

  lemma LemmaMulOrderingAuto()
    ensures forall x: int, y: int {:trigger x * y} :: (0 != x && 0 != y && x * y >= 0 ==> x * y >= x) && (0 != x && 0 != y && x * y >= 0 ==> x * y >= y)
  {
  }

  lemma LemmaMulEquality(x: int, y: int, z: int)
    requires x == y
    ensures x * z == y * z
    decreases x, y, z
  {
  }

  lemma LemmaMulEqualityAuto()
    ensures forall x: int, y: int, z: int {:trigger x * z, y * z} :: x == y ==> x * z == y * z
  {
  }

  lemma LemmaMulInequality(x: int, y: int, z: int)
    requires x <= y
    requires z >= 0
    ensures x * z <= y * z
    decreases x, y, z
  {
  }

  lemma LemmaMulInequalityAuto()
    ensures forall x: int, y: int, z: int {:trigger x * z, y * z} :: x <= y && z >= 0 ==> x * z <= y * z
  {
  }

  lemma LemmaMulStrictInequality(x: int, y: int, z: int)
    requires x < y
    requires z > 0
    ensures x * z < y * z
    decreases x, y, z
  {
  }

  lemma LemmaMulStrictInequalityAuto()
    ensures forall x: int, y: int, z: int {:trigger x * z, y * z} :: x < y && z > 0 ==> x * z < y * z
  {
  }

  lemma LemmaMulUpperBound(x: int, XBound: int, y: int, YBound: int)
    requires x <= XBound
    requires y <= YBound
    requires 0 <= x
    requires 0 <= y
    ensures x * y <= XBound * YBound
    decreases x, XBound, y, YBound
  {
  }

  lemma LemmaMulUpperBoundAuto()
    ensures forall YBound: int, y: int, XBound: int, x: int {:trigger x * y, XBound * YBound} :: x <= XBound && y <= YBound && 0 <= x && 0 <= y ==> x * y <= XBound * YBound
  {
  }

  lemma LemmaMulStrictUpperBound(x: int, XBound: int, y: int, YBound: int)
    requires x < XBound
    requires y < YBound
    requires 0 < x
    requires 0 < y
    ensures x * y <= (XBound - 1) * (YBound - 1)
    decreases x, XBound, y, YBound
  {
  }

  lemma LemmaMulStrictUpperBoundAuto()
    ensures forall YBound: int, y: int, XBound: int, x: int {:trigger x * y, (XBound - 1) * (YBound - 1)} :: x < XBound && y < YBound && 0 < x && 0 < y ==> x * y <= (XBound - 1) * (YBound - 1)
  {
  }

  lemma LemmaMulLeftInequality(x: int, y: int, z: int)
    requires 0 < x
    ensures y <= z ==> x * y <= x * z
    ensures y < z ==> x * y < x * z
    decreases x, y, z
  {
  }

  lemma LemmaMulLeftInequalityAuto()
    ensures forall x: int, y: int, z: int {:trigger x * y, x * z} :: (x > 0 ==> y <= z ==> x * y <= x * z) && (x > 0 ==> y < z ==> x * y < x * z)
  {
  }

  lemma LemmaMulEqualityConverse(m: int, x: int, y: int)
    requires m != 0
    requires m * x == m * y
    ensures x == y
    decreases m, x, y
  {
  }

  lemma LemmaMulEqualityConverseAuto()
    ensures forall m: int, x: int, y: int {:trigger m * x, m * y} :: m != 0 && m * x == m * y ==> x == y
  {
  }

  lemma LemmaMulInequalityConverse(x: int, y: int, z: int)
    requires x * z <= y * z
    requires z > 0
    ensures x <= y
    decreases x, y, z
  {
  }

  lemma LemmaMulInequalityConverseAuto()
    ensures forall x: int, y: int, z: int {:trigger x * z, y * z} :: x * z <= y * z && z > 0 ==> x <= y
  {
  }

  lemma LemmaMulStrictInequalityConverse(x: int, y: int, z: int)
    requires x * z < y * z
    requires z >= 0
    ensures x < y
    decreases x, y, z
  {
  }

  lemma LemmaMulStrictInequalityConverseAuto()
    ensures forall x: int, y: int, z: int {:trigger x * z, y * z} :: x * z < y * z && z >= 0 ==> x < y
  {
  }

  lemma LemmaMulIsDistributiveAdd(x: int, y: int, z: int)
    ensures x * (y + z) == x * y + x * z
    decreases x, y, z
  {
  }

  lemma LemmaMulIsDistributiveAddAuto()
    ensures forall x: int, y: int, z: int {:trigger x * (y + z)} :: x * (y + z) == x * y + x * z
  {
  }

  lemma LemmaMulIsDistributiveAddOtherWay(x: int, y: int, z: int)
    ensures (y + z) * x == y * x + z * x
    decreases x, y, z
  {
  }

  lemma LemmaMulIsDistributiveAddOtherWayAuto()
    ensures forall x: int, y: int, z: int {:trigger (y + z) * x} :: (y + z) * x == y * x + z * x
  {
  }

  lemma LemmaMulIsDistributiveSub(x: int, y: int, z: int)
    ensures x * (y - z) == x * y - x * z
    decreases x, y, z
  {
  }

  lemma LemmaMulIsDistributiveSubAuto()
    ensures forall x: int, y: int, z: int {:trigger x * (y - z)} :: x * (y - z) == x * y - x * z
  {
  }

  lemma LemmaMulIsDistributive(x: int, y: int, z: int)
    ensures x * (y + z) == x * y + x * z
    ensures x * (y - z) == x * y - x * z
    ensures (y + z) * x == y * x + z * x
    ensures (y - z) * x == y * x - z * x
    ensures x * (y + z) == (y + z) * x
    ensures x * (y - z) == (y - z) * x
    ensures x * y == y * x
    ensures x * z == z * x
    decreases x, y, z
  {
  }

  lemma LemmaMulIsDistributiveAuto()
    ensures forall x: int, y: int, z: int {:trigger x * (y + z)} :: x * (y + z) == x * y + x * z
    ensures forall x: int, y: int, z: int {:trigger x * (y - z)} :: x * (y - z) == x * y - x * z
    ensures forall x: int, y: int, z: int {:trigger (y + z) * x} :: (y + z) * x == y * x + z * x
    ensures forall x: int, y: int, z: int {:trigger (y - z) * x} :: (y - z) * x == y * x - z * x
  {
  }

  lemma LemmaMulStrictlyPositive(x: int, y: int)
    ensures 0 < x && 0 < y ==> 0 < x * y
    decreases x, y
  {
  }

  lemma LemmaMulStrictlyPositiveAuto()
    ensures forall x: int, y: int {:trigger x * y} :: 0 < x && 0 < y ==> 0 < x * y
  {
  }

  lemma LemmaMulStrictlyIncreases(x: int, y: int)
    requires 1 < x
    requires 0 < y
    ensures y < x * y
    decreases x, y
  {
  }

  lemma LemmaMulStrictlyIncreasesAuto()
    ensures forall x: int, y: int {:trigger x * y} :: 1 < x && 0 < y ==> y < x * y
  {
  }

  lemma LemmaMulIncreases(x: int, y: int)
    requires 0 < x
    requires 0 < y
    ensures y <= x * y
    decreases x, y
  {
  }

  lemma LemmaMulIncreasesAuto()
    ensures forall x: int, y: int {:trigger x * y} :: 0 < x && 0 < y ==> y <= x * y
  {
  }

  lemma LemmaMulNonnegative(x: int, y: int)
    requires 0 <= x
    requires 0 <= y
    ensures 0 <= x * y
    decreases x, y
  {
  }

  lemma LemmaMulNonnegativeAuto()
    ensures forall x: int, y: int {:trigger x * y} :: 0 <= x && 0 <= y ==> 0 <= x * y
  {
  }

  lemma LemmaMulUnaryNegation(x: int, y: int)
    ensures -x * y == -(x * y) == x * -y
    decreases x, y
  {
  }

  lemma LemmaMulUnaryNegationAuto()
    ensures forall x: int, y: int {:trigger -x * y} {:trigger x * -y} :: -x * y == -(x * y) && -(x * y) == x * -y
  {
  }

  lemma LemmaMulCancelsNegatives(x: int, y: int)
    ensures x * y == -x * -y
    decreases x, y
  {
  }

  lemma LemmaMulCancelsNegativesAuto()
    ensures forall x: int, y: int {:trigger x * y} :: x * y == -x * -y
  {
  }

  lemma LemmaMulProperties()
    ensures forall x: int, y: int {:trigger x * y} :: x * y == y * x
    ensures forall x: int {:trigger x * 1} {:trigger 1 * x} :: x * 1 == 1 * x && 1 * x == x
    ensures forall x: int, y: int, z: int {:trigger x * z, y * z} :: x < y && z > 0 ==> x * z < y * z
    ensures forall x: int, y: int, z: int {:trigger x * z, y * z} :: x <= y && z >= 0 ==> x * z <= y * z
    ensures forall x: int, y: int, z: int {:trigger x * (y + z)} :: x * (y + z) == x * y + x * z
    ensures forall x: int, y: int, z: int {:trigger x * (y - z)} :: x * (y - z) == x * y - x * z
    ensures forall x: int, y: int, z: int {:trigger (y + z) * x} :: (y + z) * x == y * x + z * x
    ensures forall x: int, y: int, z: int {:trigger (y - z) * x} :: (y - z) * x == y * x - z * x
    ensures forall x: int, y: int, z: int {:trigger x * y * z} {:trigger x * y * z} :: x * y * z == x * y * z
    ensures forall x: int, y: int {:trigger x * y} :: x * y != 0 <==> x != 0 && y != 0
    ensures forall x: int, y: int {:trigger x * y} :: 0 <= x && 0 <= y ==> 0 <= x * y
    ensures forall x: int, y: int {:trigger x * y} :: (0 < x && 0 < y && 0 <= x * y ==> x <= x * y) && (0 < x && 0 < y && 0 <= x * y ==> y <= x * y)
    ensures forall x: int, y: int {:trigger x * y} :: 1 < x && 0 < y ==> y < x * y
    ensures forall x: int, y: int {:trigger x * y} :: 0 < x && 0 < y ==> y <= x * y
    ensures forall x: int, y: int {:trigger x * y} :: 0 < x && 0 < y ==> 0 < x * y
  {
  }
}

module {:options ""-functionSyntax:4""} MulInternalsNonlinear {
  lemma LemmaMulStrictlyPositive(x: int, y: int)
    ensures 0 < x && 0 < y ==> 0 < x * y
    decreases x, y
  {
  }

  lemma LemmaMulNonzero(x: int, y: int)
    ensures x * y != 0 <==> x != 0 && y != 0
    decreases x, y
  {
  }

  lemma LemmaMulIsAssociative(x: int, y: int, z: int)
    ensures x * y * z == x * y * z
    decreases x, y, z
  {
  }

  lemma LemmaMulIsDistributiveAdd(x: int, y: int, z: int)
    ensures x * (y + z) == x * y + x * z
    decreases x, y, z
  {
  }

  lemma LemmaMulOrdering(x: int, y: int)
    requires x != 0
    requires y != 0
    requires 0 <= x * y
    ensures x * y >= x && x * y >= y
    decreases x, y
  {
  }

  lemma LemmaMulStrictInequality(x: int, y: int, z: int)
    requires x < y
    requires z > 0
    ensures x * z < y * z
    decreases x, y, z
  {
  }
}

module {:options ""-functionSyntax:4""} MulInternals {

  import opened GeneralInternals

  import opened MulInternalsNonlinear
  function method {:opaque} {:fuel 0, 0} MulPos(x: int, y: int): int
    requires x >= 0
    decreases x, y
  {
    if x == 0 then
      0
    else
      y + MulPos(x - 1, y)
  }

  function method MulRecursive(x: int, y: int): int
    decreases x, y
  {
    if x >= 0 then
      MulPos(x, y)
    else
      -1 * MulPos(-1 * x, y)
  }

  lemma LemmaMulInduction(f: int -> bool)
    requires f(0)
    requires forall i: int {:trigger f(i), f(i + 1)} :: i >= 0 && f(i) ==> f(i + 1)
    requires forall i: int {:trigger f(i), f(i - 1)} :: i <= 0 && f(i) ==> f(i - 1)
    ensures forall i: int {:trigger f(i)} :: f(i)
  {
  }

  lemma LemmaMulCommutes()
    ensures forall x: int, y: int {:trigger x * y} :: x * y == y * x
  {
  }

  lemma LemmaMulSuccessor()
    ensures forall x: int, y: int {:trigger (x + 1) * y} :: (x + 1) * y == x * y + y
    ensures forall x: int, y: int {:trigger (x - 1) * y} :: (x - 1) * y == x * y - y
  {
  }

  lemma LemmaMulDistributes()
    ensures forall x: int, y: int, z: int {:trigger (x + y) * z} :: (x + y) * z == x * z + y * z
    ensures forall x: int, y: int, z: int {:trigger (x - y) * z} :: (x - y) * z == x * z - y * z
  {
  }

  predicate MulAuto()
  {
    (forall x: int, y: int {:trigger x * y} :: 
      x * y == y * x) &&
    (forall x: int, y: int, z: int {:trigger (x + y) * z} :: 
      (x + y) * z == x * z + y * z) &&
    forall x: int, y: int, z: int {:trigger (x - y) * z} :: 
      (x - y) * z == x * z - y * z
  }

  lemma LemmaMulAuto()
    ensures MulAuto()
  {
  }

  lemma LemmaMulInductionAuto(x: int, f: int -> bool)
    requires MulAuto() ==> f(0) && (forall i: int {:trigger IsLe(0, i)} :: IsLe(0, i) && f(i) ==> f(i + 1)) && forall i: int {:trigger IsLe(i, 0)} :: IsLe(i, 0) && f(i) ==> f(i - 1)
    ensures MulAuto()
    ensures f(x)
    decreases x
  {
  }

  lemma LemmaMulInductionAutoForall(f: int -> bool)
    requires MulAuto() ==> f(0) && (forall i: int {:trigger IsLe(0, i)} :: IsLe(0, i) && f(i) ==> f(i + 1)) && forall i: int {:trigger IsLe(i, 0)} :: IsLe(i, 0) && f(i) ==> f(i - 1)
    ensures MulAuto()
    ensures forall i: int {:trigger f(i)} :: f(i)
  {
  }
}

module {:options ""-functionSyntax:4""} GeneralInternals {
  predicate IsLe(x: int, y: int)
    decreases x, y
  {
    x <= y
  }

  lemma LemmaInductionHelper(n: int, f: int -> bool, x: int)
    requires n > 0
    requires forall i: int {:trigger f(i)} :: 0 <= i < n ==> f(i)
    requires forall i: int {:trigger f(i), f(i + n)} :: i >= 0 && f(i) ==> f(i + n)
    requires forall i: int {:trigger f(i), f(i - n)} :: i < n && f(i) ==> f(i - n)
    ensures f(x)
    decreases if x >= n then x else -x
  {
  }
}

module {:options ""-functionSyntax:4""} DivMod {

  import opened DivInternals

  import DivINL = DivInternalsNonlinear

  import opened ModInternals

  import ModINL = ModInternalsNonlinear

  import opened MulInternals

  import opened Mul

  import opened GeneralInternals
  lemma LemmaDivIsDivRecursive(x: int, d: int)
    requires 0 < d
    ensures DivRecursive(x, d) == x / d
    decreases x, d
  {
  }

  lemma LemmaDivIsDivRecursiveAuto()
    ensures forall x: int, d: int {:trigger x / d} :: d > 0 ==> DivRecursive(x, d) == x / d
  {
  }

  lemma LemmaDivBySelf(d: int)
    requires d != 0
    ensures d / d == 1
    decreases d
  {
  }

  lemma LemmaDivOf0(d: int)
    requires d != 0
    ensures 0 / d == 0
    decreases d
  {
  }

  lemma LemmaDivBasics(x: int)
    ensures x != 0 ==> 0 / x == 0
    ensures x / 1 == x
    ensures x != 0 ==> x / x == 1
    decreases x
  {
  }

  lemma LemmaDivBasicsAuto()
    ensures forall x: int {:trigger 0 / x} :: x != 0 ==> 0 / x == 0
    ensures forall x: int {:trigger x / 1} :: x / 1 == x
    ensures forall x: int, y: int {:trigger x / y} :: x >= 0 && y > 0 ==> x / y >= 0
    ensures forall x: int, y: int {:trigger x / y} :: x >= 0 && y > 0 ==> x / y <= x
  {
  }

  lemma LemmaSmallDivConverseAuto()
    ensures forall x: int, d: int {:trigger x / d} :: 0 <= x && 0 < d && x / d == 0 ==> x < d
  {
  }

  lemma LemmaDivNonZero(x: int, d: int)
    requires x >= d > 0
    ensures x / d > 0
    decreases x, d
  {
  }

  lemma LemmaDivNonZeroAuto()
    ensures forall x: int, d: int {:trigger x / d} | x >= d > 0 :: x / d > 0
  {
  }

  lemma LemmaDivIsOrderedByDenominator(x: int, y: int, z: int)
    requires 0 <= x
    requires 1 <= y <= z
    ensures x / y >= x / z
    decreases x
  {
  }

  lemma LemmaDivIsOrderedByDenominatorAuto()
    ensures forall z: int, y: int, x: int {:trigger x / y, x / z} :: 0 <= x && 1 <= y <= z ==> x / y >= x / z
  {
  }

  lemma LemmaDivIsStrictlyOrderedByDenominator(x: int, d: int)
    requires 0 < x
    requires 1 < d
    ensures x / d < x
    decreases x
  {
  }

  lemma LemmaDivIsStrictlyOrderedByDenominatorAuto()
    ensures forall x: int, d: int {:trigger x / d} :: 0 < x && 1 < d ==> x / d < x
  {
  }

  lemma LemmaDividingSums(a: int, b: int, d: int, R: int)
    requires 0 < d
    requires R == a % d + b % d - (a + b) % d
    ensures d * (a + b) / d - R == d * a / d + d * b / d
    decreases a, b, d, R
  {
  }

  lemma LemmaDividingSumsAuto()
    ensures forall a: int, b: int, d: int, R: int {:trigger d * (a + b) / d - R, d * a / d + d * b / d} :: 0 < d && R == a % d + b % d - (a + b) % d ==> d * (a + b) / d - R == d * a / d + d * b / d
  {
  }

  lemma LemmaDivPosIsPos(x: int, d: int)
    requires 0 <= x
    requires 0 < d
    ensures 0 <= x / d
    decreases x, d
  {
  }

  lemma LemmaDivPosIsPosAuto()
    ensures forall x: int, d: int {:trigger x / d} :: 0 <= x && 0 < d ==> 0 <= x / d
  {
  }

  lemma LemmaDivPlusOne(x: int, d: int)
    requires 0 < d
    ensures 1 + x / d == (d + x) / d
    decreases x, d
  {
  }

  lemma LemmaDivPlusOneAuto()
    ensures forall x: int, d: int {:trigger 1 + x / d, (d + x) / d} :: 0 < d ==> 1 + x / d == (d + x) / d
  {
  }

  lemma LemmaDivMinusOne(x: int, d: int)
    requires 0 < d
    ensures -1 + x / d == (-d + x) / d
    decreases x, d
  {
  }

  lemma LemmaDivMinusOneAuto()
    ensures forall x: int, d: int {:trigger -1 + x / d, (-d + x) / d} :: 0 < d ==> -1 + x / d == (-d + x) / d
  {
  }

  lemma LemmaBasicDiv(d: int)
    requires 0 < d
    ensures forall x: int {:trigger x / d} :: 0 <= x < d ==> x / d == 0
    decreases d
  {
  }

  lemma LemmaBasicDivAuto()
    ensures forall d: int, x: int {:trigger x / d} :: 0 <= x < d ==> x / d == 0
  {
  }

  lemma LemmaDivIsOrdered(x: int, y: int, z: int)
    requires x <= y
    requires 0 < z
    ensures x / z <= y / z
    decreases x, y, z
  {
  }

  lemma LemmaDivIsOrderedAuto()
    ensures forall x: int, y: int, z: int {:trigger x / z, y / z} :: x <= y && 0 < z ==> x / z <= y / z
  {
  }

  lemma LemmaDivDecreases(x: int, d: int)
    requires 0 < x
    requires 1 < d
    ensures x / d < x
    decreases x, d
  {
  }

  lemma LemmaDivDecreasesAuto()
    ensures forall x: int, d: int {:trigger x / d} :: 0 < x && 1 < d ==> x / d < x
  {
  }

  lemma LemmaDivNonincreasing(x: int, d: int)
    requires 0 <= x
    requires 0 < d
    ensures x / d <= x
    decreases x, d
  {
  }

  lemma LemmaDivNonincreasingAuto()
    ensures forall x: int, d: int {:trigger x / d} :: 0 <= x && 0 < d ==> x / d <= x
  {
  }

  lemma LemmaSmallMod(x: nat, m: nat)
    requires x < m
    requires 0 < m
    ensures x % m == x
    decreases x, m
  {
  }

  lemma LemmaBreakdown(x: int, y: int, z: int)
    requires 0 <= x
    requires 0 < y
    requires 0 < z
    ensures 0 < y * z
    ensures x % (y * z) == y * x / y % z + x % y
    decreases x, y, z
  {
  }

  lemma LemmaBreakdownAuto()
    ensures forall x: int, y: int, z: int {:trigger y * z, x % (y * z), y * x / y % z + x % y} :: (0 <= x && 0 < y && 0 < z ==> 0 < y * z) && (0 <= x && 0 < y && 0 < z ==> x % (y * z) == y * x / y % z + x % y)
  {
  }

  lemma LemmaRemainderUpper(x: int, d: int)
    requires 0 <= x
    requires 0 < d
    ensures x - d < x / d * d
    decreases x, d
  {
  }

  lemma LemmaRemainderUpperAuto()
    ensures forall x: int, d: int {:trigger x - d, d * d} :: 0 <= x && 0 < d ==> x - d < x / d * d
  {
  }

  lemma LemmaRemainderLower(x: int, d: int)
    requires 0 <= x
    requires 0 < d
    ensures x >= x / d * d
    decreases x, d
  {
  }

  lemma LemmaRemainderLowerAuto()
    ensures forall x: int, d: int {:trigger x / d * d} :: 0 <= x && 0 < d ==> x >= x / d * d
  {
  }

  lemma LemmaRemainder(x: int, d: int)
    requires 0 <= x
    requires 0 < d
    ensures 0 <= x - x / d * d < d
    decreases x, d
  {
  }

  lemma LemmaRemainderAuto()
    ensures forall x: int, d: int {:trigger x - x / d * d} :: (0 <= x && 0 < d ==> 0 <= x - x / d * d) && (0 <= x && 0 < d ==> x - x / d * d < d)
  {
  }

  lemma LemmaFundamentalDivMod(x: int, d: int)
    requires d != 0
    ensures x == d * x / d + x % d
    decreases x, d
  {
  }

  lemma LemmaFundamentalDivModAuto()
    ensures forall x: int, d: int {:trigger d * x / d + x % d} :: d != 0 ==> x == d * x / d + x % d
  {
  }

  lemma LemmaDivDenominator(x: int, c: nat, d: nat)
    requires 0 <= x
    requires 0 < c
    requires 0 < d
    ensures c * d != 0
    ensures x / c / d == x / (c * d)
    decreases x, c, d
  {
  }

  lemma LemmaDivDenominatorAuto()
    ensures forall c: nat, d: nat {:trigger c * d} :: 0 < c && 0 < d ==> c * d != 0
    ensures forall x: int, c: nat, d: nat {:trigger x / c / d} :: 0 <= x && 0 < c && 0 < d ==> x / c / d == x / (c * d)
  {
  }

  lemma LemmaMulHoistInequality(x: int, y: int, z: int)
    requires 0 <= x
    requires 0 < z
    ensures x * y / z <= x * y / z
    decreases x, y, z
  {
  }

  lemma LemmaMulHoistInequalityAuto()
    ensures forall x: int, y: int, z: int {:trigger x * y / z, x * y / z} :: 0 <= x && 0 < z ==> x * y / z <= x * y / z
  {
  }

  lemma LemmaIndistinguishableQuotients(a: int, b: int, d: int)
    requires 0 < d
    requires 0 <= a - a % d <= b < a + d - a % d
    ensures a / d == b / d
    decreases a, b, d
  {
  }

  lemma LemmaIndistinguishableQuotientsAuto()
    ensures forall a: int, b: int, d: int {:trigger a / d, b / d} :: 0 < d && 0 <= a - a % d <= b < a + d - a % d ==> a / d == b / d
  {
  }

  lemma LemmaTruncateMiddle(x: int, b: int, c: int)
    requires 0 <= x
    requires 0 < b
    requires 0 < c
    ensures 0 < b * c
    ensures b * x % (b * c) == b * x % c
    decreases x, b, c
  {
  }

  lemma LemmaTruncateMiddleAuto()
    ensures forall x: int, b: int, c: int {:trigger b * x % c} :: 0 <= x && 0 < b && 0 < c && 0 < b * c ==> b * x % (b * c) == b * x % c
  {
  }

  lemma LemmaDivMultiplesVanishQuotient(x: int, a: int, d: int)
    requires 0 < x
    requires 0 <= a
    requires 0 < d
    ensures 0 < x * d
    ensures a / d == x * a / (x * d)
    decreases x, a, d
  {
  }

  lemma LemmaDivMultiplesVanishQuotientAuto()
    ensures (forall x: int, a: int, d: int {:trigger a / d, x * d, x * a} :: 0 < x && 0 <= a && 0 < d ==> 0 < x * d) && forall x: int, a: int, d: int {:trigger a / d, x * d, x * a} :: 0 < x && 0 <= a && 0 < d ==> a / d == x * a / (x * d)
  {
  }

  lemma LemmaRoundDown(a: int, r: int, d: int)
    requires 0 < d
    requires a % d == 0
    requires 0 <= r < d
    ensures a == d * (a + r) / d
    decreases a, r, d
  {
  }

  lemma LemmaRoundDownAuto()
    ensures forall d: int, r: int, a: int {:trigger d * (a + r) / d} :: 0 < d && a % d == 0 && 0 <= r < d ==> a == d * (a + r) / d
  {
  }

  lemma LemmaDivMultiplesVanishFancy(x: int, b: int, d: int)
    requires 0 < d
    requires 0 <= b < d
    ensures (d * x + b) / d == x
    decreases x, b, d
  {
  }

  lemma LemmaDivMultiplesVanishFancyAuto()
    ensures forall d: int, b: int, x: int {:trigger (d * x + b) / d} :: 0 < d && 0 <= b < d ==> (d * x + b) / d == x
  {
  }

  lemma LemmaDivMultiplesVanish(x: int, d: int)
    requires 0 < d
    ensures d * x / d == x
    decreases x, d
  {
  }

  lemma LemmaDivMultiplesVanishAuto()
    ensures forall x: int, d: int {:trigger d * x / d} :: 0 < d ==> d * x / d == x
  {
  }

  lemma LemmaDivByMultiple(b: int, d: int)
    requires 0 <= b
    requires 0 < d
    ensures b * d / d == b
    decreases b, d
  {
  }

  lemma LemmaDivByMultipleAuto()
    ensures forall b: int, d: int {:trigger b * d / d} :: 0 <= b && 0 < d ==> b * d / d == b
  {
  }

  lemma LemmaDivByMultipleIsStronglyOrdered(x: int, y: int, m: int, z: int)
    requires x < y
    requires y == m * z
    requires 0 < z
    ensures x / z < y / z
    decreases x, y, m, z
  {
  }

  lemma LemmaDivByMultipleIsStronglyOrderedAuto()
    ensures forall z: int, m: int, y: int, x: int {:trigger x / z, m * z, y / z} :: x < y && y == m * z && 0 < z ==> x / z < y / z
  {
  }

  lemma LemmaMultiplyDivideLe(a: int, b: int, c: int)
    requires 0 < b
    requires a <= b * c
    ensures a / b <= c
    decreases a, b, c
  {
  }

  lemma LemmaMultiplyDivideLeAuto()
    ensures forall a: int, b: int, c: int {:trigger a / b, b * c} :: 0 < b && a <= b * c ==> a / b <= c
  {
  }

  lemma LemmaMultiplyDivideLt(a: int, b: int, c: int)
    requires 0 < b
    requires a < b * c
    ensures a / b < c
    decreases a, b, c
  {
  }

  lemma LemmaMultiplyDivideLtAuto()
    ensures forall a: int, b: int, c: int {:trigger a / b, b * c} :: 0 < b && a < b * c ==> a / b < c
  {
  }

  lemma LemmaHoistOverDenominator(x: int, j: int, d: nat)
    requires 0 < d
    ensures x / d + j == (x + j * d) / d
    decreases x, j, d
  {
  }

  lemma LemmaHoistOverDenominatorAuto()
    ensures forall x: int, j: int, d: nat {:trigger x / d + j} :: 0 < d ==> x / d + j == (x + j * d) / d
  {
  }

  lemma LemmaPartBound1(a: int, b: int, c: int)
    requires 0 <= a
    requires 0 < b
    requires 0 < c
    ensures 0 < b * c
    ensures b * a / b % (b * c) <= b * (c - 1)
    decreases a, b, c
  {
  }

  lemma LemmaPartBound1Auto()
    ensures (forall a: int, b: int, c: int {:trigger b * a / b % (b * c)} :: 0 <= a && 0 < b && 0 < c ==> 0 < b * c) && forall a: int, b: int, c: int {:trigger b * a / b % (b * c)} :: 0 <= a && 0 < b && 0 < c ==> b * a / b % (b * c) <= b * (c - 1)
  {
  }

  lemma /*{:_induction x, m}*/ LemmaModIsModRecursive(x: int, m: int)
    requires m > 0
    ensures ModRecursive(x, m) == x % m
    decreases if x < 0 then -x + m else x
  {
  }

  lemma LemmaModIsModRecursiveAuto()
    ensures forall x: int, d: int {:trigger x % d} :: d > 0 ==> ModRecursive(x, d) == x % d
  {
  }

  lemma LemmaModBasicsAuto()
    ensures forall m: int {:trigger m % m} :: m > 0 ==> m % m == 0
    ensures forall x: int, m: int {:trigger x % m % m} :: m > 0 ==> x % m % m == x % m
  {
  }

  lemma LemmaModPropertiesAuto()
    ensures forall m: int {:trigger m % m} :: m > 0 ==> m % m == 0
    ensures forall x: int, m: int {:trigger x % m % m} :: m > 0 ==> x % m % m == x % m
    ensures forall x: int, m: int {:trigger x % m} :: (m > 0 ==> 0 <= x % m) && (m > 0 ==> x % m < m)
  {
  }

  lemma LemmaModDecreases(x: nat, m: nat)
    requires 0 < m
    ensures x % m <= x
    decreases x, m
  {
  }

  lemma LemmaModDecreasesAuto()
    ensures forall x: nat, m: nat {:trigger x % m} :: 0 < m ==> x % m <= x
  {
  }

  lemma LemmaModIsZero(x: nat, m: nat)
    requires x > 0 && m > 0
    requires x % m == 0
    ensures x >= m
    decreases x, m
  {
  }

  lemma LemmaModIsZeroAuto()
    ensures forall m: nat, x: nat {:trigger x % m} :: x > 0 && m > 0 && x % m == 0 ==> x >= m
  {
  }

  lemma LemmaModMultiplesBasic(x: int, m: int)
    requires m > 0
    ensures x * m % m == 0
    decreases x, m
  {
  }

  lemma LemmaModMultiplesBasicAuto()
    ensures forall x: int, m: int {:trigger x * m % m} :: m > 0 ==> x * m % m == 0
  {
  }

  lemma LemmaModAddMultiplesVanish(b: int, m: int)
    requires 0 < m
    ensures (m + b) % m == b % m
    decreases b, m
  {
  }

  lemma LemmaModAddMultiplesVanishAuto()
    ensures forall b: int, m: int {:trigger b % m} :: 0 < m ==> (m + b) % m == b % m
  {
  }

  lemma LemmaModSubMultiplesVanish(b: int, m: int)
    requires 0 < m
    ensures (-m + b) % m == b % m
    decreases b, m
  {
  }

  lemma LemmaModSubMultiplesVanishAuto()
    ensures forall b: int, m: int {:trigger b % m} :: 0 < m ==> (-m + b) % m == b % m
  {
  }

  lemma LemmaModMultiplesVanish(a: int, b: int, m: int)
    requires 0 < m
    ensures (m * a + b) % m == b % m
    decreases if a > 0 then a else -a
  {
  }

  lemma LemmaModMultiplesVanishAuto()
    ensures forall a: int, b: int, m: int {:trigger (m * a + b) % m} :: 0 < m ==> (m * a + b) % m == b % m
  {
  }

  lemma LemmaModSubtraction(x: nat, s: nat, d: nat)
    requires 0 < d
    requires 0 <= s <= x % d
    ensures x % d - s % d == (x - s) % d
    decreases x, s, d
  {
  }

  lemma LemmaModSubtractionAuto()
    ensures forall x: nat, s: nat, d: nat {:trigger (x - s) % d} :: 0 < d && 0 <= s <= x % d ==> x % d - s % d == (x - s) % d
  {
  }

  lemma LemmaAddModNoop(x: int, y: int, m: int)
    requires 0 < m
    ensures (x % m + y % m) % m == (x + y) % m
    decreases x, y, m
  {
  }

  lemma LemmaAddModNoopAuto()
    ensures forall x: int, y: int, m: int {:trigger (x + y) % m} :: 0 < m ==> (x % m + y % m) % m == (x + y) % m
  {
  }

  lemma LemmaAddModNoopRight(x: int, y: int, m: int)
    requires 0 < m
    ensures (x + y % m) % m == (x + y) % m
    decreases x, y, m
  {
  }

  lemma LemmaAddModNoopRightAuto()
    ensures forall x: int, y: int, m: int {:trigger (x + y) % m} :: 0 < m ==> (x + y % m) % m == (x + y) % m
  {
  }

  lemma LemmaSubModNoop(x: int, y: int, m: int)
    requires 0 < m
    ensures (x % m - y % m) % m == (x - y) % m
    decreases x, y, m
  {
  }

  lemma LemmaSubModNoopAuto()
    ensures forall x: int, y: int, m: int {:trigger (x - y) % m} :: 0 < m ==> (x % m - y % m) % m == (x - y) % m
  {
  }

  lemma LemmaSubModNoopRight(x: int, y: int, m: int)
    requires 0 < m
    ensures (x - y % m) % m == (x - y) % m
    decreases x, y, m
  {
  }

  lemma LemmaSubModNoopRightAuto()
    ensures forall x: int, y: int, m: int {:trigger (x - y) % m} :: 0 < m ==> (x - y % m) % m == (x - y) % m
  {
  }

  lemma LemmaModAdds(a: int, b: int, d: int)
    requires 0 < d
    ensures a % d + b % d == (a + b) % d + d * (a % d + b % d) / d
    ensures a % d + b % d < d ==> a % d + b % d == (a + b) % d
    decreases a, b, d
  {
  }

  lemma LemmaModAddsAuto()
    ensures forall a: int, b: int, d: int {:trigger (a + b) % d} :: (0 < d ==> a % d + b % d == (a + b) % d + d * (a % d + b % d) / d) && (0 < d ==> a % d + b % d < d ==> a % d + b % d == (a + b) % d)
  {
  }

  lemma {:vcs_split_on_every_assert} LemmaModNegNeg(x: int, d: int)
    requires 0 < d
    ensures x % d == x * (1 - d) % d
    decreases x, d
  {
  }

  lemma {:timeLimitMultiplier 5} /*{:_timeLimit 50}*/ LemmaFundamentalDivModConverse(x: int, d: int, q: int, r: int)
    requires d != 0
    requires 0 <= r < d
    requires x == q * d + r
    ensures q == x / d
    ensures r == x % d
    decreases x, d, q, r
  {
  }

  lemma {:timeLimitMultiplier 5} /*{:_timeLimit 50}*/ LemmaFundamentalDivModConverseAuto()
    ensures forall x: int, d: int, q: int, r: int {:trigger q * d + r, x % d} :: (d != 0 && 0 <= r < d && x == q * d + r ==> q == x / d) && (d != 0 && 0 <= r < d && x == q * d + r ==> r == x % d)
  {
  }

  lemma LemmaModPosBound(x: int, m: int)
    requires 0 <= x
    requires 0 < m
    ensures 0 <= x % m < m
    decreases x
  {
  }

  lemma LemmaModPosBoundAuto()
    ensures forall x: int, m: int {:trigger x % m} :: (0 <= x && 0 < m ==> 0 <= x % m) && (0 <= x && 0 < m ==> x % m < m)
  {
  }

  lemma LemmaMulModNoopLeft(x: int, y: int, m: int)
    requires 0 < m
    ensures x % m * y % m == x * y % m
    decreases x, y, m
  {
  }

  lemma LemmaMulModNoopLeftAuto()
    ensures forall x: int, y: int, m: int {:trigger x * y % m} :: 0 < m ==> x % m * y % m == x * y % m
  {
  }

  lemma LemmaMulModNoopRight(x: int, y: int, m: int)
    requires 0 < m
    ensures x * y % m % m == x * y % m
    decreases x, y, m
  {
  }

  lemma LemmaMulModNoopRightAuto()
    ensures forall x: int, y: int, m: int {:trigger x * y % m} :: 0 < m ==> x * y % m % m == x * y % m
  {
  }

  lemma LemmaMulModNoopGeneral(x: int, y: int, m: int)
    requires 0 < m
    ensures x % m * y % m == x * y % m
    ensures x * y % m % m == x * y % m
    ensures x % m * y % m % m == x * y % m
    decreases x, y, m
  {
  }

  lemma LemmaMulModNoopGeneralAuto()
    ensures (forall x: int, y: int, m: int {:trigger x * y % m} :: 0 < m ==> x % m * y % m == x * y % m % m) && forall x: int, y: int, m: int {:trigger x * y % m} :: (0 < m ==> x * y % m % m == x % m * y % m % m) && (0 < m ==> x % m * y % m % m == x * y % m)
  {
  }

  lemma LemmaMulModNoop(x: int, y: int, m: int)
    requires 0 < m
    ensures x % m * y % m % m == x * y % m
    decreases x, y, m
  {
  }

  lemma LemmaMulModNoopAuto()
    ensures forall x: int, y: int, m: int {:trigger x * y % m} :: 0 < m ==> x % m * y % m % m == x * y % m
  {
  }

  lemma LemmaModEquivalence(x: int, y: int, m: int)
    requires 0 < m
    ensures x % m == y % m <==> (x - y) % m == 0
    decreases x, y, m
  {
  }

  lemma LemmaModEquivalenceAuto()
    ensures forall x: int, y: int, m: int {:trigger x % m, y % m} :: 0 < m && x % m == y % m <==> 0 < m && (x - y) % m == 0
  {
  }

  predicate IsModEquivalent(x: int, y: int, m: int)
    requires m > 0
    ensures x % m == y % m <==> (x - y) % m == 0
    decreases x, y, m
  {
    LemmaModEquivalence(x, y, m);
    (x - y) % m == 0
  }

  lemma LemmaModMulEquivalent(x: int, y: int, z: int, m: int)
    requires m > 0
    requires IsModEquivalent(x, y, m)
    ensures IsModEquivalent(x * z, y * z, m)
    decreases x, y, z, m
  {
  }

  lemma LemmaModMulEquivalentAuto()
    ensures forall x: int, y: int, z: int, m: int {:trigger IsModEquivalent(x * z, y * z, m)} :: m > 0 && IsModEquivalent(x, y, m) ==> IsModEquivalent(x * z, y * z, m)
  {
  }

  lemma LemmaModOrdering(x: int, k: int, d: int)
    requires 1 < d
    requires 0 < k
    ensures 0 < d * k
    ensures x % d <= x % (d * k)
    decreases x, k, d
  {
  }

  lemma LemmaModOrderingAuto()
    ensures forall x: int, k: int, d: int {:trigger x % (d * k)} :: (1 < d && 0 < k ==> 0 < d * k) && (1 < d && 0 < k ==> x % d <= x % (d * k))
  {
  }

  lemma LemmaModMod(x: int, a: int, b: int)
    requires 0 < a
    requires 0 < b
    ensures 0 < a * b
    ensures x % (a * b) % a == x % a
    decreases x, a, b
  {
  }

  lemma LemmaModModAuto()
    ensures (forall x: int, a: int, b: int {:trigger a * b, x % a} :: 0 < a && 0 < b ==> 0 < a * b) && forall x: int, a: int, b: int {:trigger a * b, x % a} :: 0 < a && 0 < b ==> x % (a * b) % a == x % a
  {
  }

  lemma LemmaPartBound2(x: int, y: int, z: int)
    requires 0 <= x
    requires 0 < y
    requires 0 < z
    ensures y * z > 0
    ensures x % y % (y * z) < y
    decreases x, y, z
  {
  }

  lemma LemmaPartBound2Auto()
    ensures (forall x: int, y: int, z: int {:trigger y * z, x % y} :: 0 <= x && 0 < y && 0 < z ==> y * z > 0) && forall x: int, y: int, z: int {:trigger y * z, x % y} :: 0 <= x && 0 < y && 0 < z ==> x % y % (y * z) < y
  {
  }

  lemma LemmaModBreakdown(x: int, y: int, z: int)
    requires 0 <= x
    requires 0 < y
    requires 0 < z
    ensures y * z > 0
    ensures x % (y * z) == y * x / y % z + x % y
    decreases x, y, z
  {
  }

  lemma LemmaModBreakdownAuto()
    ensures forall x: int, y: int, z: int {:trigger x % (y * z)} :: (0 <= x && 0 < y && 0 < z ==> y * z > 0) && (0 <= x && 0 < y && 0 < z ==> x % (y * z) == y * x / y % z + x % y)
  {
  }
}

module {:options ""-functionSyntax:4""} DivInternalsNonlinear {
  lemma LemmaDivOf0(d: int)
    requires d != 0
    ensures 0 / d == 0
    decreases d
  {
  }

  lemma LemmaDivBySelf(d: int)
    requires d != 0
    ensures d / d == 1
    decreases d
  {
  }

  lemma LemmaSmallDiv()
    ensures forall d: int, x: int {:trigger x / d} :: 0 <= x < d && d > 0 ==> x / d == 0
  {
  }

  lemma LemmaRealDivGt(x: real, y: real)
    requires x > y
    requires x >= 0.0
    requires y > 0.0
    ensures x / y > 1 as real
    decreases x, y
  {
  }
}

module {:options ""-functionSyntax:4""} DivInternals {

  import opened GeneralInternals

  import opened ModInternals

  import opened ModInternalsNonlinear

  import opened DivInternalsNonlinear

  import opened MulInternals
  function method {:opaque} {:fuel 0, 0} DivPos(x: int, d: int): int
    requires d > 0
    decreases if x < 0 then d - x else x
  {
    if x < 0 then
      -1 + DivPos(x + d, d)
    else if x < d then
      0
    else
      1 + DivPos(x - d, d)
  }

  function method {:opaque} {:fuel 0, 0} DivRecursive(x: int, d: int): int
    requires d != 0
    decreases x, d
  {
    reveal DivPos();
    if d > 0 then
      DivPos(x, d)
    else
      -1 * DivPos(x, -1 * d)
  }

  lemma LemmaDivBasics(n: int)
    requires n > 0
    ensures n / n == -(-n / n) == 1
    ensures forall x: int {:trigger x / n} :: 0 <= x < n <==> x / n == 0
    ensures forall x: int {:trigger (x + n) / n} :: (x + n) / n == x / n + 1
    ensures forall x: int {:trigger (x - n) / n} :: (x - n) / n == x / n - 1
    decreases n
  {
  }

  predicate DivAuto(n: int)
    requires n > 0
    decreases n
  {
    ModAuto(n) &&
    n / n == -(-n / n) == 1 &&
    (forall x: int {:trigger x / n} :: 
      0 <= x < n <==> x / n == 0) &&
    (forall x: int, y: int {:trigger (x + y) / n} :: 
      ghost var z: int := x % n + y % n; (0 <= z < n && (x + y) / n == x / n + y / n) || (n <= z < n + n && (x + y) / n == x / n + y / n + 1)) &&
    forall x: int, y: int {:trigger (x - y) / n} :: 
      ghost var z: int := x % n - y % n; (0 <= z < n && (x - y) / n == x / n - y / n) || (-n <= z < 0 && (x - y) / n == x / n - y / n - 1)
  }

  lemma LemmaDivAuto(n: int)
    requires n > 0
    ensures DivAuto(n)
    decreases n
  {
  }

  lemma LemmaDivInductionAuto(n: int, x: int, f: int -> bool)
    requires n > 0
    requires DivAuto(n) ==> (forall i: int {:trigger IsLe(0, i)} :: IsLe(0, i) && i < n ==> f(i)) && (forall i: int {:trigger IsLe(0, i)} :: IsLe(0, i) && f(i) ==> f(i + n)) && forall i: int {:trigger IsLe(i + 1, n)} :: IsLe(i + 1, n) && f(i) ==> f(i - n)
    ensures DivAuto(n)
    ensures f(x)
    decreases n, x
  {
  }

  lemma LemmaDivInductionAutoForall(n: int, f: int -> bool)
    requires n > 0
    requires DivAuto(n) ==> (forall i: int {:trigger IsLe(0, i)} :: IsLe(0, i) && i < n ==> f(i)) && (forall i: int {:trigger IsLe(0, i)} :: IsLe(0, i) && f(i) ==> f(i + n)) && forall i: int {:trigger IsLe(i + 1, n)} :: IsLe(i + 1, n) && f(i) ==> f(i - n)
    ensures DivAuto(n)
    ensures forall i: int {:trigger f(i)} :: f(i)
    decreases n
  {
  }
}

module {:options ""-functionSyntax:4""} ModInternals {

  import opened GeneralInternals

  import opened Mul

  import opened MulInternalsNonlinear

  import opened MulInternals

  import opened ModInternalsNonlinear

  import opened DivInternalsNonlinear
  function method {:opaque} {:fuel 0, 0} ModRecursive(x: int, d: int): int
    requires d > 0
    decreases if x < 0 then d - x else x
  {
    if x < 0 then
      ModRecursive(d + x, d)
    else if x < d then
      x
    else
      ModRecursive(x - d, d)
  }

  lemma LemmaModInductionForall(n: int, f: int -> bool)
    requires n > 0
    requires forall i: int {:trigger f(i)} :: 0 <= i < n ==> f(i)
    requires forall i: int {:trigger f(i), f(i + n)} :: i >= 0 && f(i) ==> f(i + n)
    requires forall i: int {:trigger f(i), f(i - n)} :: i < n && f(i) ==> f(i - n)
    ensures forall i: int {:trigger f(i)} :: f(i)
    decreases n
  {
  }

  lemma LemmaModInductionForall2(n: int, f: (int, int) -> bool)
    requires n > 0
    requires forall i: int, j: int {:trigger f(i, j)} :: 0 <= i < n && 0 <= j < n ==> f(i, j)
    requires forall i: int, j: int {:trigger f(i, j), f(i + n, j)} :: i >= 0 && f(i, j) ==> f(i + n, j)
    requires forall i: int, j: int {:trigger f(i, j), f(i, j + n)} :: j >= 0 && f(i, j) ==> f(i, j + n)
    requires forall i: int, j: int {:trigger f(i, j), f(i - n, j)} :: i < n && f(i, j) ==> f(i - n, j)
    requires forall i: int, j: int {:trigger f(i, j), f(i, j - n)} :: j < n && f(i, j) ==> f(i, j - n)
    ensures forall i: int, j: int {:trigger f(i, j)} :: f(i, j)
    decreases n
  {
  }

  lemma LemmaDivAddDenominator(n: int, x: int)
    requires n > 0
    ensures (x + n) / n == x / n + 1
    decreases n, x
  {
  }

  lemma LemmaDivSubDenominator(n: int, x: int)
    requires n > 0
    ensures (x - n) / n == x / n - 1
    decreases n, x
  {
  }

  lemma LemmaModAddDenominator(n: int, x: int)
    requires n > 0
    ensures (x + n) % n == x % n
    decreases n, x
  {
  }

  lemma LemmaModSubDenominator(n: int, x: int)
    requires n > 0
    ensures (x - n) % n == x % n
    decreases n, x
  {
  }

  lemma LemmaModBelowDenominator(n: int, x: int)
    requires n > 0
    ensures 0 <= x < n <==> x % n == x
    decreases n, x
  {
  }

  lemma LemmaModBasics(n: int)
    requires n > 0
    ensures forall x: int {:trigger (x + n) % n} :: (x + n) % n == x % n
    ensures forall x: int {:trigger (x - n) % n} :: (x - n) % n == x % n
    ensures forall x: int {:trigger (x + n) / n} :: (x + n) / n == x / n + 1
    ensures forall x: int {:trigger (x - n) / n} :: (x - n) / n == x / n - 1
    ensures forall x: int {:trigger x % n} :: 0 <= x < n <==> x % n == x
    decreases n
  {
  }

  lemma {:vcs_split_on_every_assert} LemmaQuotientAndRemainder(x: int, q: int, r: int, n: int)
    requires n > 0
    requires 0 <= r < n
    requires x == q * n + r
    ensures q == x / n
    ensures r == x % n
    decreases if q > 0 then q else -q
  {
  }

  predicate ModAuto(n: int)
    requires n > 0
    decreases n
  {
    n % n == -n % n == 0 &&
    (forall x: int {:trigger x % n % n} :: 
      x % n % n == x % n) &&
    (forall x: int {:trigger x % n} :: 
      0 <= x < n <==> x % n == x) &&
    (forall x: int, y: int {:trigger (x + y) % n} :: 
      ghost var z: int := x % n + y % n; (0 <= z < n && (x + y) % n == z) || (n <= z < n + n && (x + y) % n == z - n)) &&
    forall x: int, y: int {:trigger (x - y) % n} :: 
      ghost var z: int := x % n - y % n; (0 <= z < n && (x - y) % n == z) || (-n <= z < 0 && (x - y) % n == z + n)
  }

  lemma LemmaModAuto(n: int)
    requires n > 0
    ensures ModAuto(n)
    decreases n
  {
  }

  lemma LemmaModInductionAuto(n: int, x: int, f: int -> bool)
    requires n > 0
    requires ModAuto(n) ==> (forall i: int {:trigger IsLe(0, i)} :: IsLe(0, i) && i < n ==> f(i)) && (forall i: int {:trigger IsLe(0, i)} :: IsLe(0, i) && f(i) ==> f(i + n)) && forall i: int {:trigger IsLe(i + 1, n)} :: IsLe(i + 1, n) && f(i) ==> f(i - n)
    ensures ModAuto(n)
    ensures f(x)
    decreases n, x
  {
  }

  lemma LemmaModInductionAutoForall(n: int, f: int -> bool)
    requires n > 0
    requires ModAuto(n) ==> (forall i: int {:trigger IsLe(0, i)} :: IsLe(0, i) && i < n ==> f(i)) && (forall i: int {:trigger IsLe(0, i)} :: IsLe(0, i) && f(i) ==> f(i + n)) && forall i: int {:trigger IsLe(i + 1, n)} :: IsLe(i + 1, n) && f(i) ==> f(i - n)
    ensures ModAuto(n)
    ensures forall i: int {:trigger f(i)} :: f(i)
    decreases n
  {
  }
}

module {:options ""-functionSyntax:4""} ModInternalsNonlinear {
  lemma LemmaModOfZeroIsZero(m: int)
    requires 0 < m
    ensures 0 % m == 0
    decreases m
  {
  }

  lemma LemmaFundamentalDivMod(x: int, d: int)
    requires d != 0
    ensures x == d * x / d + x % d
    decreases x, d
  {
  }

  lemma Lemma0ModAnything()
    ensures forall m: int {:trigger 0 % m} :: m > 0 ==> 0 % m == 0
  {
  }

  lemma LemmaSmallMod(x: nat, m: nat)
    requires x < m
    requires 0 < m
    ensures x % m == x
    decreases x, m
  {
  }

  lemma LemmaModRange(x: int, m: int)
    requires m > 0
    ensures 0 <= x % m < m
    decreases x, m
  {
  }
}

module {:options ""-functionSyntax:4""} Logarithm {

  import opened Mul

  import opened DivMod

  import opened Power
  function method {:opaque} {:fuel 0, 0} Log(base: nat, pow: nat): nat
    requires base > 1
    decreases pow
  {
    if pow < base then
      0
    else
      LemmaDivPosIsPosAuto(); LemmaDivDecreasesAuto(); 1 + Log(base, pow / base)
  }

  lemma {:induction false} LemmaLog0(base: nat, pow: nat)
    requires base > 1
    requires pow < base
    ensures Log(base, pow) == 0
    decreases base, pow
  {
  }

  lemma {:induction false} LemmaLogS(base: nat, pow: nat)
    requires base > 1
    requires pow >= base
    ensures pow / base >= 0
    ensures Log(base, pow) == 1 + Log(base, pow / base)
    decreases base, pow
  {
  }

  lemma {:induction false} LemmaLogSAuto()
    ensures forall pow: nat, base: nat {:trigger Log(base, pow / base)} | base > 1 && pow >= base :: pow / base >= 0 && Log(base, pow) == 1 + Log(base, pow / base)
  {
  }

  lemma {:induction false} LemmaLogIsOrdered(base: nat, pow: nat, pow': nat)
    requires base > 1
    requires pow <= pow'
    ensures Log(base, pow) <= Log(base, pow')
    decreases pow
  {
  }

  lemma {:induction false} LemmaLogPow(base: nat, n: nat)
    requires base > 1
    ensures (LemmaPowPositive(base, n); Log(base, Pow(base, n)) == n)
    decreases base, n
  {
  }
}

module {:options ""-functionSyntax:4""} Power {

  import opened DivMod

  import opened GeneralInternals

  import opened Mul

  import opened MulInternals
  function method {:opaque} {:fuel 0, 0} Pow(b: int, e: nat): int
    decreases e
  {
    if e == 0 then
      1
    else
      b * Pow(b, e - 1)
  }

  lemma /*{:_induction b}*/ LemmaPow0(b: int)
    ensures Pow(b, 0) == 1
    decreases b
  {
  }

  lemma LemmaPow0Auto()
    ensures forall b: nat {:trigger Pow(b, 0)} :: Pow(b, 0) == 1
  {
  }

  lemma /*{:_induction b}*/ LemmaPow1(b: int)
    ensures Pow(b, 1) == b
    decreases b
  {
  }

  lemma LemmaPow1Auto()
    ensures forall b: nat {:trigger Pow(b, 1)} :: Pow(b, 1) == b
  {
  }

  lemma /*{:_induction e}*/ Lemma0Pow(e: nat)
    requires e > 0
    ensures Pow(0, e) == 0
    decreases e
  {
  }

  lemma Lemma0PowAuto()
    ensures forall e: nat {:trigger Pow(0, e)} :: e > 0 ==> Pow(0, e) == 0
  {
  }

  lemma /*{:_induction e}*/ Lemma1Pow(e: nat)
    ensures Pow(1, e) == 1
    decreases e
  {
  }

  lemma Lemma1PowAuto()
    ensures forall e: nat {:trigger Pow(1, e)} :: Pow(1, e) == 1
  {
  }

  lemma /*{:_induction x}*/ LemmaSquareIsPow2(x: nat)
    ensures Pow(x, 2) == x * x
    decreases x
  {
  }

  lemma LemmaSquareIsPow2Auto()
    ensures forall x: nat {:trigger Pow(x, 2)} :: Pow(x, 2) == x * x
  {
  }

  lemma /*{:_induction b, e}*/ LemmaPowPositive(b: int, e: nat)
    requires b > 0
    ensures 0 < Pow(b, e)
    decreases b, e
  {
  }

  lemma LemmaPowPositiveAuto()
    ensures forall b: int, e: nat {:trigger Pow(b, e)} :: b > 0 ==> 0 < Pow(b, e)
  {
  }

  lemma /*{:_induction b, e1, e2}*/ LemmaPowAdds(b: int, e1: nat, e2: nat)
    ensures Pow(b, e1 + e2) == Pow(b, e1) * Pow(b, e2)
    decreases e1
  {
  }

  lemma LemmaPowAddsAuto()
    ensures forall b: int, e1: nat, e2: nat {:trigger Pow(b, e1 + e2)} :: Pow(b, e1 + e2) == Pow(b, e1) * Pow(b, e2)
  {
  }

  lemma /*{:_induction b, e1, e2}*/ LemmaPowSubAddCancel(b: int, e1: nat, e2: nat)
    requires e1 >= e2
    ensures Pow(b, e1 - e2) * Pow(b, e2) == Pow(b, e1)
    decreases e1
  {
  }

  lemma LemmaPowSubAddCancelAuto()
    ensures forall b: int, e1: nat, e2: nat {:trigger Pow(b, e1 - e2)} | e1 >= e2 :: Pow(b, e1 - e2) * Pow(b, e2) == Pow(b, e1)
  {
  }

  lemma /*{:_induction b, e1, e2}*/ LemmaPowSubtracts(b: nat, e1: nat, e2: nat)
    requires b > 0
    requires e1 <= e2
    ensures Pow(b, e1) > 0
    ensures Pow(b, e2 - e1) == Pow(b, e2) / Pow(b, e1) > 0
    decreases b, e1, e2
  {
  }

  lemma LemmaPowSubtractsAuto()
    ensures forall b: nat, e1: nat {:trigger Pow(b, e1)} :: b > 0 ==> Pow(b, e1) > 0
    ensures forall e2: nat, e1: nat, b: nat {:trigger Pow(b, e2 - e1)} :: (b > 0 && e1 <= e2 ==> Pow(b, e2 - e1) == Pow(b, e2) / Pow(b, e1)) && (b > 0 && e1 <= e2 ==> Pow(b, e2) / Pow(b, e1) > 0)
  {
  }

  lemma /*{:_induction a, b, c}*/ LemmaPowMultiplies(a: int, b: nat, c: nat)
    ensures 0 <= b * c
    ensures Pow(Pow(a, b), c) == Pow(a, b * c)
    decreases c
  {
  }

  lemma LemmaPowMultipliesAuto()
    ensures forall b: nat, c: nat {:trigger b * c} :: 0 <= b * c
    ensures forall a: int, b: nat, c: nat {:trigger Pow(a, b * c)} :: Pow(Pow(a, b), c) == Pow(a, b * c)
  {
  }

  lemma /*{:_induction a, b, e}*/ LemmaPowDistributes(a: int, b: int, e: nat)
    ensures Pow(a * b, e) == Pow(a, e) * Pow(b, e)
    decreases e
  {
  }

  lemma LemmaPowDistributesAuto()
    ensures forall a: int, b: int, e: nat {:trigger Pow(a * b, e)} :: Pow(a * b, e) == Pow(a, e) * Pow(b, e)
  {
  }

  lemma LemmaPowAuto()
    ensures forall x: int {:trigger Pow(x, 0)} :: Pow(x, 0) == 1
    ensures forall x: int {:trigger Pow(x, 1)} :: Pow(x, 1) == x
    ensures forall x: int, y: int {:trigger Pow(x, y)} :: y == 0 ==> Pow(x, y) == 1
    ensures forall x: int, y: int {:trigger Pow(x, y)} :: y == 1 ==> Pow(x, y) == x
    ensures forall x: int, y: int {:trigger x * y} :: 0 < x && 0 < y ==> x <= x * y
    ensures forall x: int, y: int {:trigger x * y} :: 0 < x && 1 < y ==> x < x * y
    ensures forall x: int, y: nat, z: nat {:trigger Pow(x, y + z)} :: Pow(x, y + z) == Pow(x, y) * Pow(x, z)
    ensures forall x: int, y: nat, z: nat {:trigger Pow(x, y - z)} :: y >= z ==> Pow(x, y - z) * Pow(x, z) == Pow(x, y)
    ensures forall x: int, y: int, z: nat {:trigger Pow(x * y, z)} :: Pow(x * y, z) == Pow(x, z) * Pow(y, z)
  {
  }

  lemma /*{:_induction b, e1, e2}*/ LemmaPowStrictlyIncreases(b: nat, e1: nat, e2: nat)
    requires 1 < b
    requires e1 < e2
    ensures Pow(b, e1) < Pow(b, e2)
    decreases b, e1, e2
  {
  }

  lemma LemmaPowStrictlyIncreasesAuto()
    ensures forall e2: nat, e1: nat, b: nat {:trigger Pow(b, e1), Pow(b, e2)} :: 1 < b && e1 < e2 ==> Pow(b, e1) < Pow(b, e2)
  {
  }

  lemma /*{:_induction b, e1, e2}*/ LemmaPowIncreases(b: nat, e1: nat, e2: nat)
    requires b > 0
    requires e1 <= e2
    ensures Pow(b, e1) <= Pow(b, e2)
    decreases b, e1, e2
  {
  }

  lemma LemmaPowIncreasesAuto()
    ensures forall e2: nat, e1: nat, b: nat {:trigger Pow(b, e1), Pow(b, e2)} :: 1 < b && e1 <= e2 ==> Pow(b, e1) <= Pow(b, e2)
  {
  }

  lemma /*{:_induction b, e1, e2}*/ LemmaPowStrictlyIncreasesConverse(b: nat, e1: nat, e2: nat)
    requires b > 0
    requires Pow(b, e1) < Pow(b, e2)
    ensures e1 < e2
    decreases b, e1, e2
  {
  }

  lemma LemmaPowStrictlyIncreasesConverseAuto()
    ensures forall b: nat, e1: nat, e2: nat {:trigger Pow(b, e1), Pow(b, e2)} :: b > 0 && Pow(b, e1) < Pow(b, e2) ==> e1 < e2
  {
  }

  lemma /*{:_induction b, e1, e2}*/ LemmaPowIncreasesConverse(b: nat, e1: nat, e2: nat)
    requires 1 < b
    requires Pow(b, e1) <= Pow(b, e2)
    ensures e1 <= e2
    decreases b, e1, e2
  {
  }

  lemma LemmaPowIncreasesConverseAuto()
    ensures forall b: nat, e1: nat, e2: nat {:trigger Pow(b, e1), Pow(b, e2)} :: 1 < b && Pow(b, e1) <= Pow(b, e2) ==> e1 <= e2
  {
  }

  lemma /*{:_induction b, x, y, z}*/ LemmaPullOutPows(b: nat, x: nat, y: nat, z: nat)
    requires b > 0
    ensures 0 <= x * y
    ensures 0 <= y * z
    ensures Pow(Pow(b, x * y), z) == Pow(Pow(b, x), y * z)
    decreases b, x, y, z
  {
  }

  lemma LemmaPullOutPowsAuto()
    ensures forall y: nat, z: nat {:trigger z * y} :: 0 <= z * y && 0 <= y * z
    ensures forall b: nat, x: nat, y: nat, z: nat {:trigger Pow(Pow(b, x * y), z)} :: b > 0 ==> Pow(Pow(b, x * y), z) == Pow(Pow(b, x), y * z)
  {
  }

  lemma /*{:_induction b, e1, e2}*/ LemmaPowDivisionInequality(x: nat, b: nat, e1: nat, e2: nat)
    requires b > 0
    requires e2 <= e1
    requires x < Pow(b, e1)
    ensures Pow(b, e2) > 0
    ensures x / Pow(b, e2) < Pow(b, e1 - e2)
    decreases x, b, e1, e2
  {
  }

  lemma LemmaPowDivisionInequalityAuto()
    ensures forall b: nat, e2: nat {:trigger Pow(b, e2)} :: b > 0 ==> Pow(b, e2) > 0
    ensures forall x: nat, b: nat, e1: nat, e2: nat {:trigger x / Pow(b, e2), Pow(b, e1 - e2)} :: b > 0 && e2 <= e1 && x < Pow(b, e1) ==> x / Pow(b, e2) < Pow(b, e1 - e2)
  {
  }

  lemma /*{:_induction b, e}*/ LemmaPowMod(b: nat, e: nat)
    requires b > 0 && e > 0
    ensures Pow(b, e) % b == 0
    decreases b, e
  {
  }

  lemma LemmaPowModAuto()
    ensures forall b: nat, e: nat {:trigger Pow(b, e)} :: b > 0 && e > 0 ==> Pow(b, e) % b == 0
  {
  }

  lemma /*{:_induction b, e, m}*/ LemmaPowModNoop(b: int, e: nat, m: int)
    requires m > 0
    ensures Pow(b % m, e) % m == Pow(b, e) % m
    decreases e
  {
  }

  lemma LemmaPowModNoopAuto()
    ensures forall b: nat, e: nat, m: nat {:trigger Pow(b % m, e)} :: m > 0 ==> Pow(b % m, e) % m == Pow(b, e) % m
  {
  }
}

module {:options ""-functionSyntax:4""} FileIO {

  import opened Wrappers

  export
    provides ReadBytesFromFile, WriteBytesToFile, Wrappers

  method ReadBytesFromFile(path: string) returns (res: Result<seq<bv8>, string>)
    decreases path
  {
    var isError, bytesRead, errorMsg := INTERNAL_ReadBytesFromFile(path);
    return if isError then Failure(errorMsg) else Success(bytesRead);
  }

  method WriteBytesToFile(path: string, bytes: seq<bv8>) returns (res: Result<(), string>)
    decreases path, bytes
  {
    var isError, errorMsg := INTERNAL_WriteBytesToFile(path, bytes);
    return if isError then Failure(errorMsg) else Success(());
  }

  method {:extern ""DafnyLibraries.FileIO"", ""INTERNAL_ReadBytesFromFile""} INTERNAL_ReadBytesFromFile(path: string)
      returns (isError: bool, bytesRead: seq<bv8>, errorMsg: string)
    decreases path

  method {:extern ""DafnyLibraries.FileIO"", ""INTERNAL_WriteBytesToFile""} INTERNAL_WriteBytesToFile(path: string, bytes: seq<bv8>)
      returns (isError: bool, errorMsg: string)
    decreases path, bytes
}

module {:options ""-functionSyntax:4""} UnicodeStrings refines AbstractUnicodeStrings {

  import Unicode

  import Utf8EncodingForm

  import Utf16EncodingForm
  predicate method IsWellFormedString(s: string)
    ensures |s| == 0 ==> IsWellFormedString(s)
    decreases s
  {
    Utf16EncodingForm.IsWellFormedCodeUnitSequence(Seq.Map((c: char) => c as Utf16EncodingForm.CodeUnit, s))
  }

  function method ToUTF8Checked(s: string): Option<seq<uint8>>
    decreases s
  {
    var asCodeUnits: seq<Utf16EncodingForm.CodeUnit> := Seq.Map((c: char) => c as Utf16EncodingForm.CodeUnit, s);
    var utf32: seq<Unicode.ScalarValue> :- Utf16EncodingForm.DecodeCodeUnitSequenceChecked(asCodeUnits); var asUtf8CodeUnits: WellFormedCodeUnitSeq := Utf8EncodingForm.EncodeScalarSequence(utf32); Some(Seq.Map((c: bv8) => c as byte, asUtf8CodeUnits))
  }

  function method {:vcs_split_on_every_assert} FromUTF8Checked(bs: seq<uint8>): Option<string>
    decreases bs
  {
    var asCodeUnits: seq<Utf8EncodingForm.CodeUnit> := Seq.Map((c: uint8) => c as Utf8EncodingForm.CodeUnit, bs);
    var utf32: seq<Unicode.ScalarValue> :- Utf8EncodingForm.DecodeCodeUnitSequenceChecked(asCodeUnits); var asUtf16CodeUnits: WellFormedCodeUnitSeq := Utf16EncodingForm.EncodeScalarSequence(utf32); Some(Seq.Map((cu: bv16) => cu as char, asUtf16CodeUnits))
  }

  function method ToUTF16Checked(s: string): Option<seq<uint16>>
    decreases s
  {
    if Utf16EncodingForm.IsWellFormedCodeUnitSequence(Seq.Map((c: char) => c as Utf16EncodingForm.CodeUnit, s)) then
      Some(Seq.Map((c: char) => c as uint16, s))
    else
      None
  }

  function method FromUTF16Checked(bs: seq<uint16>): Option<string>
    decreases bs
  {
    if Utf16EncodingForm.IsWellFormedCodeUnitSequence(Seq.Map((c: uint16) => c as Utf16EncodingForm.CodeUnit, bs)) then
      Some(Seq.Map((c: uint16) => c as char, bs))
    else
      None
  }

  function method ASCIIToUTF8(s: string): seq<uint8>
    requires forall i: int {:trigger s[i]} | 0 <= i < |s| :: 0 <= s[i] as int && s[i] as int < 128
    decreases s
  {
    Seq.Map((c: char) requires 0 <= c as int < 128 => c as uint8, s)
  }

  function method ASCIIToUTF16(s: string): seq<uint16>
    requires forall i: int {:trigger s[i]} | 0 <= i < |s| :: 0 <= s[i] as int && s[i] as int < 128
    decreases s
  {
    Seq.Map((c: char) requires 0 <= c as int < 128 => c as uint16, s)
  }

  import Seq

  import opened Wrappers

  import opened BoundedInts
}

abstract module {:options ""-functionSyntax:4""} AbstractUnicodeStrings {

  import Seq

  import opened Wrappers

  import opened BoundedInts
  function method ToUTF8Checked(s: string): Option<seq<uint8>>
    decreases s

  function method ASCIIToUTF8(s: string): seq<uint8>
    requires forall i: int {:trigger s[i]} | 0 <= i < |s| :: 0 <= s[i] as int && s[i] as int < 128
    decreases s
  {
    Seq.Map((c: char) requires 0 <= c as int < 128 => c as uint8, s)
  }

  function method FromUTF8Checked(bs: seq<uint8>): Option<string>
    decreases bs

  function method ToUTF16Checked(s: string): Option<seq<uint16>>
    decreases s

  function method ASCIIToUTF16(s: string): seq<uint16>
    requires forall i: int {:trigger s[i]} | 0 <= i < |s| :: 0 <= s[i] as int && s[i] as int < 128
    decreases s
  {
    Seq.Map((c: char) requires 0 <= c as int < 128 => c as uint16, s)
  }

  function method FromUTF16Checked(bs: seq<uint16>): Option<string>
    decreases bs
}

module {:options ""-functionSyntax:4""} Utf8EncodingForm refines UnicodeEncodingForm {
  type CodeUnit = bv8

  function method IsMinimalWellFormedCodeUnitSubsequence(s: CodeUnitSeq): (b: bool)
    ensures b ==> |s| > 0 && forall i: int {:trigger s[..i]} | 0 < i < |s| :: !IsMinimalWellFormedCodeUnitSubsequence(s[..i])
    decreases |s|
  {
    if |s| == 1 then
      var b: bool := IsWellFormedSingleCodeUnitSequence(s);
      assert b ==> forall i: int {:trigger s[..i]} | 0 < i < |s| :: !IsMinimalWellFormedCodeUnitSubsequence(s[..i]);
      b
    else if |s| == 2 then
      var b: bool := IsWellFormedDoubleCodeUnitSequence(s);
      assert b ==> forall i: int {:trigger s[..i]} | 0 < i < |s| :: !IsMinimalWellFormedCodeUnitSubsequence(s[..i]);
      b
    else if |s| == 3 then
      var b: bool := IsWellFormedTripleCodeUnitSequence(s);
      assert b ==> forall i: int {:trigger s[..i]} | 0 < i < |s| :: !IsMinimalWellFormedCodeUnitSubsequence(s[..i]);
      b
    else if |s| == 4 then
      var b: bool := IsWellFormedQuadrupleCodeUnitSequence(s);
      assert b ==> forall i: int {:trigger s[..i]} | 0 < i < |s| :: !IsMinimalWellFormedCodeUnitSubsequence(s[..i]);
      b
    else
      false
  }

  function method IsWellFormedSingleCodeUnitSequence(s: CodeUnitSeq): (b: bool)
    requires |s| == 1
    decreases s
  {
    var firstByte: bv8 := s[0];
    true &&
    0 <= firstByte <= 127
  }

  function method IsWellFormedDoubleCodeUnitSequence(s: CodeUnitSeq): (b: bool)
    requires |s| == 2
    ensures b ==> true && !IsWellFormedSingleCodeUnitSequence(s[..1])
    decreases s
  {
    var firstByte: bv8 := s[0];
    var secondByte: bv8 := s[1];
    194 <= firstByte <= 223 &&
    128 <= secondByte <= 191
  }

  function method IsWellFormedTripleCodeUnitSequence(s: CodeUnitSeq): (b: bool)
    requires |s| == 3
    ensures b ==> !IsWellFormedSingleCodeUnitSequence(s[..1]) && !IsWellFormedDoubleCodeUnitSequence(s[..2])
    decreases s
  {
    var firstByte: bv8 := s[0];
    var secondByte: bv8 := s[1];
    var thirdByte: bv8 := s[2];
    ((firstByte == 224 && 160 <= secondByte <= 191) || (225 <= firstByte <= 236 && 128 <= secondByte <= 191) || (firstByte == 237 && 128 <= secondByte <= 159) || (238 <= firstByte <= 239 && 128 <= secondByte <= 191)) &&
    128 <= thirdByte <= 191
  }

  function method IsWellFormedQuadrupleCodeUnitSequence(s: CodeUnitSeq): (b: bool)
    requires |s| == 4
    ensures b ==> !IsWellFormedSingleCodeUnitSequence(s[..1]) && !IsWellFormedDoubleCodeUnitSequence(s[..2]) && !IsWellFormedTripleCodeUnitSequence(s[..3])
    decreases s
  {
    var firstByte: bv8 := s[0];
    var secondByte: bv8 := s[1];
    var thirdByte: bv8 := s[2];
    var fourthByte: bv8 := s[3];
    ((firstByte == 240 && 144 <= secondByte <= 191) || (241 <= firstByte <= 243 && 128 <= secondByte <= 191) || (firstByte == 244 && 128 <= secondByte <= 143)) &&
    128 <= thirdByte <= 191 &&
    128 <= fourthByte <= 191
  }

  function method SplitPrefixMinimalWellFormedCodeUnitSubsequence(s: CodeUnitSeq): (maybePrefix: Option<MinimalWellFormedCodeUnitSeq>)
    ensures |s| == 0 ==> maybePrefix.None?
    ensures (exists i: int {:trigger s[..i]} | 0 < i <= |s| :: IsMinimalWellFormedCodeUnitSubsequence(s[..i])) <==> true && maybePrefix.Some?
    ensures maybePrefix.Some? ==> true && var prefix: MinimalWellFormedCodeUnitSeq := maybePrefix.Extract(); 0 < |prefix| <= |s| && prefix == s[..|prefix|] && forall i: int {:trigger s[..i]} | 0 < i < |prefix| :: !IsMinimalWellFormedCodeUnitSubsequence(s[..i])
    decreases s
  {
    if |s| >= 1 && IsWellFormedSingleCodeUnitSequence(s[..1]) then
      Some(s[..1])
    else if |s| >= 2 && IsWellFormedDoubleCodeUnitSequence(s[..2]) then
      Some(s[..2])
    else if |s| >= 3 && IsWellFormedTripleCodeUnitSequence(s[..3]) then
      Some(s[..3])
    else if |s| >= 4 && IsWellFormedQuadrupleCodeUnitSequence(s[..4]) then
      Some(s[..4])
    else
      None
  }

  function method EncodeScalarValue(v: Unicode.ScalarValue): (m: MinimalWellFormedCodeUnitSeq)
    decreases v
  {
    if v <= 127 then
      EncodeScalarValueSingleByte(v)
    else if v <= 2047 then
      EncodeScalarValueDoubleByte(v)
    else if v <= 65535 then
      EncodeScalarValueTripleByte(v)
    else
      EncodeScalarValueQuadrupleByte(v)
  }

  function method EncodeScalarValueSingleByte(v: Unicode.ScalarValue): (m: MinimalWellFormedCodeUnitSeq)
    requires 0 <= v <= 127
    ensures |m| == 1
    ensures IsWellFormedSingleCodeUnitSequence(m)
    decreases v
  {
    var x: bv7 := (v & 127) as bv7;
    var firstByte: CodeUnit := x as CodeUnit;
    [firstByte]
  }

  function method EncodeScalarValueDoubleByte(v: Unicode.ScalarValue): (s: CodeUnitSeq)
    requires 128 <= v <= 2047
    ensures |s| == 2
    ensures IsWellFormedDoubleCodeUnitSequence(s)
    decreases v
  {
    var x: bv6 := (v & 63) as bv6;
    var y: bv5 := (v & 1984 >> 6 as bv5) as bv5;
    var firstByte: bv8 := 192 | y as CodeUnit;
    var secondByte: bv8 := 128 | x as CodeUnit;
    [firstByte, secondByte]
  }

  function method EncodeScalarValueTripleByte(v: Unicode.ScalarValue): (s: CodeUnitSeq)
    requires 2048 <= v <= 65535
    ensures |s| == 3
    ensures IsWellFormedTripleCodeUnitSequence(s)
    decreases v
  {
    var x: bv6 := (v & 63) as bv6;
    var y: bv6 := (v & 4032 >> 6 as bv5) as bv6;
    var z: bv4 := (v & 61440 >> 12 as bv5) as bv4;
    var firstByte: bv8 := 224 | z as CodeUnit;
    var secondByte: bv8 := 128 | y as CodeUnit;
    var thirdByte: bv8 := 128 | x as CodeUnit;
    [firstByte, secondByte, thirdByte]
  }

  function method EncodeScalarValueQuadrupleByte(v: Unicode.ScalarValue): (s: CodeUnitSeq)
    requires 65536 <= v <= 1114111
    ensures |s| == 4
    ensures IsWellFormedQuadrupleCodeUnitSequence(s)
    decreases v
  {
    assert v <= 2097151;
    var x: bv6 := (v & 63) as bv6;
    var y: bv6 := (v & 4032 >> 6 as bv5) as bv6;
    var z: bv4 := (v & 61440 >> 12 as bv5) as bv4;
    var u2: bv2 := (v & 196608 >> 16 as bv5) as bv2;
    var u1: bv3 := (v & 1835008 >> 18 as bv5) as bv3;
    var firstByte: bv8 := 240 | u1 as CodeUnit;
    var secondByte: bv8 := 128 | (u2 as CodeUnit << 4 as bv4) | z as CodeUnit;
    var thirdByte: bv8 := 128 | y as CodeUnit;
    var fourthByte: bv8 := 128 | x as CodeUnit;
    [firstByte, secondByte, thirdByte, fourthByte]
  }

  function method DecodeMinimalWellFormedCodeUnitSubsequence(m: MinimalWellFormedCodeUnitSeq): (v: Unicode.ScalarValue)
    ensures EncodeScalarValue(v) == m
    decreases m
  {
    if |m| == 1 then
      DecodeMinimalWellFormedCodeUnitSubsequenceSingleByte(m)
    else if |m| == 2 then
      DecodeMinimalWellFormedCodeUnitSubsequenceDoubleByte(m)
    else if |m| == 3 then
      DecodeMinimalWellFormedCodeUnitSubsequenceTripleByte(m)
    else
      assert |m| == 4; DecodeMinimalWellFormedCodeUnitSubsequenceQuadrupleByte(m)
  }

  function method DecodeMinimalWellFormedCodeUnitSubsequenceSingleByte(m: MinimalWellFormedCodeUnitSeq): (v: Unicode.ScalarValue)
    requires |m| == 1
    ensures 0 <= v <= 127
    ensures EncodeScalarValueSingleByte(v) == m
    decreases m
  {
    var firstByte: bv8 := m[0];
    var x: bv7 := firstByte as bv7;
    x as Unicode.ScalarValue
  }

  function method DecodeMinimalWellFormedCodeUnitSubsequenceDoubleByte(m: MinimalWellFormedCodeUnitSeq): (v: Unicode.ScalarValue)
    requires |m| == 2
    ensures 128 <= v <= 2047
    ensures EncodeScalarValueDoubleByte(v) == m
    decreases m
  {
    var firstByte: bv8 := m[0];
    var secondByte: bv8 := m[1];
    var y: bv24 := (firstByte & 31) as bv24;
    var x: bv24 := (secondByte & 63) as bv24;
    (y << 6 as bv5) | x as Unicode.ScalarValue
  }

  function method DecodeMinimalWellFormedCodeUnitSubsequenceTripleByte(m: MinimalWellFormedCodeUnitSeq): (v: Unicode.ScalarValue)
    requires |m| == 3
    ensures 2048 <= v <= 65535
    ensures EncodeScalarValueTripleByte(v) == m
    decreases m
  {
    var firstByte: bv8 := m[0];
    var secondByte: bv8 := m[1];
    var thirdByte: bv8 := m[2];
    var z: bv24 := (firstByte & 15) as bv24;
    var y: bv24 := (secondByte & 63) as bv24;
    var x: bv24 := (thirdByte & 63) as bv24;
    assert {:split_here} true;
    (z << 12 as bv5) | (y << 6 as bv5) | x as Unicode.ScalarValue
  }

  function method DecodeMinimalWellFormedCodeUnitSubsequenceQuadrupleByte(m: MinimalWellFormedCodeUnitSeq): (v: Unicode.ScalarValue)
    requires |m| == 4
    ensures 65536 <= v <= 1114111
    ensures EncodeScalarValueQuadrupleByte(v) == m
    decreases m
  {
    var firstByte: bv8 := m[0];
    var secondByte: bv8 := m[1];
    var thirdByte: bv8 := m[2];
    var fourthByte: bv8 := m[3];
    var u1: bv24 := (firstByte & 7) as bv24;
    var u2: bv24 := (secondByte & 48 >> 4 as bv4) as bv24;
    var z: bv24 := (secondByte & 15) as bv24;
    var y: bv24 := (thirdByte & 63) as bv24;
    var x: bv24 := (fourthByte & 63) as bv24;
    assert {:split_here} true;
    (u1 << 18 as bv5) | (u2 << 16 as bv5) | (z << 12 as bv5) | (y << 6 as bv5) | x as Unicode.ScalarValue
  }

  lemma LemmaSplitPrefixMinimalWellFormedCodeUnitSubsequenceInvertsPrepend(m: MinimalWellFormedCodeUnitSeq, s: CodeUnitSeq)
    ensures SplitPrefixMinimalWellFormedCodeUnitSubsequence(m + s) == Some(m)
    decreases m, s
  {
    ghost var ms := m + s;
    assert IsMinimalWellFormedCodeUnitSubsequence(ms[..|m|]);
    ghost var prefix := SplitPrefixMinimalWellFormedCodeUnitSubsequence(ms).Extract();
    calc ==> {
      IsMinimalWellFormedCodeUnitSubsequence(m);
      |prefix| <= |m|;
      prefix == ms[..|prefix|] == m[..|prefix|] == m;
    }
  }

  function PartitionCodeUnitSequenceChecked(s: CodeUnitSeq): (maybeParts: Option<seq<MinimalWellFormedCodeUnitSeq>>)
    ensures maybeParts.Some? ==> Seq.Flatten(maybeParts.Extract()) == s
    decreases |s|
  {
    if s == [] then
      Some([])
    else
      var prefix: MinimalWellFormedCodeUnitSeq :- SplitPrefixMinimalWellFormedCodeUnitSubsequence(s); var restParts: seq<MinimalWellFormedCodeUnitSeq> :- PartitionCodeUnitSequenceChecked(s[|prefix|..]); Some([prefix] + restParts)
  } by method {
    if s == [] {
      return Some([]);
    }
    var result: seq<MinimalWellFormedCodeUnitSeq> := [];
    var rest := s;
    while |rest| > 0
      invariant PartitionCodeUnitSequenceChecked(s).Some? <==> PartitionCodeUnitSequenceChecked(rest).Some?
      invariant PartitionCodeUnitSequenceChecked(s).Some? ==> true && PartitionCodeUnitSequenceChecked(s).value == result + PartitionCodeUnitSequenceChecked(rest).value
      decreases |rest| - 0
    {
      var prefix :- SplitPrefixMinimalWellFormedCodeUnitSubsequence(rest);
      result := result + [prefix];
      rest := rest[|prefix|..];
    }
    assert result + [] == result;
    return Some(result);
  }

  function method PartitionCodeUnitSequence(s: WellFormedCodeUnitSeq): (parts: seq<MinimalWellFormedCodeUnitSeq>)
    ensures Seq.Flatten(parts) == s
    decreases s
  {
    PartitionCodeUnitSequenceChecked(s).Extract()
  }

  lemma /*{:_induction m}*/ LemmaPartitionMinimalWellFormedCodeUnitSubsequence(m: MinimalWellFormedCodeUnitSeq)
    ensures PartitionCodeUnitSequenceChecked(m) == Some([m])
    decreases m
  {
    LemmaSplitPrefixMinimalWellFormedCodeUnitSubsequenceInvertsPrepend(m, []);
    calc == {
      Some(m);
      SplitPrefixMinimalWellFormedCodeUnitSubsequence(m + []);
      {
        assert m + [] == m;
      }
      SplitPrefixMinimalWellFormedCodeUnitSubsequence(m);
    }
    calc == {
      PartitionCodeUnitSequenceChecked(m);
      Some([m] + []);
      {
        assert [m] + [] == [m];
      }
      Some([m]);
    }
  }

  function method IsWellFormedCodeUnitSequence(s: CodeUnitSeq): (b: bool)
    decreases s
  {
    PartitionCodeUnitSequenceChecked(s).Some?
  }

  lemma LemmaMinimalWellFormedCodeUnitSubsequenceIsWellFormedSequence(m: MinimalWellFormedCodeUnitSeq)
    ensures IsWellFormedCodeUnitSequence(m)
    decreases m
  {
    LemmaPartitionMinimalWellFormedCodeUnitSubsequence(m);
  }

  lemma LemmaPrependMinimalWellFormedCodeUnitSubsequence(m: MinimalWellFormedCodeUnitSeq, s: WellFormedCodeUnitSeq)
    ensures IsWellFormedCodeUnitSequence(m + s)
    decreases m, s
  {
    LemmaPartitionMinimalWellFormedCodeUnitSubsequence(m);
    LemmaSplitPrefixMinimalWellFormedCodeUnitSubsequenceInvertsPrepend(m, s);
    assert PartitionCodeUnitSequenceChecked(m + s).Some?;
  }

  lemma /*{:_induction ms}*/ LemmaFlattenMinimalWellFormedCodeUnitSubsequences(ms: seq<MinimalWellFormedCodeUnitSeq>)
    ensures IsWellFormedCodeUnitSequence(Seq.Flatten(ms))
    decreases ms
  {
    if |ms| == 0 {
      assert IsWellFormedCodeUnitSequence(Seq.Flatten(ms));
    } else {
      ghost var head := ms[0];
      ghost var tail := ms[1..];
      LemmaFlattenMinimalWellFormedCodeUnitSubsequences(tail);
      ghost var flatTail := Seq.Flatten(tail);
      LemmaPrependMinimalWellFormedCodeUnitSubsequence(head, flatTail);
      assert IsWellFormedCodeUnitSequence(head + flatTail);
    }
  }

  lemma LemmaConcatWellFormedCodeUnitSubsequences(s: WellFormedCodeUnitSeq, t: WellFormedCodeUnitSeq)
    ensures IsWellFormedCodeUnitSequence(s + t)
    decreases s, t
  {
    ghost var partsS := PartitionCodeUnitSequence(s);
    ghost var partsT := PartitionCodeUnitSequence(t);
    ghost var partsST := partsS + partsT;
    Seq.LemmaFlattenConcat(partsS, partsT);
    assert s + t == Seq.Flatten(partsST);
    assert forall part: CodeUnitSeq {:trigger IsMinimalWellFormedCodeUnitSubsequence(part)} {:trigger |part|} {:trigger part in partsST} | part in partsST :: |part| > 0 && IsMinimalWellFormedCodeUnitSubsequence(part);
    LemmaFlattenMinimalWellFormedCodeUnitSubsequences(partsST);
  }

  function EncodeScalarSequence(vs: seq<Unicode.ScalarValue>): (s: WellFormedCodeUnitSeq)
    decreases vs
  {
    var ms: seq<MinimalWellFormedCodeUnitSeq> := Seq.Map(EncodeScalarValue, vs);
    LemmaFlattenMinimalWellFormedCodeUnitSubsequences(ms);
    Seq.Flatten(ms)
  } by method {
    s := [];
    ghost var unflattened: seq<MinimalWellFormedCodeUnitSeq> := [];
    for i: int := |vs| downto 0
      invariant unflattened == Seq.Map(EncodeScalarValue, vs[i..])
      invariant s == Seq.Flatten(unflattened)
    {
      var next: MinimalWellFormedCodeUnitSeq := EncodeScalarValue(vs[i]);
      unflattened := [next] + unflattened;
      LemmaPrependMinimalWellFormedCodeUnitSubsequence(next, s);
      s := next + s;
    }
  }

  function method DecodeCodeUnitSequence(s: WellFormedCodeUnitSeq): (vs: seq<Unicode.ScalarValue>)
    ensures EncodeScalarSequence(vs) == s
    decreases s
  {
    var parts: seq<MinimalWellFormedCodeUnitSeq> := PartitionCodeUnitSequence(s);
    var vs: seq<Unicode.ScalarValue> := Seq.Map(DecodeMinimalWellFormedCodeUnitSubsequence, parts);
    calc == {
      s;
      Seq.Flatten(parts);
      {
        assert parts == Seq.Map(EncodeScalarValue, vs);
      }
      Seq.Flatten(Seq.Map(EncodeScalarValue, vs));
      EncodeScalarSequence(vs);
    }
    vs
  }

  function DecodeCodeUnitSequenceChecked(s: CodeUnitSeq): (maybeVs: Option<seq<Unicode.ScalarValue>>)
    ensures IsWellFormedCodeUnitSequence(s) ==> maybeVs.Some? && maybeVs.Extract() == DecodeCodeUnitSequence(s)
    ensures !IsWellFormedCodeUnitSequence(s) ==> true && maybeVs.None?
    decreases s
  {
    if IsWellFormedCodeUnitSequence(s) then
      Some(DecodeCodeUnitSequence(s))
    else
      None
  } by method {
    var maybeParts := PartitionCodeUnitSequenceChecked(s);
    if maybeParts.None? {
      return None;
    }
    var parts := maybeParts.value;
    var vs := Seq.Map(DecodeMinimalWellFormedCodeUnitSubsequence, parts);
    calc == {
      s;
      Seq.Flatten(parts);
      {
        assert parts == Seq.Map(EncodeScalarValue, vs);
      }
      Seq.Flatten(Seq.Map(EncodeScalarValue, vs));
      EncodeScalarSequence(vs);
    }
    return Some(vs);
  }

  import opened Wrappers

  import Functions

  import Seq

  import Unicode

  type CodeUnitSeq = seq<CodeUnit>

  type WellFormedCodeUnitSeq = s: CodeUnitSeq
    | IsWellFormedCodeUnitSequence(s)
    witness []

  type MinimalWellFormedCodeUnitSeq = s: CodeUnitSeq
    | IsMinimalWellFormedCodeUnitSubsequence(s)
    witness *
}

module {:options ""-functionSyntax:4""} Functions {
  predicate Injective<X(!new), Y>(f: X --> Y)
    requires forall x: X {:trigger f.requires(x)} :: f.requires(x)
    reads set _x0: X, _obj: object? /*{:_reads}*/ {:trigger _obj in f.reads(_x0)} | _obj in f.reads(_x0) :: _obj
    decreases set _x0: X, _obj: object? /*{:_reads}*/ {:trigger _obj in f.reads(_x0)} | _obj in f.reads(_x0) :: _obj
  {
    forall x1: X, x2: X {:trigger f(x2), f(x1)} :: 
      f(x1) == f(x2) ==>
        x1 == x2
  }
}

module {:options ""-functionSyntax:4""} Unicode {

  import opened Wrappers

  import Seq
  type CodePoint = i: bv24
    | 0 <= i <= 1114111

  type HighSurrogateCodePoint = p: CodePoint
    | HIGH_SURROGATE_MIN <= p <= HIGH_SURROGATE_MAX
    witness HIGH_SURROGATE_MIN

  type LowSurrogateCodePoint = p: CodePoint
    | LOW_SURROGATE_MIN <= p <= LOW_SURROGATE_MAX
    witness LOW_SURROGATE_MIN

  type ScalarValue = p: CodePoint
    | (p < HIGH_SURROGATE_MIN || p > HIGH_SURROGATE_MAX) && (p < LOW_SURROGATE_MIN || p > LOW_SURROGATE_MAX)

  type AssignedCodePoint = p: CodePoint
    | IsInAssignedPlane(p)
    witness *

  const HIGH_SURROGATE_MIN: CodePoint := 55296
  const HIGH_SURROGATE_MAX: CodePoint := 56319
  const LOW_SURROGATE_MIN: CodePoint := 56320
  const LOW_SURROGATE_MAX: CodePoint := 57343
  const ASSIGNED_PLANES: set<bv8> := {0, 1, 2, 3, 14, 15, 16}

  predicate {:opaque} {:fuel 0, 0} IsInAssignedPlane(i: CodePoint)
    decreases i
  {
    ghost var plane: bv8 := (i >> 16 as bv5) as bv8;
    plane in ASSIGNED_PLANES
  }
}

abstract module {:options ""-functionSyntax:4""} UnicodeEncodingForm {

  import opened Wrappers

  import Functions

  import Seq

  import Unicode
  type CodeUnitSeq = seq<CodeUnit>

  type WellFormedCodeUnitSeq = s: CodeUnitSeq
    | IsWellFormedCodeUnitSequence(s)
    witness []

  type MinimalWellFormedCodeUnitSeq = s: CodeUnitSeq
    | IsMinimalWellFormedCodeUnitSubsequence(s)
    witness *

  type CodeUnit

  function method IsMinimalWellFormedCodeUnitSubsequence(s: CodeUnitSeq): (b: bool)
    ensures b ==> |s| > 0 && forall i: int {:trigger s[..i]} | 0 < i < |s| :: !IsMinimalWellFormedCodeUnitSubsequence(s[..i])
    decreases |s|

  function method SplitPrefixMinimalWellFormedCodeUnitSubsequence(s: CodeUnitSeq): (maybePrefix: Option<MinimalWellFormedCodeUnitSeq>)
    ensures |s| == 0 ==> maybePrefix.None?
    ensures (exists i: int {:trigger s[..i]} | 0 < i <= |s| :: IsMinimalWellFormedCodeUnitSubsequence(s[..i])) <==> true && maybePrefix.Some?
    ensures maybePrefix.Some? ==> true && var prefix: MinimalWellFormedCodeUnitSeq := maybePrefix.Extract(); 0 < |prefix| <= |s| && prefix == s[..|prefix|] && forall i: int {:trigger s[..i]} | 0 < i < |prefix| :: !IsMinimalWellFormedCodeUnitSubsequence(s[..i])
    decreases s

  function method EncodeScalarValue(v: Unicode.ScalarValue): (m: MinimalWellFormedCodeUnitSeq)
    decreases v

  function method DecodeMinimalWellFormedCodeUnitSubsequence(m: MinimalWellFormedCodeUnitSeq): (v: Unicode.ScalarValue)
    ensures EncodeScalarValue(v) == m
    decreases m

  lemma LemmaSplitPrefixMinimalWellFormedCodeUnitSubsequenceInvertsPrepend(m: MinimalWellFormedCodeUnitSeq, s: CodeUnitSeq)
    ensures SplitPrefixMinimalWellFormedCodeUnitSubsequence(m + s) == Some(m)
    decreases m, s
  {
  }

  function PartitionCodeUnitSequenceChecked(s: CodeUnitSeq): (maybeParts: Option<seq<MinimalWellFormedCodeUnitSeq>>)
    ensures maybeParts.Some? ==> Seq.Flatten(maybeParts.Extract()) == s
    decreases |s|
  {
    if s == [] then
      Some([])
    else
      var prefix: MinimalWellFormedCodeUnitSeq :- SplitPrefixMinimalWellFormedCodeUnitSubsequence(s); var restParts: seq<MinimalWellFormedCodeUnitSeq> :- PartitionCodeUnitSequenceChecked(s[|prefix|..]); Some([prefix] + restParts)
  } by method {
    if s == [] {
      return Some([]);
    }
    var result: seq<MinimalWellFormedCodeUnitSeq> := [];
    var rest := s;
    while |rest| > 0
      invariant PartitionCodeUnitSequenceChecked(s).Some? <==> PartitionCodeUnitSequenceChecked(rest).Some?
      invariant PartitionCodeUnitSequenceChecked(s).Some? ==> true && PartitionCodeUnitSequenceChecked(s).value == result + PartitionCodeUnitSequenceChecked(rest).value
      decreases |rest| - 0
    {
      var prefix :- SplitPrefixMinimalWellFormedCodeUnitSubsequence(rest);
      result := result + [prefix];
      rest := rest[|prefix|..];
    }
    assert result + [] == result;
    return Some(result);
  }

  function method PartitionCodeUnitSequence(s: WellFormedCodeUnitSeq): (parts: seq<MinimalWellFormedCodeUnitSeq>)
    ensures Seq.Flatten(parts) == s
    decreases s
  {
    PartitionCodeUnitSequenceChecked(s).Extract()
  }

  lemma /*{:_induction m}*/ LemmaPartitionMinimalWellFormedCodeUnitSubsequence(m: MinimalWellFormedCodeUnitSeq)
    ensures PartitionCodeUnitSequenceChecked(m) == Some([m])
    decreases m
  {
  }

  function method IsWellFormedCodeUnitSequence(s: CodeUnitSeq): (b: bool)
    decreases s
  {
    PartitionCodeUnitSequenceChecked(s).Some?
  }

  lemma LemmaMinimalWellFormedCodeUnitSubsequenceIsWellFormedSequence(m: MinimalWellFormedCodeUnitSeq)
    ensures IsWellFormedCodeUnitSequence(m)
    decreases m
  {
  }

  lemma LemmaPrependMinimalWellFormedCodeUnitSubsequence(m: MinimalWellFormedCodeUnitSeq, s: WellFormedCodeUnitSeq)
    ensures IsWellFormedCodeUnitSequence(m + s)
    decreases m, s
  {
  }

  lemma /*{:_induction ms}*/ LemmaFlattenMinimalWellFormedCodeUnitSubsequences(ms: seq<MinimalWellFormedCodeUnitSeq>)
    ensures IsWellFormedCodeUnitSequence(Seq.Flatten(ms))
    decreases ms
  {
  }

  lemma LemmaConcatWellFormedCodeUnitSubsequences(s: WellFormedCodeUnitSeq, t: WellFormedCodeUnitSeq)
    ensures IsWellFormedCodeUnitSequence(s + t)
    decreases s, t
  {
  }

  function EncodeScalarSequence(vs: seq<Unicode.ScalarValue>): (s: WellFormedCodeUnitSeq)
    decreases vs
  {
    var ms: seq<MinimalWellFormedCodeUnitSeq> := Seq.Map(EncodeScalarValue, vs);
    LemmaFlattenMinimalWellFormedCodeUnitSubsequences(ms);
    Seq.Flatten(ms)
  } by method {
    s := [];
    ghost var unflattened: seq<MinimalWellFormedCodeUnitSeq> := [];
    for i: int := |vs| downto 0
      invariant unflattened == Seq.Map(EncodeScalarValue, vs[i..])
      invariant s == Seq.Flatten(unflattened)
    {
      var next: MinimalWellFormedCodeUnitSeq := EncodeScalarValue(vs[i]);
      unflattened := [next] + unflattened;
      LemmaPrependMinimalWellFormedCodeUnitSubsequence(next, s);
      s := next + s;
    }
  }

  function method DecodeCodeUnitSequence(s: WellFormedCodeUnitSeq): (vs: seq<Unicode.ScalarValue>)
    ensures EncodeScalarSequence(vs) == s
    decreases s
  {
    var parts: seq<MinimalWellFormedCodeUnitSeq> := PartitionCodeUnitSequence(s);
    var vs: seq<Unicode.ScalarValue> := Seq.Map(DecodeMinimalWellFormedCodeUnitSubsequence, parts);
    calc == {
      s;
      Seq.Flatten(parts);
      {
        assert parts == Seq.Map(EncodeScalarValue, vs);
      }
      Seq.Flatten(Seq.Map(EncodeScalarValue, vs));
      EncodeScalarSequence(vs);
    }
    vs
  }

  function DecodeCodeUnitSequenceChecked(s: CodeUnitSeq): (maybeVs: Option<seq<Unicode.ScalarValue>>)
    ensures IsWellFormedCodeUnitSequence(s) ==> maybeVs.Some? && maybeVs.Extract() == DecodeCodeUnitSequence(s)
    ensures !IsWellFormedCodeUnitSequence(s) ==> true && maybeVs.None?
    decreases s
  {
    if IsWellFormedCodeUnitSequence(s) then
      Some(DecodeCodeUnitSequence(s))
    else
      None
  } by method {
    var maybeParts := PartitionCodeUnitSequenceChecked(s);
    if maybeParts.None? {
      return None;
    }
    var parts := maybeParts.value;
    var vs := Seq.Map(DecodeMinimalWellFormedCodeUnitSubsequence, parts);
    calc == {
      s;
      Seq.Flatten(parts);
      {
        assert parts == Seq.Map(EncodeScalarValue, vs);
      }
      Seq.Flatten(Seq.Map(EncodeScalarValue, vs));
      EncodeScalarSequence(vs);
    }
    return Some(vs);
  }
}

module {:options ""-functionSyntax:4""} Utf16EncodingForm refines UnicodeEncodingForm {
  type CodeUnit = bv16

  function method IsMinimalWellFormedCodeUnitSubsequence(s: CodeUnitSeq): (b: bool)
    ensures b ==> |s| > 0 && forall i: int {:trigger s[..i]} | 0 < i < |s| :: !IsMinimalWellFormedCodeUnitSubsequence(s[..i])
    decreases |s|
  {
    if |s| == 1 then
      IsWellFormedSingleCodeUnitSequence(s)
    else if |s| == 2 then
      var b: bool := IsWellFormedDoubleCodeUnitSequence(s);
      assert b ==> forall i: int {:trigger s[..i]} | 0 < i < |s| :: !IsMinimalWellFormedCodeUnitSubsequence(s[..i]);
      b
    else
      false
  }

  function method IsWellFormedSingleCodeUnitSequence(s: CodeUnitSeq): (b: bool)
    requires |s| == 1
    decreases s
  {
    var firstWord: bv16 := s[0];
    0 <= firstWord <= 55295 || 57344 <= firstWord <= 65535
  }

  function method IsWellFormedDoubleCodeUnitSequence(s: CodeUnitSeq): (b: bool)
    requires |s| == 2
    ensures b ==> !IsWellFormedSingleCodeUnitSequence(s[..1])
    decreases s
  {
    var firstWord: bv16 := s[0];
    var secondWord: bv16 := s[1];
    55296 <= firstWord <= 56319 &&
    56320 <= secondWord <= 57343
  }

  function method SplitPrefixMinimalWellFormedCodeUnitSubsequence(s: CodeUnitSeq): (maybePrefix: Option<MinimalWellFormedCodeUnitSeq>)
    ensures |s| == 0 ==> maybePrefix.None?
    ensures (exists i: int {:trigger s[..i]} | 0 < i <= |s| :: IsMinimalWellFormedCodeUnitSubsequence(s[..i])) <==> true && maybePrefix.Some?
    ensures maybePrefix.Some? ==> true && var prefix: MinimalWellFormedCodeUnitSeq := maybePrefix.Extract(); 0 < |prefix| <= |s| && prefix == s[..|prefix|] && forall i: int {:trigger s[..i]} | 0 < i < |prefix| :: !IsMinimalWellFormedCodeUnitSubsequence(s[..i])
    ensures |s| == 0 ==> maybePrefix.None?
    ensures (exists i: int {:trigger s[..i]} | 0 < i <= |s| :: IsMinimalWellFormedCodeUnitSubsequence(s[..i])) <==> true && maybePrefix.Some?
    ensures maybePrefix.Some? ==> true && var prefix: MinimalWellFormedCodeUnitSeq := maybePrefix.Extract(); 0 < |prefix| <= |s| && prefix == s[..|prefix|] && IsMinimalWellFormedCodeUnitSubsequence(prefix)
    decreases s
  {
    if |s| >= 1 && IsWellFormedSingleCodeUnitSequence(s[..1]) then
      Some(s[..1])
    else if |s| >= 2 && IsWellFormedDoubleCodeUnitSequence(s[..2]) then
      Some(s[..2])
    else
      None
  }

  function method EncodeScalarValue(v: Unicode.ScalarValue): (m: MinimalWellFormedCodeUnitSeq)
    decreases v
  {
    if 0 <= v <= 55295 || 57344 <= v <= 65535 then
      EncodeScalarValueSingleWord(v)
    else
      EncodeScalarValueDoubleWord(v)
  }

  function method EncodeScalarValueSingleWord(v: Unicode.ScalarValue): (m: MinimalWellFormedCodeUnitSeq)
    requires 0 <= v <= 55295 || 57344 <= v <= 65535
    ensures |m| == 1
    ensures IsWellFormedSingleCodeUnitSequence(m)
    decreases v
  {
    var firstWord: CodeUnit := v as CodeUnit;
    [firstWord]
  }

  function method EncodeScalarValueDoubleWord(v: Unicode.ScalarValue): (m: MinimalWellFormedCodeUnitSeq)
    requires 65536 <= v <= 1114111
    ensures |m| == 2
    ensures IsWellFormedDoubleCodeUnitSequence(m)
    decreases v
  {
    var x2: bv10 := (v & 1023) as bv10;
    var x1: bv6 := (v & 64512 >> 10 as bv5) as bv6;
    var u: bv5 := (v & 2031616 >> 16 as bv5) as bv5;
    var w: bv4 := (u - 1) as bv4;
    var firstWord: bv16 := 55296 | (w as CodeUnit << 6 as bv5) | x1 as CodeUnit;
    var secondWord: bv16 := 56320 | x2 as CodeUnit;
    [firstWord, secondWord]
  }

  function method DecodeMinimalWellFormedCodeUnitSubsequence(m: MinimalWellFormedCodeUnitSeq): (v: Unicode.ScalarValue)
    ensures EncodeScalarValue(v) == m
    decreases m
  {
    if |m| == 1 then
      DecodeMinimalWellFormedCodeUnitSubsequenceSingleWord(m)
    else
      assert |m| == 2; DecodeMinimalWellFormedCodeUnitSubsequenceDoubleWord(m)
  }

  function method DecodeMinimalWellFormedCodeUnitSubsequenceSingleWord(m: MinimalWellFormedCodeUnitSeq): (v: Unicode.ScalarValue)
    requires |m| == 1
    ensures 0 <= v <= 55295 || 57344 <= v <= 65535
    ensures EncodeScalarValueSingleWord(v) == m
    decreases m
  {
    var firstWord: bv16 := m[0];
    var x: bv16 := firstWord as bv16;
    assert EncodeScalarValueSingleWord(x as Unicode.ScalarValue) == m;
    x as Unicode.ScalarValue
  }

  function method DecodeMinimalWellFormedCodeUnitSubsequenceDoubleWord(m: MinimalWellFormedCodeUnitSeq): (v: Unicode.ScalarValue)
    requires |m| == 2
    ensures 65536 <= v <= 1114111
    ensures EncodeScalarValueDoubleWord(v) == m
    decreases m
  {
    var firstWord: bv16 := m[0];
    var secondWord: bv16 := m[1];
    var x2: bv24 := (secondWord & 1023) as bv24;
    var x1: bv24 := (firstWord & 63) as bv24;
    var w: bv24 := (firstWord & 960 >> 6 as bv5) as bv24;
    var u: bv24 := (w + 1) as bv24;
    var v: bv24 := (u << 16 as bv5) | (x1 << 10 as bv5) | x2 as Unicode.ScalarValue;
    assert {:split_here} true;
    assert EncodeScalarValueDoubleWord(v) == m;
    v
  }

  lemma LemmaSplitPrefixMinimalWellFormedCodeUnitSubsequenceInvertsPrepend(m: MinimalWellFormedCodeUnitSeq, s: CodeUnitSeq)
    ensures SplitPrefixMinimalWellFormedCodeUnitSubsequence(m + s) == Some(m)
    decreases m, s
  {
    ghost var ms := m + s;
    assert IsMinimalWellFormedCodeUnitSubsequence(ms[..|m|]);
    ghost var prefix := SplitPrefixMinimalWellFormedCodeUnitSubsequence(ms).Extract();
    calc ==> {
      IsMinimalWellFormedCodeUnitSubsequence(m);
      |prefix| <= |m|;
      prefix == ms[..|prefix|] == m[..|prefix|] == m;
    }
  }

  function PartitionCodeUnitSequenceChecked(s: CodeUnitSeq): (maybeParts: Option<seq<MinimalWellFormedCodeUnitSeq>>)
    ensures maybeParts.Some? ==> Seq.Flatten(maybeParts.Extract()) == s
    decreases |s|
  {
    if s == [] then
      Some([])
    else
      var prefix: MinimalWellFormedCodeUnitSeq :- SplitPrefixMinimalWellFormedCodeUnitSubsequence(s); var restParts: seq<MinimalWellFormedCodeUnitSeq> :- PartitionCodeUnitSequenceChecked(s[|prefix|..]); Some([prefix] + restParts)
  } by method {
    if s == [] {
      return Some([]);
    }
    var result: seq<MinimalWellFormedCodeUnitSeq> := [];
    var rest := s;
    while |rest| > 0
      invariant PartitionCodeUnitSequenceChecked(s).Some? <==> PartitionCodeUnitSequenceChecked(rest).Some?
      invariant PartitionCodeUnitSequenceChecked(s).Some? ==> true && PartitionCodeUnitSequenceChecked(s).value == result + PartitionCodeUnitSequenceChecked(rest).value
      decreases |rest| - 0
    {
      var prefix :- SplitPrefixMinimalWellFormedCodeUnitSubsequence(rest);
      result := result + [prefix];
      rest := rest[|prefix|..];
    }
    assert result + [] == result;
    return Some(result);
  }

  function method PartitionCodeUnitSequence(s: WellFormedCodeUnitSeq): (parts: seq<MinimalWellFormedCodeUnitSeq>)
    ensures Seq.Flatten(parts) == s
    decreases s
  {
    PartitionCodeUnitSequenceChecked(s).Extract()
  }

  lemma /*{:_induction m}*/ LemmaPartitionMinimalWellFormedCodeUnitSubsequence(m: MinimalWellFormedCodeUnitSeq)
    ensures PartitionCodeUnitSequenceChecked(m) == Some([m])
    decreases m
  {
    LemmaSplitPrefixMinimalWellFormedCodeUnitSubsequenceInvertsPrepend(m, []);
    calc == {
      Some(m);
      SplitPrefixMinimalWellFormedCodeUnitSubsequence(m + []);
      {
        assert m + [] == m;
      }
      SplitPrefixMinimalWellFormedCodeUnitSubsequence(m);
    }
    calc == {
      PartitionCodeUnitSequenceChecked(m);
      Some([m] + []);
      {
        assert [m] + [] == [m];
      }
      Some([m]);
    }
  }

  function method IsWellFormedCodeUnitSequence(s: CodeUnitSeq): (b: bool)
    decreases s
  {
    PartitionCodeUnitSequenceChecked(s).Some?
  }

  lemma LemmaMinimalWellFormedCodeUnitSubsequenceIsWellFormedSequence(m: MinimalWellFormedCodeUnitSeq)
    ensures IsWellFormedCodeUnitSequence(m)
    decreases m
  {
    LemmaPartitionMinimalWellFormedCodeUnitSubsequence(m);
  }

  lemma LemmaPrependMinimalWellFormedCodeUnitSubsequence(m: MinimalWellFormedCodeUnitSeq, s: WellFormedCodeUnitSeq)
    ensures IsWellFormedCodeUnitSequence(m + s)
    decreases m, s
  {
    LemmaPartitionMinimalWellFormedCodeUnitSubsequence(m);
    LemmaSplitPrefixMinimalWellFormedCodeUnitSubsequenceInvertsPrepend(m, s);
    assert PartitionCodeUnitSequenceChecked(m + s).Some?;
  }

  lemma /*{:_induction ms}*/ LemmaFlattenMinimalWellFormedCodeUnitSubsequences(ms: seq<MinimalWellFormedCodeUnitSeq>)
    ensures IsWellFormedCodeUnitSequence(Seq.Flatten(ms))
    decreases ms
  {
    if |ms| == 0 {
      assert IsWellFormedCodeUnitSequence(Seq.Flatten(ms));
    } else {
      ghost var head := ms[0];
      ghost var tail := ms[1..];
      LemmaFlattenMinimalWellFormedCodeUnitSubsequences(tail);
      ghost var flatTail := Seq.Flatten(tail);
      LemmaPrependMinimalWellFormedCodeUnitSubsequence(head, flatTail);
      assert IsWellFormedCodeUnitSequence(head + flatTail);
    }
  }

  lemma LemmaConcatWellFormedCodeUnitSubsequences(s: WellFormedCodeUnitSeq, t: WellFormedCodeUnitSeq)
    ensures IsWellFormedCodeUnitSequence(s + t)
    decreases s, t
  {
    ghost var partsS := PartitionCodeUnitSequence(s);
    ghost var partsT := PartitionCodeUnitSequence(t);
    ghost var partsST := partsS + partsT;
    Seq.LemmaFlattenConcat(partsS, partsT);
    assert s + t == Seq.Flatten(partsST);
    assert forall part: CodeUnitSeq {:trigger IsMinimalWellFormedCodeUnitSubsequence(part)} {:trigger |part|} {:trigger part in partsST} | part in partsST :: |part| > 0 && IsMinimalWellFormedCodeUnitSubsequence(part);
    LemmaFlattenMinimalWellFormedCodeUnitSubsequences(partsST);
  }

  function EncodeScalarSequence(vs: seq<Unicode.ScalarValue>): (s: WellFormedCodeUnitSeq)
    decreases vs
  {
    var ms: seq<MinimalWellFormedCodeUnitSeq> := Seq.Map(EncodeScalarValue, vs);
    LemmaFlattenMinimalWellFormedCodeUnitSubsequences(ms);
    Seq.Flatten(ms)
  } by method {
    s := [];
    ghost var unflattened: seq<MinimalWellFormedCodeUnitSeq> := [];
    for i: int := |vs| downto 0
      invariant unflattened == Seq.Map(EncodeScalarValue, vs[i..])
      invariant s == Seq.Flatten(unflattened)
    {
      var next: MinimalWellFormedCodeUnitSeq := EncodeScalarValue(vs[i]);
      unflattened := [next] + unflattened;
      LemmaPrependMinimalWellFormedCodeUnitSubsequence(next, s);
      s := next + s;
    }
  }

  function method DecodeCodeUnitSequence(s: WellFormedCodeUnitSeq): (vs: seq<Unicode.ScalarValue>)
    ensures EncodeScalarSequence(vs) == s
    decreases s
  {
    var parts: seq<MinimalWellFormedCodeUnitSeq> := PartitionCodeUnitSequence(s);
    var vs: seq<Unicode.ScalarValue> := Seq.Map(DecodeMinimalWellFormedCodeUnitSubsequence, parts);
    calc == {
      s;
      Seq.Flatten(parts);
      {
        assert parts == Seq.Map(EncodeScalarValue, vs);
      }
      Seq.Flatten(Seq.Map(EncodeScalarValue, vs));
      EncodeScalarSequence(vs);
    }
    vs
  }

  function DecodeCodeUnitSequenceChecked(s: CodeUnitSeq): (maybeVs: Option<seq<Unicode.ScalarValue>>)
    ensures IsWellFormedCodeUnitSequence(s) ==> maybeVs.Some? && maybeVs.Extract() == DecodeCodeUnitSequence(s)
    ensures !IsWellFormedCodeUnitSequence(s) ==> true && maybeVs.None?
    decreases s
  {
    if IsWellFormedCodeUnitSequence(s) then
      Some(DecodeCodeUnitSequence(s))
    else
      None
  } by method {
    var maybeParts := PartitionCodeUnitSequenceChecked(s);
    if maybeParts.None? {
      return None;
    }
    var parts := maybeParts.value;
    var vs := Seq.Map(DecodeMinimalWellFormedCodeUnitSubsequence, parts);
    calc == {
      s;
      Seq.Flatten(parts);
      {
        assert parts == Seq.Map(EncodeScalarValue, vs);
      }
      Seq.Flatten(Seq.Map(EncodeScalarValue, vs));
      EncodeScalarSequence(vs);
    }
    return Some(vs);
  }

  import opened Wrappers

  import Functions

  import Seq

  import Unicode

  type CodeUnitSeq = seq<CodeUnit>

  type WellFormedCodeUnitSeq = s: CodeUnitSeq
    | IsWellFormedCodeUnitSequence(s)
    witness []

  type MinimalWellFormedCodeUnitSeq = s: CodeUnitSeq
    | IsMinimalWellFormedCodeUnitSubsequence(s)
    witness *
}

module JSON {

  module {:options ""-functionSyntax:4""} API {

    import opened BoundedInts

    import opened Errors

    import Values

    import Serializer

    import Deserializer

    import ZeroCopy = ZeroCopy.API
    function method {:opaque} {:fuel 0, 0} Serialize(js: Values.JSON): (bs: SerializationResult<seq<byte>>)
      decreases js
    {
      var js: Grammar.JSON :- Serializer.JSON(js); ZeroCopy.Serialize(js)
    }

    method SerializeAlloc(js: Values.JSON) returns (bs: SerializationResult<array<byte>>)
      decreases js
    {
      var js :- Serializer.JSON(js);
      bs := ZeroCopy.SerializeAlloc(js);
    }

    method SerializeInto(js: Values.JSON, bs: array<byte>) returns (len: SerializationResult<uint32>)
      modifies bs
      decreases js, bs
    {
      var js :- Serializer.JSON(js);
      len := ZeroCopy.SerializeInto(js, bs);
    }

    function method {:opaque} {:fuel 0, 0} Deserialize(bs: seq<byte>): (js: DeserializationResult<Values.JSON>)
      decreases bs
    {
      var js: Grammar.JSON :- ZeroCopy.Deserialize(bs); Deserializer.JSON(js)
    }
  }

  module {:options ""-functionSyntax:4""} Serializer {

    import Seq

    import Math

    import opened Wrappers

    import opened BoundedInts

    import opened Str = Utils.Str

    import Values

    import Spec

    import opened Errors

    import opened Vectors = Utils.Vectors

    import opened Grammar

    import opened Core = Utils.Views.Core
    type Result<+T> = SerializationResult<T>

    type bytes = seq<uint8>

    type bytes32 = bs: bytes
      | |bs| < TWO_TO_THE_32

    type string32 = s: string
      | |s| < TWO_TO_THE_32

    module ByteStrConversion refines Str.ParametricConversion {

      import opened BoundedInts
      type Char = uint8

      function method Digits(n: nat, base: int): (digits: seq<int>)
        requires base > 1
        ensures n == 0 ==> |digits| == 0
        ensures n > 0 ==> |digits| == Log(base, n) + 1
        ensures forall d: int {:trigger d in digits} | d in digits :: 0 <= d && d < base
        decreases n
      {
        if n == 0 then
          assert Pow(base, 0) == 1 by {
            reveal Pow();
          }
          []
        else
          LemmaDivPosIsPosAuto(); LemmaDivDecreasesAuto(); var digits': seq<int> := Digits(n / base, base); var digits: seq<int> := digits' + [n % base]; assert |digits| == Log(base, n) + 1 by {
    assert |digits| == |digits'| + 1;
    if n < base {
      LemmaLog0(base, n);
      assert n / base == 0 by {
        LemmaBasicDiv(base);
      }
    } else {
      LemmaLogS(base, n);
      assert n / base > 0 by {
        LemmaDivNonZeroAuto();
      }
    }
  } digits
      }

      function method OfDigits(digits: seq<int>, chars: seq<Char>): (str: String)
        requires forall d: int {:trigger d in digits} | d in digits :: 0 <= d && d < |chars|
        ensures forall c: uint8 {:trigger c in chars} {:trigger c in str} | c in str :: c in chars
        ensures |str| == |digits|
        decreases digits, chars
      {
        if digits == [] then
          []
        else
          assert digits[0] in digits; assert forall d: int {:trigger d in digits} {:trigger d in digits[1..]} | d in digits[1..] :: d in digits; [chars[digits[0]]] + OfDigits(digits[1..], chars)
      }

      function method OfNat_any(n: nat, chars: seq<Char>): (str: String)
        requires |chars| > 1
        ensures |str| == Log(|chars|, n) + 1
        ensures forall c: uint8 {:trigger c in chars} {:trigger c in str} | c in str :: c in chars
        decreases n, chars
      {
        var base: int := |chars|;
        if n == 0 then
          reveal Log();
          [chars[0]]
        else
          OfDigits(Digits(n, base), chars)
      }

      predicate method NumberStr(str: String, minus: Char, is_digit: Char -> bool)
        decreases str, minus
      {
        str != [] ==>
          (str[0] == minus || is_digit(str[0])) &&
          forall c: uint8 {:trigger is_digit(c)} {:trigger c in str[1..]} | c in str[1..] :: 
            is_digit(c)
      }

      function method OfInt_any(n: int, chars: seq<Char>, minus: Char): (str: String)
        requires |chars| > 1
        ensures NumberStr(str, minus, (c: uint8) => c in chars)
        decreases n, chars, minus
      {
        if n >= 0 then
          OfNat_any(n, chars)
        else
          [minus] + OfNat_any(-n, chars)
      }

      function method ToNat_any(str: String, base: nat, digits: map<Char, nat>): (n: nat)
        requires base > 0
        requires forall c: uint8 {:trigger c in digits} {:trigger c in str} | c in str :: c in digits
        decreases str, base, digits
      {
        if str == [] then
          0
        else
          LemmaMulNonnegativeAuto(); ToNat_any(str[..|str| - 1], base, digits) * base + digits[str[|str| - 1]]
      }

      lemma {:induction false} ToNat_bound(str: String, base: nat, digits: map<Char, nat>)
        requires base > 0
        requires forall c: uint8 {:trigger c in digits} {:trigger c in str} | c in str :: c in digits
        requires forall c: uint8 {:trigger digits[c]} {:trigger c in str} | c in str :: digits[c] < base
        ensures ToNat_any(str, base, digits) < Pow(base, |str|)
        decreases str, base, digits
      {
        if str == [] {
          reveal Pow();
        } else {
          calc <= {
            ToNat_any(str, base, digits);
            ToNat_any(str[..|str| - 1], base, digits) * base + digits[str[|str| - 1]];
            ToNat_any(str[..|str| - 1], base, digits) * base + base - 1;
            {
              ToNat_bound(str[..|str| - 1], base, digits);
              LemmaMulInequalityAuto();
            }
            (Pow(base, |str| - 1) - 1) * base + base - 1;
            {
              LemmaMulIsDistributiveAuto();
            }
            Pow(base, |str| - 1) * base - 1;
            {
              reveal Pow();
              LemmaMulIsCommutativeAuto();
            }
            Pow(base, |str|) - 1;
          }
        }
      }

      function method ToInt_any(str: String, minus: Char, base: nat, digits: map<Char, nat>): (s: int)
        requires base > 0
        requires str != [minus]
        requires NumberStr(str, minus, (c: uint8) => c in digits)
        decreases str, minus, base, digits
      {
        if [minus] <= str then
          -(ToNat_any(str[1..], base, digits) as int)
        else
          assert str == [] || str == [str[0]] + str[1..]; ToNat_any(str, base, digits)
      }

      import opened Wrappers

      import opened Mul

      import opened DivMod

      import opened Power

      import opened Logarithm

      type String = seq<Char>
    }

    function method Bool(b: bool): jbool
      decreases b
    {
      View.OfBytes(if b then TRUE else FALSE)
    }

    function method CheckLength<T>(s: seq<T>, err: SerializationError): Outcome<SerializationError>
      decreases s, err
    {
      Need(|s| < TWO_TO_THE_32, err)
    }

    function method String(str: string): Result<jstring>
      decreases str
    {
      var bs: bytes :- Spec.EscapeToUTF8(str); CheckLength(bs, StringTooLong(str)); Success(Grammar.JString(Grammar.DOUBLEQUOTE, View.OfBytes(bs), Grammar.DOUBLEQUOTE))
    }

    function method Sign(n: int): jminus
      decreases n
    {
      View.OfBytes(if n < 0 then ['-' as byte] else [])
    }

    const DIGITS := ['0' as uint8, '1' as uint8, '2' as uint8, '3' as uint8, '4' as uint8, '5' as uint8, '6' as uint8, '7' as uint8, '8' as uint8, '9' as uint8]
    const MINUS := '-' as uint8

    function method Int'(n: int): (str: bytes)
      ensures forall c: uint8 {:trigger c in DIGITS} {:trigger c in str} | c in str :: c in DIGITS || c == MINUS
      decreases n
    {
      ByteStrConversion.OfInt_any(n, DIGITS, MINUS)
    }

    function method Int(n: int): Result<View>
      decreases n
    {
      var bs: bytes := Int'(n);
      CheckLength(bs, IntTooLarge(n)); Success(View.OfBytes(bs))
    }

    function method Number(dec: Values.Decimal): Result<jnumber>
      decreases dec
    {
      var minus: jminus := Sign(dec.n);
      var num: jnum :- Int(Math.Abs(dec.n)); var frac: Maybe<jfrac> := Empty(); var exp: Maybe<jexp> :- if dec.e10 == 0 then Success(Empty()) else var e: je := View.OfBytes(['e' as byte]); var sign: jsign := Sign(dec.e10); var num: jnum :- Int(Math.Abs(dec.e10)); Success(NonEmpty(JExp(e, sign, num))); Success(JNumber(minus, num, Empty, exp))
    }

    function method MkStructural<T>(v: T): Structural<T>
    {
      Structural(EMPTY, v, EMPTY)
    }

    const COLON: Structural<jcolon> := MkStructural(Grammar.COLON)

    function method KeyValue(kv: (string, Values.JSON)): Result<jKeyValue>
      decreases kv
    {
      var k: jstring :- String(kv.0); var v: Grammar.Value :- Value(kv.1); Success(Grammar.KeyValue(k, COLON, v))
    }

    function method MkSuffixedSequence<D, S>(ds: seq<D>, suffix: Structural<S>, start: nat := 0): SuffixedSequence<D, S>
      decreases |ds| - start
    {
      if start >= |ds| then
        []
      else if start == |ds| - 1 then
        [Suffixed(ds[start], Empty)]
      else
        [Suffixed(ds[start], NonEmpty(suffix))] + MkSuffixedSequence(ds, suffix, start + 1)
    }

    const COMMA: Structural<jcomma> := MkStructural(Grammar.COMMA)

    function method Object(obj: seq<(string, Values.JSON)>): Result<jobject>
      decreases obj
    {
      var items: seq<jKeyValue> :- Seq.MapWithResult((v: (string, Values.JSON)) requires v in obj => KeyValue(v), obj); Success(Bracketed(MkStructural(LBRACE), MkSuffixedSequence(items, COMMA), MkStructural(RBRACE)))
    }

    function method Array(arr: seq<Values.JSON>): Result<jarray>
      decreases arr
    {
      var items: seq<Grammar.Value> :- Seq.MapWithResult((v: Values.JSON) requires v in arr => Value(v), arr); Success(Bracketed(MkStructural(LBRACKET), MkSuffixedSequence(items, COMMA), MkStructural(RBRACKET)))
    }

    function method Value(js: Values.JSON): Result<Grammar.Value>
      decreases js
    {
      match js
      case Null() =>
        Success(Grammar.Null(View.OfBytes(NULL)))
      case Bool(b) =>
        Success(Grammar.Bool(Bool(b)))
      case String(str) =>
        var s: jstring :- String(str); Success(Grammar.String(s))
      case Number(dec) =>
        var n: jnumber :- Number(dec); Success(Grammar.Number(n))
      case Object(obj) =>
        var o: jobject :- Object(obj); Success(Grammar.Object(o))
      case Array(arr) =>
        var a: jarray :- Array(arr); Success(Grammar.Array(a))
    }

    function method JSON(js: Values.JSON): Result<Grammar.JSON>
      decreases js
    {
      var val: Grammar.Value :- Value(js); Success(MkStructural(val))
    }
  }

  module {:options ""-functionSyntax:4""} Errors {

    import Wrappers

    import opened BoundedInts

    import Str = Utils.Str
    datatype DeserializationError = UnterminatedSequence | UnsupportedEscape(str: string) | EscapeAtEOS | EmptyNumber | ExpectingEOF | IntOverflow | ReachedEOF | ExpectingByte(expected: byte, b: opt_byte) | ExpectingAnyByte(expected_sq: seq<byte>, b: opt_byte) | InvalidUnicode {
      function method ToString(): string
        decreases this
      {
        match this
        case UnterminatedSequence() =>
          ""Unterminated sequence""
        case UnsupportedEscape(str) =>
          ""Unsupported escape sequence: "" + str
        case EscapeAtEOS() =>
          ""Escape character at end of string""
        case EmptyNumber() =>
          ""Number must contain at least one digit""
        case ExpectingEOF() =>
          ""Expecting EOF""
        case IntOverflow() =>
          ""Input length does not fit in a 32-bit counter""
        case ReachedEOF() =>
          ""Reached EOF""
        case ExpectingByte(b0, b) =>
          var c: seq<char> := if b > 0 then ""'"" + [b as char] + ""'"" else ""EOF"";
          ""Expecting '"" + [b0 as char] + ""', read "" + c
        case ExpectingAnyByte(bs0, b) =>
          var c: seq<char> := if b > 0 then ""'"" + [b as char] + ""'"" else ""EOF"";
          var c0s: seq<char> := seq(|bs0|, (idx: int) requires 0 <= idx < |bs0| => bs0[idx] as char);
          ""Expecting one of '"" + c0s + ""', read "" + c
        case InvalidUnicode() =>
          ""Invalid Unicode sequence""
      }
    }

    datatype SerializationError = OutOfMemory | IntTooLarge(i: int) | StringTooLong(s: string) | InvalidUnicode {
      function method ToString(): string
        decreases this
      {
        match this
        case OutOfMemory() =>
          ""Out of memory""
        case IntTooLarge(i: int) =>
          ""Integer too large: "" + Str.OfInt(i)
        case StringTooLong(s: string) =>
          ""String too long: "" + s
        case InvalidUnicode() =>
          ""Invalid Unicode sequence""
      }
    }

    type SerializationResult<+T> = Wrappers.Result<T, SerializationError>

    type DeserializationResult<+T> = Wrappers.Result<T, DeserializationError>
  }

  module {:options ""-functionSyntax:4""} Values {
    datatype Decimal = Decimal(n: int, e10: int)

    datatype JSON = Null | Bool(b: bool) | String(str: string) | Number(num: Decimal) | Object(obj: seq<(string, JSON)>) | Array(arr: seq<JSON>)

    function method Int(n: int): Decimal
      decreases n
    {
      Decimal(n, 0)
    }
  }

  module {:options ""-functionSyntax:4""} Grammar {

    import opened BoundedInts

    import opened Core = Utils.Views.Core
    type jchar = v: View
      | v.Length() == 1
      witness View.OfBytes(['b' as byte])

    type jquote = v: View
      | v.Char?('\""')
      witness DOUBLEQUOTE

    type jperiod = v: View
      | v.Char?('.')
      witness PERIOD

    type je = v: View
      | v.Char?('e') || v.Char?('E')
      witness E

    type jcolon = v: View
      | v.Char?(':')
      witness COLON

    type jcomma = v: View
      | v.Char?(',')
      witness COMMA

    type jlbrace = v: View
      | v.Char?('{')
      witness LBRACE

    type jrbrace = v: View
      | v.Char?('}')
      witness RBRACE

    type jlbracket = v: View
      | v.Char?('[')
      witness LBRACKET

    type jrbracket = v: View
      | v.Char?(']')
      witness RBRACKET

    type jminus = v: View
      | v.Char?('-') || v.Empty?
      witness MINUS

    type jsign = v: View
      | v.Char?('-') || v.Char?('+') || v.Empty?
      witness EMPTY

    type jblanks = v: View
      | Blanks?(v)
      witness View.OfBytes([])

    datatype Structural<+T> = Structural(before: jblanks, t: T, after: jblanks)

    datatype Maybe<+T> = Empty | NonEmpty(t: T)

    datatype Suffixed<+T, +S> = Suffixed(t: T, suffix: Maybe<Structural<S>>)

    type SuffixedSequence<+D, +S> = s: seq<Suffixed<D, S>>
      | NoTrailingSuffix(s)

    datatype Bracketed<+L, +D, +S, +R> = Bracketed(l: Structural<L>, data: SuffixedSequence<D, S>, r: Structural<R>)

    type jnull = v: View
      | Null?(v)
      witness View.OfBytes(NULL)

    type jbool = v: View
      | Bool?(v)
      witness View.OfBytes(TRUE)

    type jdigits = v: View
      | Digits?(v)
      witness View.OfBytes([])

    type jnum = v: View
      | Num?(v)
      witness View.OfBytes(['0' as byte])

    type jint = v: View
      | Int?(v)
      witness View.OfBytes(['0' as byte])

    type jstr = v: View
      | true
      witness View.OfBytes([])

    datatype jstring = JString(lq: jquote, contents: jstr, rq: jquote)

    datatype jKeyValue = KeyValue(k: jstring, colon: Structural<jcolon>, v: Value)

    type jobject = Bracketed<jlbrace, jKeyValue, jcomma, jrbrace>

    type jarray = Bracketed<jlbracket, Value, jcomma, jrbracket>

    type jmembers = SuffixedSequence<jKeyValue, jcomma>

    type jmember = Suffixed<jKeyValue, jcomma>

    type jitems = SuffixedSequence<Value, jcomma>

    type jitem = Suffixed<Value, jcomma>

    datatype jfrac = JFrac(period: jperiod, num: jnum)

    datatype jexp = JExp(e: je, sign: jsign, num: jnum)

    datatype jnumber = JNumber(minus: jminus, num: jnum, frac: Maybe<jfrac>, exp: Maybe<jexp>)

    datatype Value = Null(n: jnull) | Bool(b: jbool) | String(str: jstring) | Number(num: jnumber) | Object(obj: jobject) | Array(arr: jarray)

    type JSON = Structural<Value>

    const EMPTY := View.OfBytes([])
    const DOUBLEQUOTE := View.OfBytes(['\""' as byte])
    const PERIOD := View.OfBytes(['.' as byte])
    const E := View.OfBytes(['e' as byte])
    const COLON := View.OfBytes([':' as byte])
    const COMMA := View.OfBytes([',' as byte])
    const LBRACE := View.OfBytes(['{' as byte])
    const RBRACE := View.OfBytes(['}' as byte])
    const LBRACKET := View.OfBytes(['[' as byte])
    const RBRACKET := View.OfBytes([']' as byte])
    const MINUS := View.OfBytes(['-' as byte])

    predicate method Blank?(b: byte)
      decreases b
    {
      b == 32 || b == 9 || b == 10 || b == 13
    }

    predicate Blanks?(v: View)
      decreases v
    {
      forall b: uint8 {:trigger Blank?(b)} {:trigger b in v.Bytes()} | b in v.Bytes() :: 
        Blank?(b)
    }

    predicate NoTrailingSuffix<S, D>(s: seq<Suffixed<D, S>>)
      decreases s
    {
      forall idx: int {:trigger s[idx]} | 0 <= idx < |s| :: 
        s[idx].suffix.Empty? <==> idx == |s| - 1
    }

    const NULL: bytes := ['n' as byte, 'u' as byte, 'l' as byte, 'l' as byte]
    const TRUE: bytes := ['t' as byte, 'r' as byte, 'u' as byte, 'e' as byte]
    const FALSE: bytes := ['f' as byte, 'a' as byte, 'l' as byte, 's' as byte, 'e' as byte]

    predicate Null?(v: View)
      decreases v
    {
      v.Bytes() == NULL
    }

    predicate Bool?(v: View)
      decreases v
    {
      v.Bytes() in {TRUE, FALSE}
    }

    predicate method Digit?(b: byte)
      decreases b
    {
      '0' as byte <= b <= '9' as byte
    }

    predicate Digits?(v: View)
      decreases v
    {
      forall b: uint8 {:trigger Digit?(b)} {:trigger b in v.Bytes()} | b in v.Bytes() :: 
        Digit?(b)
    }

    predicate Num?(v: View)
      decreases v
    {
      Digits?(v) &&
      !v.Empty?
    }

    predicate Int?(v: View)
      decreases v
    {
      v.Char?('0') || (Num?(v) && v.At(0) != '0' as byte)
    }
  }

  module {:options ""-functionSyntax:4""} Spec {

    import opened BoundedInts

    import opened Str = Utils.Str

    import opened Values

    import opened Wrappers

    import opened Errors

    import opened UnicodeStrings

    import opened Logarithm

    import Seq
    type bytes = seq<uint8>

    type Result<+T> = SerializationResult<T>

    function method EscapeUnicode(c: uint16): seq<uint16>
      decreases c
    {
      var sStr: string := Str.OfNat(c as nat, 16);
      Seq.MembershipImpliesIndexing((c: char) => 0 <= c as int < 128, sStr);
      var s: seq<uint16> := ASCIIToUTF16(sStr);
      assert |s| <= 4 by {
        assert c as nat <= 65535;
        assert Log(16, c as nat) <= Log(16, 65535) by {
          LemmaLogIsOrdered(16, c as nat, 65535);
        }
        assert Log(16, 65535) == 3 by {
          reveal Log();
        }
      }
      s + seq(4 - |s|, (_ /* _v0 */: int) => ' ' as uint16)
    }

    function method Escape(str: seq<uint16>, start: nat := 0): seq<uint16>
      decreases |str| - start
    {
      if start >= |str| then
        []
      else
        (match str[start] case 34 => ASCIIToUTF16(""\\\"""") case 92 => ASCIIToUTF16(""\\\\"") case 8 => ASCIIToUTF16(""\\b"") case 12 => ASCIIToUTF16(""\\f"") case 10 => ASCIIToUTF16(""\\n"") case 13 => ASCIIToUTF16(""\\r"") case 9 => ASCIIToUTF16(""\\t"") case c => (if c < 31 then ASCIIToUTF16(""\\u"") + EscapeUnicode(c) else [str[start]])) + Escape(str, start + 1)
    }

    function method EscapeToUTF8(str: string, start: nat := 0): Result<bytes>
      decreases str, start
    {
      var utf16: seq<uint16> :- ToUTF16Checked(str).ToResult'(SerializationError.InvalidUnicode); var escaped: seq<uint16> := Escape(utf16); var utf32: string :- FromUTF16Checked(escaped).ToResult'(SerializationError.InvalidUnicode); ToUTF8Checked(utf32).ToResult'(SerializationError.InvalidUnicode)
    }

    function method String(str: string): Result<bytes>
      decreases str
    {
      var inBytes: bytes :- EscapeToUTF8(str); Success(ASCIIToUTF8(""\"""") + inBytes + ASCIIToUTF8(""\""""))
    }

    lemma OfIntOnlyASCII(n: int)
      ensures true && ghost var s: string := Str.OfInt(n); true && forall i: int {:trigger s[i]} | 0 <= i < |s| :: 0 <= s[i] as int && s[i] as int < 128
      decreases n
    {
    }

    function method IntToBytes(n: int): bytes
      decreases n
    {
      var s: string := Str.OfInt(n);
      OfIntOnlyASCII(n);
      ASCIIToUTF8(s)
    }

    function method Number(dec: Decimal): Result<bytes>
      decreases dec
    {
      Success(IntToBytes(dec.n) + if dec.e10 == 0 then [] else ASCIIToUTF8(""e"") + IntToBytes(dec.e10))
    }

    function method KeyValue(kv: (string, JSON)): Result<bytes>
      decreases kv
    {
      var key: bytes :- String(kv.0); var value: bytes :- JSON(kv.1); Success(key + ASCIIToUTF8("":"") + value)
    }

    function method Join(sep: bytes, items: seq<Result<bytes>>): Result<bytes>
      decreases sep, items
    {
      if |items| == 0 then
        Success([])
      else
        var first: bytes :- items[0]; if |items| == 1 then Success(first) else var rest: bytes :- Join(sep, items[1..]); Success(first + sep + rest)
    }

    function method Object(obj: seq<(string, JSON)>): Result<bytes>
      decreases obj
    {
      var middle: bytes :- Join(ASCIIToUTF8("",""), seq(|obj|, (i: int) requires 0 <= i < |obj| => KeyValue(obj[i]))); Success(ASCIIToUTF8(""{"") + middle + ASCIIToUTF8(""}""))
    }

    function method Array(arr: seq<JSON>): Result<bytes>
      decreases arr
    {
      var middle: bytes :- Join(ASCIIToUTF8("",""), seq(|arr|, (i: int) requires 0 <= i < |arr| => JSON(arr[i]))); Success(ASCIIToUTF8(""["") + middle + ASCIIToUTF8(""]""))
    }

    function method JSON(js: JSON): Result<bytes>
      decreases js
    {
      match js
      case Null() =>
        Success(ASCIIToUTF8(""null""))
      case Bool(b) =>
        Success(if b then ASCIIToUTF8(""true"") else ASCIIToUTF8(""false""))
      case String(str) =>
        String(str)
      case Number(dec) =>
        Number(dec)
      case Object(obj) =>
        Object(obj)
      case Array(arr) =>
        Array(arr)
    }
  }

  module {:options ""-functionSyntax:4""} Deserializer {

    import Seq

    import opened Wrappers

    import opened BoundedInts

    import opened Logarithm

    import opened Power

    import opened Str = Utils.Str

    import opened UnicodeStrings

    import Values

    import Spec

    import opened Errors

    import opened Vectors = Utils.Vectors

    import opened Grammar

    import opened Core = Utils.Views.Core

    module Uint16StrConversion refines Str.ParametricConversion {

      import opened BoundedInts
      type Char = uint16

      function method Digits(n: nat, base: int): (digits: seq<int>)
        requires base > 1
        ensures n == 0 ==> |digits| == 0
        ensures n > 0 ==> |digits| == Log(base, n) + 1
        ensures forall d: int {:trigger d in digits} | d in digits :: 0 <= d && d < base
        decreases n
      {
        if n == 0 then
          assert Pow(base, 0) == 1 by {
            reveal Pow();
          }
          []
        else
          LemmaDivPosIsPosAuto(); LemmaDivDecreasesAuto(); var digits': seq<int> := Digits(n / base, base); var digits: seq<int> := digits' + [n % base]; assert |digits| == Log(base, n) + 1 by {
    assert |digits| == |digits'| + 1;
    if n < base {
      LemmaLog0(base, n);
      assert n / base == 0 by {
        LemmaBasicDiv(base);
      }
    } else {
      LemmaLogS(base, n);
      assert n / base > 0 by {
        LemmaDivNonZeroAuto();
      }
    }
  } digits
      }

      function method OfDigits(digits: seq<int>, chars: seq<Char>): (str: String)
        requires forall d: int {:trigger d in digits} | d in digits :: 0 <= d && d < |chars|
        ensures forall c: uint16 {:trigger c in chars} {:trigger c in str} | c in str :: c in chars
        ensures |str| == |digits|
        decreases digits, chars
      {
        if digits == [] then
          []
        else
          assert digits[0] in digits; assert forall d: int {:trigger d in digits} {:trigger d in digits[1..]} | d in digits[1..] :: d in digits; [chars[digits[0]]] + OfDigits(digits[1..], chars)
      }

      function method OfNat_any(n: nat, chars: seq<Char>): (str: String)
        requires |chars| > 1
        ensures |str| == Log(|chars|, n) + 1
        ensures forall c: uint16 {:trigger c in chars} {:trigger c in str} | c in str :: c in chars
        decreases n, chars
      {
        var base: int := |chars|;
        if n == 0 then
          reveal Log();
          [chars[0]]
        else
          OfDigits(Digits(n, base), chars)
      }

      predicate method NumberStr(str: String, minus: Char, is_digit: Char -> bool)
        decreases str, minus
      {
        str != [] ==>
          (str[0] == minus || is_digit(str[0])) &&
          forall c: uint16 {:trigger is_digit(c)} {:trigger c in str[1..]} | c in str[1..] :: 
            is_digit(c)
      }

      function method OfInt_any(n: int, chars: seq<Char>, minus: Char): (str: String)
        requires |chars| > 1
        ensures NumberStr(str, minus, (c: uint16) => c in chars)
        decreases n, chars, minus
      {
        if n >= 0 then
          OfNat_any(n, chars)
        else
          [minus] + OfNat_any(-n, chars)
      }

      function method ToNat_any(str: String, base: nat, digits: map<Char, nat>): (n: nat)
        requires base > 0
        requires forall c: uint16 {:trigger c in digits} {:trigger c in str} | c in str :: c in digits
        decreases str, base, digits
      {
        if str == [] then
          0
        else
          LemmaMulNonnegativeAuto(); ToNat_any(str[..|str| - 1], base, digits) * base + digits[str[|str| - 1]]
      }

      lemma {:induction false} ToNat_bound(str: String, base: nat, digits: map<Char, nat>)
        requires base > 0
        requires forall c: uint16 {:trigger c in digits} {:trigger c in str} | c in str :: c in digits
        requires forall c: uint16 {:trigger digits[c]} {:trigger c in str} | c in str :: digits[c] < base
        ensures ToNat_any(str, base, digits) < Pow(base, |str|)
        decreases str, base, digits
      {
        if str == [] {
          reveal Pow();
        } else {
          calc <= {
            ToNat_any(str, base, digits);
            ToNat_any(str[..|str| - 1], base, digits) * base + digits[str[|str| - 1]];
            ToNat_any(str[..|str| - 1], base, digits) * base + base - 1;
            {
              ToNat_bound(str[..|str| - 1], base, digits);
              LemmaMulInequalityAuto();
            }
            (Pow(base, |str| - 1) - 1) * base + base - 1;
            {
              LemmaMulIsDistributiveAuto();
            }
            Pow(base, |str| - 1) * base - 1;
            {
              reveal Pow();
              LemmaMulIsCommutativeAuto();
            }
            Pow(base, |str|) - 1;
          }
        }
      }

      function method ToInt_any(str: String, minus: Char, base: nat, digits: map<Char, nat>): (s: int)
        requires base > 0
        requires str != [minus]
        requires NumberStr(str, minus, (c: uint16) => c in digits)
        decreases str, minus, base, digits
      {
        if [minus] <= str then
          -(ToNat_any(str[1..], base, digits) as int)
        else
          assert str == [] || str == [str[0]] + str[1..]; ToNat_any(str, base, digits)
      }

      import opened Wrappers

      import opened Mul

      import opened DivMod

      import opened Power

      import opened Logarithm

      type String = seq<Char>
    }

    module ByteStrConversion refines Str.ParametricConversion {

      import opened BoundedInts
      type Char = byte

      function method Digits(n: nat, base: int): (digits: seq<int>)
        requires base > 1
        ensures n == 0 ==> |digits| == 0
        ensures n > 0 ==> |digits| == Log(base, n) + 1
        ensures forall d: int {:trigger d in digits} | d in digits :: 0 <= d && d < base
        decreases n
      {
        if n == 0 then
          assert Pow(base, 0) == 1 by {
            reveal Pow();
          }
          []
        else
          LemmaDivPosIsPosAuto(); LemmaDivDecreasesAuto(); var digits': seq<int> := Digits(n / base, base); var digits: seq<int> := digits' + [n % base]; assert |digits| == Log(base, n) + 1 by {
    assert |digits| == |digits'| + 1;
    if n < base {
      LemmaLog0(base, n);
      assert n / base == 0 by {
        LemmaBasicDiv(base);
      }
    } else {
      LemmaLogS(base, n);
      assert n / base > 0 by {
        LemmaDivNonZeroAuto();
      }
    }
  } digits
      }

      function method OfDigits(digits: seq<int>, chars: seq<Char>): (str: String)
        requires forall d: int {:trigger d in digits} | d in digits :: 0 <= d && d < |chars|
        ensures forall c: uint8 {:trigger c in chars} {:trigger c in str} | c in str :: c in chars
        ensures |str| == |digits|
        decreases digits, chars
      {
        if digits == [] then
          []
        else
          assert digits[0] in digits; assert forall d: int {:trigger d in digits} {:trigger d in digits[1..]} | d in digits[1..] :: d in digits; [chars[digits[0]]] + OfDigits(digits[1..], chars)
      }

      function method OfNat_any(n: nat, chars: seq<Char>): (str: String)
        requires |chars| > 1
        ensures |str| == Log(|chars|, n) + 1
        ensures forall c: uint8 {:trigger c in chars} {:trigger c in str} | c in str :: c in chars
        decreases n, chars
      {
        var base: int := |chars|;
        if n == 0 then
          reveal Log();
          [chars[0]]
        else
          OfDigits(Digits(n, base), chars)
      }

      predicate method NumberStr(str: String, minus: Char, is_digit: Char -> bool)
        decreases str, minus
      {
        str != [] ==>
          (str[0] == minus || is_digit(str[0])) &&
          forall c: uint8 {:trigger is_digit(c)} {:trigger c in str[1..]} | c in str[1..] :: 
            is_digit(c)
      }

      function method OfInt_any(n: int, chars: seq<Char>, minus: Char): (str: String)
        requires |chars| > 1
        ensures NumberStr(str, minus, (c: uint8) => c in chars)
        decreases n, chars, minus
      {
        if n >= 0 then
          OfNat_any(n, chars)
        else
          [minus] + OfNat_any(-n, chars)
      }

      function method ToNat_any(str: String, base: nat, digits: map<Char, nat>): (n: nat)
        requires base > 0
        requires forall c: uint8 {:trigger c in digits} {:trigger c in str} | c in str :: c in digits
        decreases str, base, digits
      {
        if str == [] then
          0
        else
          LemmaMulNonnegativeAuto(); ToNat_any(str[..|str| - 1], base, digits) * base + digits[str[|str| - 1]]
      }

      lemma {:induction false} ToNat_bound(str: String, base: nat, digits: map<Char, nat>)
        requires base > 0
        requires forall c: uint8 {:trigger c in digits} {:trigger c in str} | c in str :: c in digits
        requires forall c: uint8 {:trigger digits[c]} {:trigger c in str} | c in str :: digits[c] < base
        ensures ToNat_any(str, base, digits) < Pow(base, |str|)
        decreases str, base, digits
      {
        if str == [] {
          reveal Pow();
        } else {
          calc <= {
            ToNat_any(str, base, digits);
            ToNat_any(str[..|str| - 1], base, digits) * base + digits[str[|str| - 1]];
            ToNat_any(str[..|str| - 1], base, digits) * base + base - 1;
            {
              ToNat_bound(str[..|str| - 1], base, digits);
              LemmaMulInequalityAuto();
            }
            (Pow(base, |str| - 1) - 1) * base + base - 1;
            {
              LemmaMulIsDistributiveAuto();
            }
            Pow(base, |str| - 1) * base - 1;
            {
              reveal Pow();
              LemmaMulIsCommutativeAuto();
            }
            Pow(base, |str|) - 1;
          }
        }
      }

      function method ToInt_any(str: String, minus: Char, base: nat, digits: map<Char, nat>): (s: int)
        requires base > 0
        requires str != [minus]
        requires NumberStr(str, minus, (c: uint8) => c in digits)
        decreases str, minus, base, digits
      {
        if [minus] <= str then
          -(ToNat_any(str[1..], base, digits) as int)
        else
          assert str == [] || str == [str[0]] + str[1..]; ToNat_any(str, base, digits)
      }

      import opened Wrappers

      import opened Mul

      import opened DivMod

      import opened Power

      import opened Logarithm

      type String = seq<Char>
    }
    function method Bool(js: Grammar.jbool): bool
      decreases js
    {
      assert js.Bytes() in {Grammar.TRUE, Grammar.FALSE};
      js.At(0) == 't' as byte
    }

    function method UnsupportedEscape16(code: seq<uint16>): DeserializationError
      decreases code
    {
      UnsupportedEscape(FromUTF16Checked(code).UnwrapOr(""Couldn't decode UTF-16""))
    }

    const HEX_TABLE_16: map<Uint16StrConversion.Char, nat> := map['0' as uint16 := 0, '1' as uint16 := 1, '2' as uint16 := 2, '3' as uint16 := 3, '4' as uint16 := 4, '5' as uint16 := 5, '6' as uint16 := 6, '7' as uint16 := 7, '8' as uint16 := 8, '9' as uint16 := 9, 'a' as uint16 := 10, 'b' as uint16 := 11, 'c' as uint16 := 12, 'd' as uint16 := 13, 'e' as uint16 := 14, 'f' as uint16 := 15, 'A' as uint16 := 10, 'B' as uint16 := 11, 'C' as uint16 := 12, 'D' as uint16 := 13, 'E' as uint16 := 14, 'F' as uint16 := 15]

    function method ToNat16(str: Uint16StrConversion.String): uint16
      requires |str| <= 4
      requires forall c: uint16 {:trigger c in HEX_TABLE_16} {:trigger c in str} | c in str :: c in HEX_TABLE_16
      decreases str
    {
      Uint16StrConversion.ToNat_bound(str, 16, HEX_TABLE_16);
      var hd: nat := Uint16StrConversion.ToNat_any(str, 16, HEX_TABLE_16);
      assert hd < 65536 by {
        reveal Pow();
      }
      hd as uint16
    }

    function method {:tailrecursion} {:vcs_split_on_every_assert} Unescape(str: seq<uint16>, start: nat := 0, prefix: seq<uint16> := []): DeserializationResult<seq<uint16>>
      decreases |str| - start
    {
      if start >= |str| then
        Success(prefix)
      else if str[start] == '\\' as uint16 then
        if |str| == start + 1 then
          Failure(EscapeAtEOS)
        else
          var c: uint16 := str[start + 1]; if c == 'u' as uint16 then if |str| <= start + 6 then Failure(EscapeAtEOS) else var code: seq<uint16> := str[start + 2 .. start + 6]; if exists c: uint16 {:trigger c in HEX_TABLE_16} {:trigger c in code} | c in code :: c !in HEX_TABLE_16 then Failure(UnsupportedEscape16(code)) else var hd: uint16 := ToNat16(code); Unescape(str, start + 6, prefix + [hd]) else var unescaped: uint16 := match c case 34 => 34 as uint16 case 92 => 92 as uint16 case 98 => 8 as uint16 case 102 => 12 as uint16 case 110 => 10 as uint16 case 114 => 13 as uint16 case 116 => 9 as uint16 case _ /* _v0 */ => 0 as uint16; if unescaped as int == 0 then Failure(UnsupportedEscape16(str[start .. start + 2])) else Unescape(str, start + 2, prefix + [unescaped])
      else
        Unescape(str, start + 1, prefix + [str[start]])
    }

    function method String(js: Grammar.jstring): DeserializationResult<string>
      decreases js
    {
      var asUtf32: string :- FromUTF8Checked(js.contents.Bytes()).ToResult'(DeserializationError.InvalidUnicode); var asUint16: seq<uint16> :- ToUTF16Checked(asUtf32).ToResult'(DeserializationError.InvalidUnicode); var unescaped: seq<uint16> :- Unescape(asUint16); FromUTF16Checked(unescaped).ToResult'(DeserializationError.InvalidUnicode)
    }

    const DIGITS := map['0' as uint8 := 0, '1' as uint8 := 1, '2' as uint8 := 2, '3' as uint8 := 3, '4' as uint8 := 4, '5' as uint8 := 5, '6' as uint8 := 6, '7' as uint8 := 7, '8' as uint8 := 8, '9' as uint8 := 9]
    const MINUS := '-' as uint8

    function method ToInt(sign: jsign, n: jnum): DeserializationResult<int>
      decreases sign, n
    {
      var n: int := ByteStrConversion.ToNat_any(n.Bytes(), 10, DIGITS);
      Success(if sign.Char?('-') then -n else n)
    }

    function method Number(js: Grammar.jnumber): DeserializationResult<Values.Decimal>
      decreases js
    {
      var JNumber(minus: jminus, num: jnum, frac: Maybe<jfrac>, exp: Maybe<jexp>) := js;
      var n: int :- ToInt(minus, num); var e10: int :- match exp case Empty() => Success(0) case NonEmpty(JExp(_ /* _v1 */, sign, num)) => ToInt(sign, num); match frac case Empty() => Success(Values.Decimal(n, e10)) case NonEmpty(JFrac(_ /* _v2 */, num)) => var pow10: int := num.Length() as int; var frac: int :- ToInt(minus, num); Success(Values.Decimal(n * Pow(10, pow10) + frac, e10 - pow10))
    }

    function method KeyValue(js: Grammar.jKeyValue): DeserializationResult<(string, Values.JSON)>
      decreases js
    {
      var k: string :- String(js.k); var v: Values.JSON :- Value(js.v); Success((k, v))
    }

    function method Object(js: Grammar.jobject): DeserializationResult<seq<(string, Values.JSON)>>
      decreases js
    {
      Seq.MapWithResult((d: Suffixed<jKeyValue, jcomma>) requires d in js.data => KeyValue(d.t), js.data)
    }

    function method Array(js: Grammar.jarray): DeserializationResult<seq<Values.JSON>>
      decreases js
    {
      Seq.MapWithResult((d: Suffixed<Value, jcomma>) requires d in js.data => Value(d.t), js.data)
    }

    function method Value(js: Grammar.Value): DeserializationResult<Values.JSON>
      decreases js
    {
      match js
      case Null(_ /* _v3 */) =>
        Success(Values.Null())
      case Bool(b) =>
        Success(Values.Bool(Bool(b)))
      case String(str) =>
        var s: string :- String(str); Success(Values.String(s))
      case Number(dec) =>
        var n: Values.Decimal :- Number(dec); Success(Values.Number(n))
      case Object(obj) =>
        var o: seq<(string, Values.JSON)> :- Object(obj); Success(Values.Object(o))
      case Array(arr) =>
        var a: seq<Values.JSON> :- Array(arr); Success(Values.Array(a))
    }

    function method JSON(js: Grammar.JSON): DeserializationResult<Values.JSON>
      decreases js
    {
      Value(js.t)
    }
  }

  module Utils {

    module {:options ""-functionSyntax:4""} Vectors {

      import opened BoundedInts

      import opened Wrappers
      datatype VectorError = OutOfMemory

      class Vector<A> {
        ghost var items: seq<A>
        ghost var Repr: set<object>
        const a: A
        var size: uint32
        var capacity: uint32
        var data: array<A>
        const MAX_CAPACITY: uint32 := UINT32_MAX
        const MAX_CAPACITY_BEFORE_DOUBLING: uint32 := UINT32_MAX / 2

        predicate Valid?()
          reads this, Repr
          ensures Valid?() ==> this in Repr
          decreases Repr + {this}
        {
          Repr == {this, data} &&
          capacity != 0 &&
          data.Length == capacity as int &&
          size <= capacity &&
          size as int == |items| &&
          items == data[..size]
        }

        constructor (a0: A, initial_capacity: uint32 := 8)
          requires initial_capacity > 0
          ensures size == 0
          ensures items == []
          ensures fresh(Repr)
          ensures Valid?()
          decreases initial_capacity
        {
          a := a0;
          items := [];
          size := 0;
          capacity := initial_capacity;
          data := new A[initial_capacity] ((_ /* _v0 */: nat) => a0);
          Repr := {this, data};
        }

        function method At(idx: uint32): (a: A)
          requires idx < size
          requires Valid?()
          reads this, this.data
          ensures a == data[idx] == items[idx]
          decreases {this, this.data}, idx
        {
          data[idx]
        }

        function method Top(): (a: A)
          requires 0 < size
          requires Valid?()
          reads this, this.data
          ensures a == data[size - 1] == items[size - 1]
          decreases {this, this.data}
        {
          data[size - 1]
        }

        method Put(idx: uint32, a: A)
          requires idx < size
          requires Valid?()
          modifies data, `items
          ensures Valid?()
          ensures items == old(items)[idx := a]
          decreases idx
        {
          data[idx] := a;
          items := items[idx := a];
        }

        method CopyFrom(new_data: array<A>, count: uint32)
          requires count as int <= new_data.Length
          requires count <= capacity
          requires data.Length == capacity as int
          modifies data
          ensures data[..count] == new_data[..count]
          ensures data[count..] == old(data[count..])
          decreases new_data, count
        {
          for idx: uint32 := 0 to count
            invariant idx <= capacity
            invariant data.Length == capacity as int
            invariant data[..idx] == new_data[..idx]
            invariant data[count..] == old(data[count..])
          {
            data[idx] := new_data[idx];
          }
        }

        method Realloc(new_capacity: uint32)
          requires Valid?()
          requires new_capacity > capacity
          modifies `capacity, `data, `Repr, data
          ensures Valid?()
          ensures capacity == new_capacity
          ensures fresh(data)
          decreases new_capacity
        {
          var old_data, old_capacity := data, capacity;
          data, capacity := new A[new_capacity] ((_ /* _v1 */: nat) => a), new_capacity;
          CopyFrom(old_data, old_capacity);
          Repr := {this, data};
        }

        function method DefaultNewCapacity(capacity: uint32): uint32
          decreases capacity
        {
          if capacity < MAX_CAPACITY_BEFORE_DOUBLING then
            2 * capacity
          else
            MAX_CAPACITY
        }

        method ReallocDefault() returns (o: Outcome<VectorError>)
          requires Valid?()
          modifies `capacity, `data, `Repr, data
          ensures Valid?()
          ensures o.Fail? <==> old(capacity) == MAX_CAPACITY
          ensures o.Fail? ==> unchanged(this) && unchanged(data)
          ensures o.Pass? ==> fresh(data) && old(capacity) < MAX_CAPACITY && capacity == old(if capacity < MAX_CAPACITY_BEFORE_DOUBLING then 2 * capacity else MAX_CAPACITY)
        {
          if capacity == MAX_CAPACITY {
            return Fail(OutOfMemory);
          }
          Realloc(DefaultNewCapacity(capacity));
          return Pass;
        }

        method Ensure(reserved: uint32) returns (o: Outcome<VectorError>)
          requires Valid?()
          modifies this, `data, `capacity, `data, `Repr, data
          ensures Valid?()
          ensures reserved <= capacity - size ==> o.Pass?
          ensures o.Pass? ==> old(size as int + reserved as int) <= capacity as int
          ensures o.Fail? ==> reserved > MAX_CAPACITY - size
          decreases reserved
        {
          if reserved > MAX_CAPACITY - size {
            return Fail(OutOfMemory);
          }
          if reserved <= capacity - size {
            return Pass;
          }
          var new_capacity := capacity;
          while reserved > new_capacity - size
            invariant new_capacity >= capacity
            decreases MAX_CAPACITY - new_capacity
          {
            new_capacity := DefaultNewCapacity(new_capacity);
          }
          Realloc(new_capacity);
          return Pass;
        }

        method PopFast()
          requires Valid?()
          requires size > 0
          modifies `size, `items
          ensures Valid?()
          ensures size == old(size) - 1
          ensures items == old(items[..|items| - 1])
        {
          size := size - 1;
          items := items[..|items| - 1];
        }

        method PushFast(a: A)
          requires Valid?()
          requires size < capacity
          modifies `size, `items, data
          ensures Valid?()
          ensures size == old(size) + 1
          ensures items == old(items) + [a]
        {
          data[size] := a;
          size := size + 1;
          items := items + [a];
        }

        method Push(a: A) returns (o: Outcome<VectorError>)
          requires Valid?()
          modifies this, data
          ensures Valid?()
          ensures o.Fail? ==> unchanged(this) && unchanged(data)
          ensures o.Pass? ==> old(size) < MAX_CAPACITY && size == old(size) + 1 && items == old(items) + [a] && capacity >= old(capacity) && if old(size == capacity) then fresh(data) else unchanged(`data)
        {
          if size == capacity {
            var d := ReallocDefault();
            if d.Fail? {
              return d;
            }
          }
          PushFast(a);
          return Pass;
        }
      }

      const OOM_FAILURE := Fail(OutOfMemory)
    }

    module {:options ""-functionSyntax:4""} Str {

      import opened Wrappers

      import opened Power

      import opened Logarithm

      abstract module ParametricConversion {

        import opened Wrappers

        import opened Mul

        import opened DivMod

        import opened Power

        import opened Logarithm
        type Char(==)

        type String = seq<Char>

        function method Digits(n: nat, base: int): (digits: seq<int>)
          requires base > 1
          ensures n == 0 ==> |digits| == 0
          ensures n > 0 ==> |digits| == Log(base, n) + 1
          ensures forall d: int {:trigger d in digits} | d in digits :: 0 <= d && d < base
          decreases n
        {
          if n == 0 then
            assert Pow(base, 0) == 1 by {
              reveal Pow();
            }
            []
          else
            LemmaDivPosIsPosAuto(); LemmaDivDecreasesAuto(); var digits': seq<int> := Digits(n / base, base); var digits: seq<int> := digits' + [n % base]; assert |digits| == Log(base, n) + 1 by {
    assert |digits| == |digits'| + 1;
    if n < base {
      LemmaLog0(base, n);
      assert n / base == 0 by {
        LemmaBasicDiv(base);
      }
    } else {
      LemmaLogS(base, n);
      assert n / base > 0 by {
        LemmaDivNonZeroAuto();
      }
    }
  } digits
        }

        function method OfDigits(digits: seq<int>, chars: seq<Char>): (str: String)
          requires forall d: int {:trigger d in digits} | d in digits :: 0 <= d && d < |chars|
          ensures forall c: Char {:trigger c in chars} {:trigger c in str} | c in str :: c in chars
          ensures |str| == |digits|
          decreases digits, chars
        {
          if digits == [] then
            []
          else
            assert digits[0] in digits; assert forall d: int {:trigger d in digits} {:trigger d in digits[1..]} | d in digits[1..] :: d in digits; [chars[digits[0]]] + OfDigits(digits[1..], chars)
        }

        function method OfNat_any(n: nat, chars: seq<Char>): (str: String)
          requires |chars| > 1
          ensures |str| == Log(|chars|, n) + 1
          ensures forall c: Char {:trigger c in chars} {:trigger c in str} | c in str :: c in chars
          decreases n, chars
        {
          var base: int := |chars|;
          if n == 0 then
            reveal Log();
            [chars[0]]
          else
            OfDigits(Digits(n, base), chars)
        }

        predicate method NumberStr(str: String, minus: Char, is_digit: Char -> bool)
          decreases str
        {
          str != [] ==>
            (str[0] == minus || is_digit(str[0])) &&
            forall c: Char {:trigger is_digit(c)} {:trigger c in str[1..]} | c in str[1..] :: 
              is_digit(c)
        }

        function method OfInt_any(n: int, chars: seq<Char>, minus: Char): (str: String)
          requires |chars| > 1
          ensures NumberStr(str, minus, (c: Char) => c in chars)
          decreases n, chars
        {
          if n >= 0 then
            OfNat_any(n, chars)
          else
            [minus] + OfNat_any(-n, chars)
        }

        function method ToNat_any(str: String, base: nat, digits: map<Char, nat>): (n: nat)
          requires base > 0
          requires forall c: Char {:trigger c in digits} {:trigger c in str} | c in str :: c in digits
          decreases str, base, digits
        {
          if str == [] then
            0
          else
            LemmaMulNonnegativeAuto(); ToNat_any(str[..|str| - 1], base, digits) * base + digits[str[|str| - 1]]
        }

        lemma {:induction false} ToNat_bound(str: String, base: nat, digits: map<Char, nat>)
          requires base > 0
          requires forall c: Char {:trigger c in digits} {:trigger c in str} | c in str :: c in digits
          requires forall c: Char {:trigger digits[c]} {:trigger c in str} | c in str :: digits[c] < base
          ensures ToNat_any(str, base, digits) < Pow(base, |str|)
          decreases str, base, digits
        {
        }

        function method ToInt_any(str: String, minus: Char, base: nat, digits: map<Char, nat>): (s: int)
          requires base > 0
          requires str != [minus]
          requires NumberStr(str, minus, (c: Char) => c in digits)
          decreases str, base, digits
        {
          if [minus] <= str then
            -(ToNat_any(str[1..], base, digits) as int)
          else
            assert str == [] || str == [str[0]] + str[1..]; ToNat_any(str, base, digits)
        }
      }

      abstract module ParametricEscaping {

        import opened Wrappers
        type Char(==)

        type String = seq<Char>

        datatype UnescapeError = EscapeAtEOS

        function method Escape(str: String, special: set<Char>, escape: Char): String
          decreases str, special
        {
          if str == [] then
            str
          else if str[0] in special then
            [escape, str[0]] + Escape(str[1..], special, escape)
          else
            [str[0]] + Escape(str[1..], special, escape)
        }

        function method Unescape(str: String, escape: Char): Result<String, UnescapeError>
          decreases str
        {
          if str == [] then
            Success(str)
          else if str[0] == escape then
            if |str| > 1 then
              var tl: String :- Unescape(str[2..], escape); Success([str[1]] + tl)
            else
              Failure(EscapeAtEOS)
          else
            var tl: String :- Unescape(str[1..], escape); Success([str[0]] + tl)
        }

        lemma {:induction false} Unescape_Escape(str: String, special: set<Char>, escape: Char)
          requires escape in special
          ensures Unescape(Escape(str, special, escape), escape) == Success(str)
          decreases str, special
        {
        }
      }

      module CharStrConversion refines ParametricConversion {
        type Char = char

        function method Digits(n: nat, base: int): (digits: seq<int>)
          requires base > 1
          ensures n == 0 ==> |digits| == 0
          ensures n > 0 ==> |digits| == Log(base, n) + 1
          ensures forall d: int {:trigger d in digits} | d in digits :: 0 <= d && d < base
          decreases n
        {
          if n == 0 then
            assert Pow(base, 0) == 1 by {
              reveal Pow();
            }
            []
          else
            LemmaDivPosIsPosAuto(); LemmaDivDecreasesAuto(); var digits': seq<int> := Digits(n / base, base); var digits: seq<int> := digits' + [n % base]; assert |digits| == Log(base, n) + 1 by {
    assert |digits| == |digits'| + 1;
    if n < base {
      LemmaLog0(base, n);
      assert n / base == 0 by {
        LemmaBasicDiv(base);
      }
    } else {
      LemmaLogS(base, n);
      assert n / base > 0 by {
        LemmaDivNonZeroAuto();
      }
    }
  } digits
        }

        function method OfDigits(digits: seq<int>, chars: seq<Char>): (str: String)
          requires forall d: int {:trigger d in digits} | d in digits :: 0 <= d && d < |chars|
          ensures forall c: char {:trigger c in chars} {:trigger c in str} | c in str :: c in chars
          ensures |str| == |digits|
          decreases digits, chars
        {
          if digits == [] then
            []
          else
            assert digits[0] in digits; assert forall d: int {:trigger d in digits} {:trigger d in digits[1..]} | d in digits[1..] :: d in digits; [chars[digits[0]]] + OfDigits(digits[1..], chars)
        }

        function method OfNat_any(n: nat, chars: seq<Char>): (str: String)
          requires |chars| > 1
          ensures |str| == Log(|chars|, n) + 1
          ensures forall c: char {:trigger c in chars} {:trigger c in str} | c in str :: c in chars
          decreases n, chars
        {
          var base: int := |chars|;
          if n == 0 then
            reveal Log();
            [chars[0]]
          else
            OfDigits(Digits(n, base), chars)
        }

        predicate method NumberStr(str: String, minus: Char, is_digit: Char -> bool)
          decreases str, minus
        {
          str != [] ==>
            (str[0] == minus || is_digit(str[0])) &&
            forall c: Char {:trigger is_digit(c)} {:trigger c in str[1..]} | c in str[1..] :: 
              is_digit(c)
        }

        function method OfInt_any(n: int, chars: seq<Char>, minus: Char): (str: String)
          requires |chars| > 1
          ensures NumberStr(str, minus, (c: char) => c in chars)
          decreases n, chars, minus
        {
          if n >= 0 then
            OfNat_any(n, chars)
          else
            [minus] + OfNat_any(-n, chars)
        }

        function method ToNat_any(str: String, base: nat, digits: map<Char, nat>): (n: nat)
          requires base > 0
          requires forall c: char {:trigger c in digits} {:trigger c in str} | c in str :: c in digits
          decreases str, base, digits
        {
          if str == [] then
            0
          else
            LemmaMulNonnegativeAuto(); ToNat_any(str[..|str| - 1], base, digits) * base + digits[str[|str| - 1]]
        }

        lemma {:induction false} ToNat_bound(str: String, base: nat, digits: map<Char, nat>)
          requires base > 0
          requires forall c: char {:trigger c in digits} {:trigger c in str} | c in str :: c in digits
          requires forall c: char {:trigger digits[c]} {:trigger c in str} | c in str :: digits[c] < base
          ensures ToNat_any(str, base, digits) < Pow(base, |str|)
          decreases str, base, digits
        {
          if str == [] {
            reveal Pow();
          } else {
            calc <= {
              ToNat_any(str, base, digits);
              ToNat_any(str[..|str| - 1], base, digits) * base + digits[str[|str| - 1]];
              ToNat_any(str[..|str| - 1], base, digits) * base + base - 1;
              {
                ToNat_bound(str[..|str| - 1], base, digits);
                LemmaMulInequalityAuto();
              }
              (Pow(base, |str| - 1) - 1) * base + base - 1;
              {
                LemmaMulIsDistributiveAuto();
              }
              Pow(base, |str| - 1) * base - 1;
              {
                reveal Pow();
                LemmaMulIsCommutativeAuto();
              }
              Pow(base, |str|) - 1;
            }
          }
        }

        function method ToInt_any(str: String, minus: Char, base: nat, digits: map<Char, nat>): (s: int)
          requires base > 0
          requires str != [minus]
          requires NumberStr(str, minus, (c: char) => c in digits)
          decreases str, minus, base, digits
        {
          if [minus] <= str then
            -(ToNat_any(str[1..], base, digits) as int)
          else
            assert str == [] || str == [str[0]] + str[1..]; ToNat_any(str, base, digits)
        }

        import opened Wrappers

        import opened Mul

        import opened DivMod

        import opened Power

        import opened Logarithm

        type String = seq<Char>
      }

      module CharStrEscaping refines ParametricEscaping {
        type Char = char

        function method Escape(str: String, special: set<Char>, escape: Char): String
          decreases str, special, escape
        {
          if str == [] then
            str
          else if str[0] in special then
            [escape, str[0]] + Escape(str[1..], special, escape)
          else
            [str[0]] + Escape(str[1..], special, escape)
        }

        function method Unescape(str: String, escape: Char): Result<String, UnescapeError>
          decreases str, escape
        {
          if str == [] then
            Success(str)
          else if str[0] == escape then
            if |str| > 1 then
              var tl: String :- Unescape(str[2..], escape); Success([str[1]] + tl)
            else
              Failure(EscapeAtEOS)
          else
            var tl: String :- Unescape(str[1..], escape); Success([str[0]] + tl)
        }

        lemma {:induction false} Unescape_Escape(str: String, special: set<Char>, escape: Char)
          requires escape in special
          ensures Unescape(Escape(str, special, escape), escape) == Success(str)
          decreases str, special, escape
        {
          if str == [] {
          } else {
            assert str == [str[0]] + str[1..];
            Unescape_Escape(str[1..], special, escape);
          }
        }

        import opened Wrappers

        type String = seq<Char>

        datatype UnescapeError = EscapeAtEOS
      }
      const HEX_DIGITS: seq<char> := ""0123456789ABCDEF""
      const HEX_TABLE := map['0' := 0, '1' := 1, '2' := 2, '3' := 3, '4' := 4, '5' := 5, '6' := 6, '7' := 7, '8' := 8, '9' := 9, 'a' := 10, 'b' := 11, 'c' := 12, 'd' := 13, 'e' := 14, 'f' := 15, 'A' := 10, 'B' := 11, 'C' := 12, 'D' := 13, 'E' := 14, 'F' := 15]

      function method OfNat(n: nat, base: int := 10): (str: string)
        requires 2 <= base <= 16
        ensures |str| == Log(base, n) + 1
        ensures forall c: char {:trigger c in HEX_DIGITS[..base]} {:trigger c in str} | c in str :: c in HEX_DIGITS[..base]
        decreases n, base
      {
        CharStrConversion.OfNat_any(n, HEX_DIGITS[..base])
      }

      function method OfInt(n: int, base: int := 10): (str: string)
        requires 2 <= base <= 16
        ensures CharStrConversion.NumberStr(str, '-', (c: char) => c in HEX_DIGITS[..base])
        decreases n, base
      {
        CharStrConversion.OfInt_any(n, HEX_DIGITS[..base], '-')
      }

      function method ToNat(str: string, base: int := 10): (n: nat)
        requires 2 <= base <= 16
        requires forall c: char {:trigger HEX_TABLE[c]} {:trigger c in HEX_TABLE} {:trigger c in str} | c in str :: c in HEX_TABLE && HEX_TABLE[c] as int < base
        ensures n < Pow(base, |str|)
        decreases str, base
      {
        CharStrConversion.ToNat_bound(str, base, HEX_TABLE);
        CharStrConversion.ToNat_any(str, base, HEX_TABLE)
      }

      function method ToInt(str: string, base: int := 10): (n: int)
        requires str != ""-""
        requires 2 <= base <= 16
        requires CharStrConversion.NumberStr(str, '-', (c: char) => c in HEX_TABLE && HEX_TABLE[c] as int < base)
        decreases str, base
      {
        CharStrConversion.ToInt_any(str, '-', base, HEX_TABLE)
      }

      function method EscapeQuotes(str: string): string
        decreases str
      {
        CharStrEscaping.Escape(str, {'\""', '\''}, '\\')
      }

      function method UnescapeQuotes(str: string): Result<string, CharStrEscaping.UnescapeError>
        decreases str
      {
        CharStrEscaping.Unescape(str, '\\')
      }

      method Test()
      {
        expect OfInt(0, 10) == ""0"", ""expectation violation""
        expect OfInt(3, 10) == ""3"", ""expectation violation""
        expect OfInt(302, 10) == ""302"", ""expectation violation""
        expect OfInt(-3, 10) == ""-3"", ""expectation violation""
        expect OfInt(-302, 10) == ""-302"", ""expectation violation""
      }

      function method OfBool(b: bool): string
        decreases b
      {
        if b then
          ""true""
        else
          ""false""
      }

      function method OfChar(c: char): string
        decreases c
      {
        [c]
      }

      function method Join(sep: string, strs: seq<string>): string
        decreases sep, strs
      {
        if |strs| == 0 then
          """"
        else if |strs| == 1 then
          strs[0]
        else
          strs[0] + sep + Join(sep, strs[1..])
      }

      function method Concat(strs: seq<string>): string
        decreases strs
      {
        if |strs| == 0 then
          """"
        else
          strs[0] + Concat(strs[1..])
      }

      lemma /*{:_induction strs}*/ Concat_Join(strs: seq<string>)
        ensures Concat(strs) == Join("""", strs)
        decreases strs
      {
      }
    }

    module {:options ""-functionSyntax:4""} Seq {
      lemma Neutral(l: seq)
        ensures l == l + []
        decreases l
      {
      }

      lemma Assoc(a: seq, b: seq, c: seq)
        ensures a + b + c == a + (b + c)
        decreases a, b, c
      {
      }

      lemma Assoc'(a: seq, b: seq, c: seq)
        ensures a + (b + c) == a + b + c
        decreases a, b, c
      {
      }

      lemma Assoc2(a: seq, b: seq, c: seq, d: seq)
        ensures a + b + c + d == a + (b + c + d)
        decreases a, b, c, d
      {
      }
    }

    module {:options ""-functionSyntax:4""} Parsers {

      import opened BoundedInts

      import opened Wrappers

      import opened Core = Views.Core

      import opened Cursors
      type SplitResult<+T, +R> = Result<Split<T>, CursorError<R>>

      type Parser<!T, +R> = p: Parser_<T, R>
        | p.Valid?()
        witness ParserWitness<T, R>()

      datatype Parser_<!T, +R> = Parser(fn: FreshCursor -> SplitResult<T, R>, ghost spec: T -> bytes) {
        predicate Valid?()
          decreases this
        {
          forall cs': FreshCursor {:trigger fn(cs')} :: 
            fn(cs').Success? ==>
              fn(cs').value.StrictlySplitFrom?(cs', spec)
        }
      }

      datatype SubParser_<!T, +R> = SubParser(ghost cs: Cursor, ghost pre: FreshCursor -> bool, fn: FreshCursor --> SplitResult<T, R>, ghost spec: T -> bytes) {
        predicate Valid?()
          decreases this
        {
          (forall cs': FreshCursor {:trigger fn.requires(cs')} {:trigger pre(cs')} | pre(cs') :: 
            fn.requires(cs')) &&
          (forall cs': FreshCursor {:trigger pre(cs')} {:trigger cs'.StrictlySplitFrom?(cs)} | cs'.StrictlySplitFrom?(cs) :: 
            pre(cs')) &&
          forall cs': FreshCursor {:trigger fn(cs')} {:trigger pre(cs')} | pre(cs') :: 
            fn(cs').Success? ==>
              fn(cs').value.StrictlySplitFrom?(cs', spec)
        }
      }

      type SubParser<!T, +R> = p: SubParser_<T, R>
        | p.Valid?()
        witness SubParserWitness<T, R>()

      function method {:opaque} {:fuel 0, 0} ParserWitness<T, R>(): (p: Parser_<T, R>)
        ensures p.Valid?()
      {
        Parser((_ /* _v0 */: FreshCursor) => Failure(EOF), (_ /* _v1 */: T) => [])
      }

      function method {:opaque} {:fuel 0, 0} SubParserWitness<T, R>(): (subp: SubParser_<T, R>)
        ensures subp.Valid?()
      {
        SubParser(Cursor([], 0, 0, 0), (cs: FreshCursor) => false, (cs: FreshCursor) => Failure(EOF), (_ /* _v2 */: T) => [])
      }
    }

    module {:options ""-functionSyntax:4""} Cursors {

      import opened BoundedInts

      import opened Wrappers

      import opened Vs = Views.Core

      import opened Lx = Lexers.Core
      datatype Split<+T> = SP(t: T, cs: FreshCursor) {
        predicate BytesSplitFrom?(cs0: Cursor, spec: T -> bytes)
          decreases this, cs0
        {
          cs0.Bytes() == spec(t) + cs.Bytes()
        }

        predicate SplitFrom?(cs0: Cursor, spec: T -> bytes)
          decreases this, cs0
        {
          cs.SplitFrom?(cs0) &&
          BytesSplitFrom?(cs0, spec)
        }

        predicate StrictlySplitFrom?(cs0: Cursor, spec: T -> bytes)
          decreases this, cs0
        {
          cs.StrictlySplitFrom?(cs0) &&
          BytesSplitFrom?(cs0, spec)
        }
      }

      type Cursor = ps: Cursor_
        | ps.Valid?
        witness Cursor([], 0, 0, 0)

      type FreshCursor = ps: Cursor
        | ps.BOF?
        witness Cursor([], 0, 0, 0)

      datatype CursorError<+R> = EOF | ExpectingByte(expected: byte, b: opt_byte) | ExpectingAnyByte(expected_sq: seq<byte>, b: opt_byte) | OtherError(err: R) {
        function method ToString(pr: R -> string): string
          decreases this
        {
          match this
          case EOF() =>
            ""Reached EOF""
          case ExpectingByte(b0, b) =>
            var c: seq<char> := if b > 0 then ""'"" + [b as char] + ""'"" else ""EOF"";
            ""Expecting '"" + [b0 as char] + ""', read "" + c
          case ExpectingAnyByte(bs0, b) =>
            var c: seq<char> := if b > 0 then ""'"" + [b as char] + ""'"" else ""EOF"";
            var c0s: seq<char> := seq(|bs0|, (idx: int) requires 0 <= idx < |bs0| => bs0[idx] as char);
            ""Expecting one of '"" + c0s + ""', read "" + c
          case OtherError(err) =>
            pr(err)
        }
      }

      type CursorResult<+R> = Result<Cursor, CursorError<R>>

      datatype Cursor_ = Cursor(s: bytes, beg: uint32, point: uint32, end: uint32) {
        ghost const Valid?: bool := 0 <= beg as int <= point as int <= end as int <= |s| < TWO_TO_THE_32
        const BOF? := point == beg
        const EOF? := point == end

        static function method OfView(v: View): FreshCursor
          decreases v
        {
          Cursor(v.s, v.beg, v.beg, v.end)
        }

        static function method OfBytes(bs: bytes): FreshCursor
          requires |bs| < TWO_TO_THE_32
          decreases bs
        {
          Cursor(bs, 0, 0, |bs| as uint32)
        }

        function method Bytes(): bytes
          requires Valid?
          decreases this
        {
          s[beg .. end]
        }

        predicate StrictlyAdvancedFrom?(other: Cursor): (b: bool)
          requires Valid?
          ensures b ==> SuffixLength() < other.SuffixLength()
          ensures b ==> beg == other.beg && end == other.end ==> forall idx: uint32 {:trigger other.s[idx]} {:trigger s[idx]} | beg <= idx < point :: s[idx] == other.s[idx]
          decreases this, other
        {
          s == other.s &&
          beg == other.beg &&
          end == other.end &&
          point > other.point
        }

        predicate AdvancedFrom?(other: Cursor)
          requires Valid?
          decreases this, other
        {
          this == other || StrictlyAdvancedFrom?(other)
        }

        predicate StrictSuffixOf?(other: Cursor)
          requires Valid?
          ensures StrictSuffixOf?(other) ==> Length() < other.Length()
          decreases this, other
        {
          s == other.s &&
          beg > other.beg &&
          end == other.end
        }

        predicate SuffixOf?(other: Cursor)
          requires Valid?
          decreases this, other
        {
          this == other || StrictSuffixOf?(other)
        }

        predicate StrictlySplitFrom?(other: Cursor)
          requires Valid?
          decreases this, other
        {
          BOF? &&
          StrictSuffixOf?(other)
        }

        predicate SplitFrom?(other: Cursor)
          requires Valid?
          decreases this, other
        {
          this == other || StrictlySplitFrom?(other)
        }

        function method Prefix(): View
          requires Valid?
          decreases this
        {
          View(s, beg, point)
        }

        function method Suffix(): Cursor
          requires Valid?
          decreases this
        {
          this.(beg := point)
        }

        function method Split(): (sp: Split<View>)
          requires Valid?
          ensures sp.SplitFrom?(this, (v: View) => v.Bytes())
          ensures beg != point ==> sp.StrictlySplitFrom?(this, (v: View) => v.Bytes())
          decreases this
        {
          SP(this.Prefix(), this.Suffix())
        }

        function method PrefixLength(): uint32
          requires Valid?
          decreases this
        {
          point - beg
        }

        function method SuffixLength(): uint32
          requires Valid?
          decreases this
        {
          end - point
        }

        function method Length(): uint32
          requires Valid?
          decreases this
        {
          end - beg
        }

        lemma /*{:_induction this}*/ PrefixSuffixLength()
          requires Valid?
          ensures Length() == PrefixLength() + SuffixLength()
          decreases this
        {
        }

        predicate ValidIndex?(idx: uint32)
          decreases this, idx
        {
          beg as int + idx as int < end as int
        }

        function method At(idx: uint32): byte
          requires Valid?
          requires ValidIndex?(idx)
          decreases this, idx
        {
          s[beg + idx]
        }

        predicate ValidSuffixIndex?(idx: uint32)
          decreases this, idx
        {
          point as int + idx as int < end as int
        }

        function method SuffixAt(idx: uint32): byte
          requires Valid?
          requires ValidSuffixIndex?(idx)
          decreases this, idx
        {
          s[point + idx]
        }

        function method Peek(): (r: opt_byte)
          requires Valid?
          ensures r < 0 <==> EOF?
          decreases this
        {
          if EOF? then
            -1
          else
            SuffixAt(0) as opt_byte
        }

        predicate method LookingAt(c: char): (b: bool)
          requires Valid?
          requires c as int < 256
          ensures b <==> !EOF? && SuffixAt(0) == c as byte
          decreases this, c
        {
          Peek() == c as opt_byte
        }

        function method Skip(n: uint32): (ps: Cursor)
          requires Valid?
          requires point as int + n as int <= end as int
          ensures n == 0 ==> ps == this
          ensures n > 0 ==> ps.StrictlyAdvancedFrom?(this)
          decreases this, n
        {
          this.(point := point + n)
        }

        function method Unskip(n: uint32): Cursor
          requires Valid?
          requires beg as int <= point as int - n as int
          decreases this, n
        {
          this.(point := point - n)
        }

        function method Get<R>(err: R): (ppr: CursorResult<R>)
          requires Valid?
          ensures ppr.Success? ==> ppr.value.StrictlyAdvancedFrom?(this)
          decreases this
        {
          if EOF? then
            Failure(OtherError(err))
          else
            Success(Skip(1))
        }

        function method AssertByte<R>(b: byte): (pr: CursorResult<R>)
          requires Valid?
          ensures pr.Success? ==> !EOF?
          ensures pr.Success? ==> s[point] == b
          ensures pr.Success? ==> pr.value.StrictlyAdvancedFrom?(this)
          decreases this, b
        {
          var nxt: opt_byte := Peek();
          if nxt == b as opt_byte then
            Success(Skip(1))
          else
            Failure(ExpectingByte(b, nxt))
        }

        function method {:tailrecursion} AssertBytes<R>(bs: bytes, offset: uint32 := 0): (pr: CursorResult<R>)
          requires Valid?
          requires |bs| < TWO_TO_THE_32
          requires offset <= |bs| as uint32
          requires forall b: uint8 {:trigger b in bs} | b in bs :: b as int < 256
          ensures pr.Success? ==> pr.value.AdvancedFrom?(this)
          ensures pr.Success? && offset < |bs| as uint32 ==> pr.value.StrictlyAdvancedFrom?(this)
          ensures pr.Success? ==> s[point .. pr.value.point] == bs[offset..]
          decreases SuffixLength()
        {
          if offset == |bs| as uint32 then
            Success(this)
          else
            var ps: Cursor :- AssertByte(bs[offset] as byte); ps.AssertBytes(bs, offset + 1)
        }

        function method AssertChar<R>(c0: char): (pr: CursorResult<R>)
          requires Valid?
          requires c0 as int < 256
          ensures pr.Success? ==> pr.value.StrictlyAdvancedFrom?(this)
          decreases this, c0
        {
          AssertByte(c0 as byte)
        }

        function method SkipByte(): (ps: Cursor)
          requires Valid?
          ensures ps.AdvancedFrom?(this)
          ensures !EOF? ==> ps.StrictlyAdvancedFrom?(this)
          decreases SuffixLength()
        {
          if EOF? then
            this
          else
            Skip(1)
        }

        function method SkipIf(p: byte -> bool): (ps: Cursor)
          requires Valid?
          ensures ps.AdvancedFrom?(this)
          ensures !EOF? && p(SuffixAt(0)) ==> ps.StrictlyAdvancedFrom?(this)
          decreases SuffixLength()
        {
          if EOF? || !p(SuffixAt(0)) then
            this
          else
            Skip(1)
        }

        function SkipWhile(p: byte -> bool): (ps: Cursor)
          requires Valid?
          ensures ps.AdvancedFrom?(this)
          ensures forall idx: uint32 {:trigger ps.s[idx]} | point <= idx < ps.point :: p(ps.s[idx])
          decreases SuffixLength()
        {
          if EOF? || !p(SuffixAt(0)) then
            this
          else
            Skip(1).SkipWhile(p)
        } by method {
          var point' := this.point;
          var end := this.end;
          while point' < end && p(this.s[point'])
            invariant this.(point := point').Valid?
            invariant this.(point := point').SkipWhile(p) == this.SkipWhile(p)
            decreases end as int - point' as int
          {
            point' := point' + 1;
          }
          return Cursor(this.s, this.beg, point', this.end);
        }

        function SkipWhileLexer<A, R>(step: Lexer<A, R>, st: A): (pr: CursorResult<R>)
          requires Valid?
          ensures pr.Success? ==> pr.value.AdvancedFrom?(this)
          decreases SuffixLength()
        {
          match step(st, Peek())
          case Accept() =>
            Success(this)
          case Reject(err) =>
            Failure(OtherError(err))
          case Partial(st) =>
            if EOF? then
              Failure(EOF)
            else
              Skip(1).SkipWhileLexer(step, st)
        } by method {
          var point' := point;
          var end := this.end;
          var st' := st;
          while true
            invariant this.(point := point').Valid?
            invariant this.(point := point').SkipWhileLexer(step, st') == this.SkipWhileLexer(step, st)
            decreases this.(point := point').SuffixLength()
          {
            var eof := point' == end;
            var minusone: opt_byte := -1;
            var c := if eof then minusone else this.s[point'] as opt_byte;
            match step(st', c)
            case {:split false} Accept() =>
              return Success(Cursor(this.s, this.beg, point', this.end));
            case {:split false} Reject(err) =>
              return Failure(OtherError(err));
            case {:split false} Partial(st'') =>
              if eof {
                return Failure(EOF);
              } else {
                st' := st'';
                point' := point' + 1;
              }
          }
        }
      }
    }

    module {:options ""-functionSyntax:4""} Lexers {

      module Core {

        import opened Wrappers

        import opened BoundedInts
        datatype LexerResult<+T, +R> = Accept | Reject(err: R) | Partial(st: T)

        type Lexer<!T, +R> = (T, opt_byte) -> LexerResult<T, R>
      }

      module Strings {

        import opened Core

        import opened BoundedInts
        type StringBodyLexerState = bool

        datatype StringLexerState = Start | Body(escaped: bool) | End

        const StringBodyLexerStart: StringBodyLexerState := false

        function method StringBody<R>(escaped: StringBodyLexerState, byte: opt_byte): LexerResult<StringBodyLexerState, R>
          decreases escaped, byte
        {
          if byte == '\\' as opt_byte then
            Partial(!escaped)
          else if byte == '\""' as opt_byte && !escaped then
            Accept
          else
            Partial(false)
        }

        const StringLexerStart: StringLexerState := Start

        function method String(st: StringLexerState, byte: opt_byte): LexerResult<StringLexerState, string>
          decreases st, byte
        {
          match st
          case Start() =>
            if byte == '\""' as opt_byte then
              Partial(Body(false))
            else
              Reject(""String must start with double quote"")
          case End() =>
            Accept
          case Body(escaped) =>
            if byte == '\\' as opt_byte then
              Partial(Body(!escaped))
            else if byte == '\""' as opt_byte && !escaped then
              Partial(End)
            else
              Partial(Body(false))
        }
      }
    }

    module Views {

      module {:options ""-functionSyntax:4""} Core {

        import opened BoundedInts
        type View = v: View_
          | v.Valid?
          witness View([], 0, 0)

        datatype View_ = View(s: bytes, beg: uint32, end: uint32) {
          ghost const Valid?: bool := 0 <= beg as int <= end as int <= |s| < TWO_TO_THE_32
          static const Empty: View := View([], 0, 0)
          const Empty? := beg == end

          function method Length(): uint32
            requires Valid?
            decreases this
          {
            end - beg
          }

          function method Bytes(): bytes
            requires Valid?
            decreases this
          {
            s[beg .. end]
          }

          static function method OfBytes(bs: bytes): (v: View)
            requires |bs| < TWO_TO_THE_32
            ensures v.Bytes() == bs
            decreases bs
          {
            View(bs, 0 as uint32, |bs| as uint32)
          }

          static function method OfString(s: string): bytes
            requires forall c: char {:trigger c in s} | c in s :: c as int < 256
            decreases s
          {
            seq(|s|, (i: int) requires 0 <= i < |s| => assert s[i] in s; s[i] as byte)
          }

          predicate SliceOf?(v': View)
            decreases this, v'
          {
            v'.s == s &&
            v'.beg <= beg &&
            end <= v'.end
          }

          predicate StrictPrefixOf?(v': View)
            decreases this, v'
          {
            v'.s == s &&
            v'.beg == beg &&
            end < v'.end
          }

          predicate StrictSuffixOf?(v': View)
            decreases this, v'
          {
            v'.s == s &&
            v'.beg < beg &&
            end == v'.end
          }

          predicate Byte?(c: byte)
            requires Valid?
            decreases this, c
          {
            Bytes() == [c]
          } by method {
            return Length() == 1 && At(0) == c;
          }

          predicate method Char?(c: char)
            requires Valid?
            requires c as int < 256
            decreases this, c
          {
            Byte?(c as byte)
          }

          predicate ValidIndex?(idx: uint32)
            decreases this, idx
          {
            beg as int + idx as int < end as int
          }

          function method At(idx: uint32): byte
            requires Valid?
            requires ValidIndex?(idx)
            decreases this, idx
          {
            s[beg + idx]
          }

          function method Peek(): (r: opt_byte)
            requires Valid?
            ensures r < 0 <==> Empty?
            decreases this
          {
            if Empty? then
              -1
            else
              At(0) as opt_byte
          }

          method CopyTo(dest: array<byte>, start: uint32 := 0)
            requires Valid?
            requires start as int + Length() as int <= dest.Length
            requires start as int + Length() as int < TWO_TO_THE_32
            modifies dest
            ensures dest[start .. start + Length()] == Bytes()
            ensures dest[start + Length()..] == old(dest[start + Length()..])
            decreases this, dest, start
          {
            for idx: uint32 := 0 to Length()
              invariant dest[start .. start + idx] == Bytes()[..idx]
              invariant dest[start + Length()..] == old(dest[start + Length()..])
            {
              dest[start + idx] := s[beg + idx];
            }
          }
        }

        predicate method Adjacent(lv: View, rv: View)
          decreases lv, rv
        {
          lv.end == rv.beg &&
          lv.s == rv.s
        }

        function method Merge(lv: View, rv: View): (v: View)
          requires Adjacent(lv, rv)
          ensures v.Bytes() == lv.Bytes() + rv.Bytes()
          decreases lv, rv
        {
          lv.(end := rv.end)
        }
      }

      module {:options ""-functionSyntax:4""} Writers {

        import opened BoundedInts

        import opened Wrappers

        import opened Core
        datatype Chain = Empty | Chain(previous: Chain, v: View) {
          function method Length(): nat
            decreases this
          {
            if Empty? then
              0
            else
              previous.Length() + v.Length() as int
          }

          function method Count(): nat
            decreases this
          {
            if Empty? then
              0
            else
              previous.Count() + 1
          }

          function method Bytes(): (bs: bytes)
            ensures |bs| == Length()
            decreases this
          {
            if Empty? then
              []
            else
              previous.Bytes() + v.Bytes()
          }

          function method Append(v': View): (c: Chain)
            ensures c.Bytes() == Bytes() + v'.Bytes()
            decreases this, v'
          {
            if Chain? && Adjacent(v, v') then
              Chain(previous, Merge(v, v'))
            else
              Chain(this, v')
          }

          method {:tailrecursion} CopyTo(dest: array<byte>, end: uint32)
            requires end as int == Length() <= dest.Length
            modifies dest
            ensures dest[..end] == Bytes()
            ensures dest[end..] == old(dest[end..])
            decreases this, dest, end
          {
            if Chain? {
              var end := end - v.Length();
              v.CopyTo(dest, end);
              previous.CopyTo(dest, end);
            }
          }
        }

        type Writer = w: Writer_
          | w.Valid?
          witness Writer(0, Chain.Empty)

        datatype Writer_ = Writer(length: uint32, chain: Chain) {
          static const Empty: Writer := Writer(0, Chain.Empty)
          const Empty? := chain.Empty?
          const Unsaturated? := length != UINT32_MAX

          function Length(): nat
            decreases this
          {
            chain.Length()
          }

          ghost const Valid? := length == if chain.Length() >= TWO_TO_THE_32 then UINT32_MAX else chain.Length() as uint32

          function method Bytes(): (bs: bytes)
            ensures |bs| == Length()
            decreases this
          {
            chain.Bytes()
          }

          static function method SaturatedAddU32(a: uint32, b: uint32): uint32
            decreases a, b
          {
            if a <= UINT32_MAX - b then
              a + b
            else
              UINT32_MAX
          }

          function method {:opaque} {:fuel 0, 0} Append(v': View): (rw: Writer)
            requires Valid?
            ensures rw.Unsaturated? <==> v'.Length() < UINT32_MAX - length
            ensures rw.Bytes() == Bytes() + v'.Bytes()
            decreases this, v'
          {
            Writer(SaturatedAddU32(length, v'.Length()), chain.Append(v'))
          }

          function method Then(fn: Writer ~> Writer): Writer
            requires Valid?
            requires fn.requires(this)
            reads set _x0: Writer, _obj: object? /*{:_reads}*/ {:trigger _obj in fn.reads(_x0)} | _obj in fn.reads(_x0) :: _obj
            decreases set _x0: Writer, _obj: object? /*{:_reads}*/ {:trigger _obj in fn.reads(_x0)} | _obj in fn.reads(_x0) :: _obj, this
          {
            fn(this)
          }

          method {:tailrecursion} CopyTo(dest: array<byte>)
            requires Valid?
            requires Unsaturated?
            requires Length() <= dest.Length
            modifies dest
            ensures dest[..length] == Bytes()
            ensures dest[length..] == old(dest[length..])
            decreases this, dest
          {
            chain.CopyTo(dest, length);
          }

          method ToArray() returns (bs: array<byte>)
            requires Valid?
            requires Unsaturated?
            ensures fresh(bs)
            ensures bs[..] == Bytes()
            decreases this
          {
            bs := new byte[length];
            CopyTo(bs);
          }
        }
      }
    }
  }

  module ZeroCopy {

    module {:options ""-functionSyntax:4""} API {

      import opened BoundedInts

      import opened Wrappers

      import opened Errors

      import Grammar

      import Spec = ConcreteSyntax.Spec

      import Serializer

      import Deserializer
      function method {:opaque} {:fuel 0, 0} Serialize(js: Grammar.JSON): (bs: SerializationResult<seq<byte>>)
        ensures bs == Success(Spec.JSON(js))
        decreases js
      {
        Success(Serializer.Text(js).Bytes())
      }

      method SerializeAlloc(js: Grammar.JSON) returns (bs: SerializationResult<array<byte>>)
        ensures bs.Success? ==> fresh(bs.value)
        ensures bs.Success? ==> bs.value[..] == Spec.JSON(js)
        decreases js
      {
        bs := Serializer.Serialize(js);
      }

      method SerializeInto(js: Grammar.JSON, bs: array<byte>) returns (len: SerializationResult<uint32>)
        modifies bs
        ensures len.Success? ==> len.value as int <= bs.Length
        ensures len.Success? ==> bs[..len.value] == Spec.JSON(js)
        ensures len.Success? ==> bs[len.value..] == old(bs[len.value..])
        ensures len.Failure? ==> unchanged(bs)
        decreases js, bs
      {
        len := Serializer.SerializeTo(js, bs);
      }

      function method {:opaque} {:fuel 0, 0} Deserialize(bs: seq<byte>): (js: DeserializationResult<Grammar.JSON>)
        ensures js.Success? ==> bs == Spec.JSON(js.value)
        decreases bs
      {
        Deserializer.API.OfBytes(bs)
      }
    }

    module {:options ""-functionSyntax:4""} Serializer {

      import opened BoundedInts

      import opened Wrappers

      import opened Seq = Utils.Seq

      import opened Errors

      import Spec = ConcreteSyntax.Spec

      import SpecProperties = ConcreteSyntax.SpecProperties

      import opened Grammar

      import opened Writers = Utils.Views.Writers

      import opened Vs = Utils.Views.Core
      method Serialize(js: JSON) returns (rbs: SerializationResult<array<byte>>)
        ensures rbs.Success? ==> fresh(rbs.value)
        ensures rbs.Success? ==> rbs.value[..] == Spec.JSON(js)
        decreases js
      {
        var writer := Text(js);
        :- Need(writer.Unsaturated?, OutOfMemory);
        var bs := writer.ToArray();
        return Success(bs);
      }

      method SerializeTo(js: JSON, dest: array<byte>) returns (len: SerializationResult<uint32>)
        modifies dest
        ensures len.Success? ==> len.value as int <= dest.Length
        ensures len.Success? ==> dest[..len.value] == Spec.JSON(js)
        ensures len.Success? ==> dest[len.value..] == old(dest[len.value..])
        ensures len.Failure? ==> unchanged(dest)
        decreases js, dest
      {
        var writer := Text(js);
        :- Need(writer.Unsaturated?, OutOfMemory);
        :- Need(writer.length as int <= dest.Length, OutOfMemory);
        writer.CopyTo(dest);
        return Success(writer.length);
      }

      function method {:opaque} {:fuel 0, 0} Text(js: JSON): (wr: Writer)
        ensures wr.Bytes() == Spec.JSON(js)
        decreases js
      {
        JSON(js)
      }

      function method {:opaque} {:fuel 0, 0} JSON(js: JSON, writer: Writer := Writer.Empty): (wr: Writer)
        ensures wr.Bytes() == writer.Bytes() + Spec.JSON(js)
        decreases js, writer
      {
        Seq.Assoc2(writer.Bytes(), js.before.Bytes(), Spec.Value(js.t), js.after.Bytes());
        writer.Append(js.before).Then((wr: Writer) => Value(js.t, wr)).Append(js.after)
      }

      function method {:opaque} {:vcs_split_on_every_assert} {:fuel 0, 0} Value(v: Value, writer: Writer): (wr: Writer)
        ensures wr.Bytes() == writer.Bytes() + Spec.Value(v)
        decreases v, 4
      {
        match v
        case Null(n) =>
          writer.Append(n)
        case Bool(b) =>
          var wr: Writer := writer.Append(b);
          wr
        case String(str) =>
          var wr: Writer := String(str, writer);
          wr
        case Number(num) =>
          assert Grammar.Number(num) == v by {
            Spec.UnfoldValueNumber(v);
          } var wr: Writer := Number(num, writer); wr
        case Object(obj) =>
          assert Grammar.Object(obj) == v; assert Spec.Value(v) == Spec.Object(obj); var wr: Writer := Object(obj, writer); wr
        case Array(arr) =>
          assert Grammar.Array(arr) == v;
          assert Spec.Value(v) == Spec.Array(arr);
          var wr: Writer := Array(arr, writer);
          assert wr.Bytes() == writer.Bytes() + Spec.Value(v);
          wr
      }

      function method {:opaque} {:fuel 0, 0} String(str: jstring, writer: Writer): (wr: Writer)
        ensures wr.Bytes() == writer.Bytes() + Spec.String(str)
        decreases str, 0
      {
        writer.Append(str.lq).Append(str.contents).Append(str.rq)
      }

      function method {:opaque} {:fuel 0, 0} Number(num: jnumber, writer: Writer): (wr: Writer)
        ensures wr.Bytes() == writer.Bytes() + Spec.Number(num)
        decreases num, 0
      {
        var wr: Writer := writer.Append(num.minus).Append(num.num);
        var wr: Writer_ := if num.frac.NonEmpty? then wr.Append(num.frac.t.period).Append(num.frac.t.num) else wr;
        assert wr.Bytes() == writer.Bytes() + Spec.View(num.minus) + Spec.View(num.num) + Spec.Maybe(num.frac, Spec.Frac) by {
          assert num.frac.Empty? ==> wr.Bytes() == writer.Bytes() + Spec.View(num.minus) + Spec.View(num.num) + [];
        }
        var wr: Writer_ := if num.exp.NonEmpty? then wr.Append(num.exp.t.e).Append(num.exp.t.sign).Append(num.exp.t.num) else wr;
        assert wr.Bytes() == writer.Bytes() + Spec.View(num.minus) + Spec.View(num.num) + Spec.Maybe(num.frac, Spec.Frac) + Spec.Maybe(num.exp, Spec.Exp) by {
          if num.exp.NonEmpty? {
          } else {
            assert wr.Bytes() == writer.Bytes() + Spec.View(num.minus) + Spec.View(num.num) + Spec.Maybe(num.frac, Spec.Frac);
            assert wr.Bytes() == writer.Bytes() + Spec.View(num.minus) + Spec.View(num.num) + Spec.Maybe(num.frac, Spec.Frac) + [];
          }
        }
        wr
      }

      function method StructuralView(st: Structural<View>, writer: Writer): (wr: Writer)
        ensures wr.Bytes() == writer.Bytes() + Spec.Structural(st, Spec.View)
        decreases st, writer
      {
        writer.Append(st.before).Append(st.t).Append(st.after)
      }

      lemma StructuralViewEns(st: Structural<View>, writer: Writer)
        ensures StructuralView(st, writer).Bytes() == writer.Bytes() + Spec.Structural(st, Spec.View)
        decreases st, writer
      {
      }

      lemma {:axiom} Assume(b: bool)
        ensures b
        decreases b

      lemma /*{:_induction obj}*/ BracketedToObject(obj: jobject)
        ensures Spec.Bracketed(obj, Spec.Member) == Spec.Object(obj)
        decreases obj
      {
      }

      function method {:opaque} {:fuel 0, 0} Object(obj: jobject, writer: Writer): (wr: Writer)
        ensures wr.Bytes() == writer.Bytes() + Spec.Object(obj)
        decreases obj, 3
      {
        var wr: Writer := StructuralView(obj.l, writer);
        StructuralViewEns(obj.l, writer);
        var wr: Writer := Members(obj, wr);
        var wr: Writer := StructuralView(obj.r, wr);
        Seq.Assoc2(writer.Bytes(), Spec.Structural<View>(obj.l, Spec.View), Spec.ConcatBytes(obj.data, Spec.Member), Spec.Structural<View>(obj.r, Spec.View));
        assert wr.Bytes() == writer.Bytes() + Spec.Bracketed(obj, Spec.Member);
        assert Spec.Bracketed(obj, Spec.Member) == Spec.Object(obj) by {
          BracketedToObject(obj);
        }
        wr
      }

      lemma /*{:_induction arr}*/ BracketedToArray(arr: jarray)
        ensures Spec.Bracketed(arr, Spec.Item) == Spec.Array(arr)
        decreases arr
      {
      }

      function method {:opaque} {:fuel 0, 0} Array(arr: jarray, writer: Writer): (wr: Writer)
        ensures wr.Bytes() == writer.Bytes() + Spec.Array(arr)
        decreases arr, 3
      {
        var wr: Writer := StructuralView(arr.l, writer);
        StructuralViewEns(arr.l, writer);
        var wr: Writer := Items(arr, wr);
        var wr: Writer := StructuralView(arr.r, wr);
        Seq.Assoc2(writer.Bytes(), Spec.Structural<View>(arr.l, Spec.View), Spec.ConcatBytes(arr.data, Spec.Item), Spec.Structural<View>(arr.r, Spec.View));
        assert wr.Bytes() == writer.Bytes() + Spec.Bracketed(arr, Spec.Item);
        assert Spec.Bracketed(arr, Spec.Item) == Spec.Array(arr) by {
          BracketedToArray(arr);
        }
        wr
      }

      function {:opaque} {:fuel 0, 0} Members(obj: jobject, writer: Writer): (wr: Writer)
        ensures wr.Bytes() == writer.Bytes() + Spec.ConcatBytes(obj.data, Spec.Member)
        decreases obj, 2
      {
        MembersSpec(obj, obj.data, writer)
      } by method {
        wr := MembersImpl(obj, writer);
        Assume(false);
      }

      function {:opaque} {:fuel 0, 0} Items(arr: jarray, writer: Writer): (wr: Writer)
        ensures wr.Bytes() == writer.Bytes() + Spec.ConcatBytes(arr.data, Spec.Item)
        decreases arr, 2
      {
        ItemsSpec(arr, arr.data, writer)
      } by method {
        wr := ItemsImpl(arr, writer);
        Assume(false);
      }

      function MembersSpec(obj: jobject, members: seq<jmember>, writer: Writer): (wr: Writer)
        requires forall j: int {:trigger members[j]} | 0 <= j < |members| :: members[j] < obj
        ensures wr.Bytes() == writer.Bytes() + Spec.ConcatBytes(members, Spec.Member)
        decreases obj, 1, members
      {
        if members == [] then
          writer
        else
          ghost var butLast: seq<Suffixed<jKeyValue, jcomma>>, last: Suffixed<jKeyValue, jcomma> := members[..|members| - 1], members[|members| - 1]; assert members == butLast + [last]; ghost var wr: Writer := MembersSpec(obj, butLast, writer); ghost var wr: Writer := Member(obj, last, wr); assert wr.Bytes() == writer.Bytes() + (Spec.ConcatBytes(butLast, Spec.Member) + Spec.ConcatBytes([last], Spec.Member)) by {
    Seq.Assoc(writer.Bytes(), Spec.ConcatBytes(butLast, Spec.Member), Spec.ConcatBytes([last], Spec.Member));
  } SpecProperties.ConcatBytes_Linear(butLast, [last], Spec.Member); wr
      }

      function SequenceSpec<T>(v: Value, items: seq<T>, spec: T -> bytes, impl: (Value, T, Writer) --> Writer, writer: Writer): (wr: Writer)
        requires forall item: T, wr: Writer {:trigger impl.requires(v, item, wr)} | item in items :: impl.requires(v, item, wr)
        requires forall item: T, wr: Writer {:trigger wr.Bytes() + spec(item)} {:trigger impl(v, item, wr)} | item in items :: impl(v, item, wr).Bytes() == wr.Bytes() + spec(item)
        ensures wr.Bytes() == writer.Bytes() + Spec.ConcatBytes(items, spec)
        decreases v, 1, items
      {
        if items == [] then
          writer
        else
          ghost var writer: Writer := SequenceSpec(v, items[..|items| - 1], spec, impl, writer); assert items == items[..|items| - 1] + [items[|items| - 1]]; SpecProperties.ConcatBytes_Linear(items[..|items| - 1], [items[|items| - 1]], spec); impl(v, items[|items| - 1], writer)
      }

      function ItemsSpec(arr: jarray, items: seq<jitem>, writer: Writer): (wr: Writer)
        requires forall j: int {:trigger items[j]} | 0 <= j < |items| :: items[j] < arr
        ensures wr.Bytes() == writer.Bytes() + Spec.ConcatBytes(items, Spec.Item)
        decreases arr, 1, items
      {
        if items == [] then
          writer
        else
          ghost var butLast: seq<Suffixed<Value, jcomma>>, last: Suffixed<Value, jcomma> := items[..|items| - 1], items[|items| - 1]; assert items == butLast + [last]; ghost var wr: Writer := ItemsSpec(arr, butLast, writer); ghost var wr: Writer := Item(arr, last, wr); assert wr.Bytes() == writer.Bytes() + (Spec.ConcatBytes(butLast, Spec.Item) + Spec.ConcatBytes([last], Spec.Item)) by {
    Seq.Assoc(writer.Bytes(), Spec.ConcatBytes(butLast, Spec.Item), Spec.ConcatBytes([last], Spec.Item));
  } SpecProperties.ConcatBytes_Linear(butLast, [last], Spec.Item); wr
      }

      method MembersImpl(obj: jobject, writer: Writer) returns (wr: Writer)
        ensures wr == MembersSpec(obj, obj.data, writer)
        decreases obj, 1
      {
        wr := writer;
        var members := obj.data;
        assert wr == MembersSpec(obj, members[..0], writer);
        for i: int := 0 to |members|
          invariant wr == MembersSpec(obj, members[..i], writer)
        {
          assert members[..i + 1][..i] == members[..i];
          wr := Member(obj, members[i], wr);
        }
        assert members[..|members|] == members;
        assert wr == MembersSpec(obj, members, writer);
      }

      method ItemsImpl(arr: jarray, writer: Writer) returns (wr: Writer)
        ensures wr == ItemsSpec(arr, arr.data, writer)
        decreases arr, 1
      {
        wr := writer;
        var items := arr.data;
        assert wr == ItemsSpec(arr, items[..0], writer);
        for i: int := 0 to |items|
          invariant wr == ItemsSpec(arr, items[..i], writer)
        {
          assert items[..i + 1][..i] == items[..i];
          wr := Item(arr, items[i], wr);
        }
        assert items[..|items|] == items;
      }

      function method {:opaque} {:fuel 0, 0} Member(ghost obj: jobject, m: jmember, writer: Writer): (wr: Writer)
        requires m < obj
        ensures wr.Bytes() == writer.Bytes() + Spec.Member(m)
        decreases obj, 0
      {
        var wr: Writer := String(m.t.k, writer);
        var wr: Writer := StructuralView(m.t.colon, wr);
        var wr: Writer := Value(m.t.v, wr);
        assert wr.Bytes() == writer.Bytes() + (Spec.String(m.t.k) + Spec.Structural<View>(m.t.colon, Spec.View) + Spec.Value(m.t.v)) by {
          Seq.Assoc2(writer.Bytes(), Spec.String(m.t.k), Spec.Structural<View>(m.t.colon, Spec.View), Spec.Value(m.t.v));
        }
        var wr: Writer_ := if m.suffix.Empty? then wr else StructuralView(m.suffix.t, wr);
        assert wr.Bytes() == writer.Bytes() + Spec.KeyValue(m.t) + Spec.CommaSuffix(m.suffix) by {
          if m.suffix.Empty? {
            Neutral(Spec.KeyValue(m.t));
            Seq.Assoc'(writer.Bytes(), Spec.KeyValue(m.t), []);
          } else {
            assert Spec.StructuralView(m.suffix.t) == Spec.CommaSuffix(m.suffix);
          }
        }
        assert wr.Bytes() == writer.Bytes() + (Spec.KeyValue(m.t) + Spec.CommaSuffix(m.suffix)) by {
          Seq.Assoc(writer.Bytes(), Spec.KeyValue(m.t), Spec.CommaSuffix(m.suffix));
        }
        wr
      }

      function method {:opaque} {:fuel 0, 0} Item(ghost arr: jarray, m: jitem, writer: Writer): (wr: Writer)
        requires m < arr
        ensures wr.Bytes() == writer.Bytes() + Spec.Item(m)
        decreases arr, 0
      {
        var wr: Writer := Value(m.t, writer);
        var wr: Writer_ := if m.suffix.Empty? then wr else StructuralView(m.suffix.t, wr);
        assert wr.Bytes() == writer.Bytes() + (Spec.Value(m.t) + Spec.CommaSuffix(m.suffix)) by {
          Seq.Assoc(writer.Bytes(), Spec.Value(m.t), Spec.CommaSuffix(m.suffix));
        }
        wr
      }
    }

    module {:options ""-functionSyntax:4""} Deserializer {

      module Core {

        import opened BoundedInts

        import opened Wrappers

        import Spec = ConcreteSyntax.Spec

        import Vs = Utils.Views.Core

        import opened Cursors = Utils.Cursors

        import opened Parsers = Utils.Parsers

        import opened Grammar

        import Errors

        import opened Seq = Utils.Seq
        type JSONError = Errors.DeserializationError

        type Error = CursorError<JSONError>

        type ParseResult<+T> = SplitResult<T, JSONError>

        type Parser<!T> = Parsers.Parser<T, JSONError>

        type SubParser<!T> = Parsers.SubParser<T, JSONError>

        type jopt = v: Vs.View
          | v.Length() <= 1
          witness Vs.View.OfBytes([])

        type ValueParser = sp: SubParser<Value>
          | forall t: Value :: sp.spec(t) == Spec.Value(t)
          witness *

        const SpecView := (v: Vs.View) => Spec.View(v)

        function method {:opaque} {:fuel 0, 0} Get(cs: FreshCursor, err: JSONError): (pr: ParseResult<jchar>)
          ensures pr.Success? ==> pr.value.StrictlySplitFrom?(cs, SpecView)
          decreases cs, err
        {
          var cs: Cursor :- cs.Get(err); Success(cs.Split())
        }

        function {:opaque} {:fuel 0, 0} WS(cs: FreshCursor): (sp: Split<jblanks>)
          ensures sp.SplitFrom?(cs, SpecView)
          decreases cs
        {
          cs.SkipWhile(Blank?).Split()
        } by method {
          reveal WS();
          var point' := cs.point;
          var end := cs.end;
          while point' < end && Blank?(cs.s[point'])
            invariant cs.(point := point').Valid?
            invariant cs.(point := point').SkipWhile(Blank?) == cs.SkipWhile(Blank?)
            decreases end as int - point' as int
          {
            point' := point' + 1;
          }
          return Cursor(cs.s, cs.beg, point', cs.end).Split();
        }

        function method {:opaque} {:fuel 0, 0} Structural<T>(cs: FreshCursor, parser: Parser<T>): (pr: ParseResult<Structural<T>>)
          requires forall cs: FreshCursor {:trigger parser.fn.requires(cs)} :: parser.fn.requires(cs)
          ensures pr.Success? ==> pr.value.StrictlySplitFrom?(cs, (st: Structural<T>) => Spec.Structural(st, parser.spec))
          decreases cs, parser
        {
          var SP(before: jblanks, cs: FreshCursor) := WS(cs);
          var SP(val: T, cs: FreshCursor) :- parser.fn(cs); var SP(after: jblanks, cs: FreshCursor) := WS(cs); Success(SP(Grammar.Structural(before, val, after), cs))
        }

        function method {:opaque} {:fuel 0, 0} TryStructural(cs: FreshCursor): (sp: Split<Structural<jopt>>)
          ensures sp.SplitFrom?(cs, (st: Structural<jopt>) => Spec.Structural(st, SpecView))
          decreases cs
        {
          var SP(before: jblanks, cs: FreshCursor) := WS(cs);
          var SP(val: View, cs: FreshCursor) := cs.SkipByte().Split();
          var SP(after: jblanks, cs: FreshCursor) := WS(cs);
          SP(Grammar.Structural(before, val, after), cs)
        }
      }
      type Error = Core.Error

      abstract module SequenceParams {

        import opened BoundedInts

        import opened Grammar

        import opened Cursors = Utils.Cursors

        import opened Core
        type TElement

        const OPEN: byte
        const CLOSE: byte

        function ElementSpec(t: TElement): bytes

        function method Element(cs: FreshCursor, json: ValueParser): (pr: ParseResult<TElement>)
          requires cs.StrictlySplitFrom?(json.cs)
          ensures pr.Success? ==> pr.value.StrictlySplitFrom?(cs, ElementSpec)
          decreases cs.Length()
      }

      abstract module Sequences {

        import opened Wrappers

        import opened BoundedInts

        import opened Params : SequenceParams

        import SpecProperties = ConcreteSyntax.SpecProperties

        import opened Vs = Utils.Views.Core

        import opened Grammar

        import opened Cursors = Utils.Cursors

        import Parsers = Utils.Parsers

        import opened Core
        type jopen = v: Vs.View
          | v.Byte?(OPEN)
          witness Vs.View.OfBytes([OPEN])

        type jclose = v: Vs.View
          | v.Byte?(CLOSE)
          witness Vs.View.OfBytes([CLOSE])

        type TBracketed = Bracketed<jopen, TElement, jcomma, jclose>

        type TSuffixedElement = Suffixed<TElement, jcomma>

        const SEPARATOR: byte := ',' as byte

        function SuffixedElementSpec(e: TSuffixedElement): bytes
          decreases e
        {
          ElementSpec(e.t) + Spec.CommaSuffix(e.suffix)
        }

        function BracketedSpec(ts: TBracketed): bytes
          decreases ts
        {
          Spec.Bracketed(ts, SuffixedElementSpec)
        }

        function SuffixedElementsSpec(ts: seq<TSuffixedElement>): bytes
          decreases ts
        {
          Spec.ConcatBytes(ts, SuffixedElementSpec)
        }

        function method {:opaque} {:fuel 0, 0} Open(cs: FreshCursor): (pr: ParseResult<jopen>)
          ensures pr.Success? ==> pr.value.StrictlySplitFrom?(cs, (_ /* _v0 */: View_) => [OPEN])
          decreases cs
        {
          var cs: Cursor :- cs.AssertByte(OPEN); Success(cs.Split())
        }

        function method {:opaque} {:fuel 0, 0} Close(cs: FreshCursor): (pr: ParseResult<jclose>)
          ensures pr.Success? ==> pr.value.StrictlySplitFrom?(cs, (_ /* _v1 */: View_) => [CLOSE])
          decreases cs
        {
          var cs: Cursor :- cs.AssertByte(CLOSE); Success(cs.Split())
        }

        function method {:opaque} {:fuel 0, 0} BracketedFromParts(ghost cs: Cursor, open: Split<Structural<jopen>>, elems: Split<seq<TSuffixedElement>>, close: Split<Structural<jclose>>): (sp: Split<TBracketed>)
          requires Grammar.NoTrailingSuffix(elems.t)
          requires open.StrictlySplitFrom?(cs, (c: Structural<jopen>) => Spec.Structural(c, SpecView))
          requires elems.SplitFrom?(open.cs, SuffixedElementsSpec)
          requires close.StrictlySplitFrom?(elems.cs, (c: Structural<jclose>) => Spec.Structural(c, SpecView))
          ensures sp.StrictlySplitFrom?(cs, BracketedSpec)
          decreases cs, open, elems, close
        {
          var sp: Split<Bracketed<jopen, TElement, jcomma, jclose>> := SP(Grammar.Bracketed(open.t, elems.t, close.t), close.cs);
          calc {
            cs.Bytes();
            Spec.Structural(open.t, SpecView) + open.cs.Bytes();
            {
              assert open.cs.Bytes() == SuffixedElementsSpec(elems.t) + elems.cs.Bytes();
            }
            Spec.Structural(open.t, SpecView) + (SuffixedElementsSpec(elems.t) + elems.cs.Bytes());
            {
              Seq.Assoc'(Spec.Structural(open.t, SpecView), SuffixedElementsSpec(elems.t), elems.cs.Bytes());
            }
            Spec.Structural(open.t, SpecView) + SuffixedElementsSpec(elems.t) + elems.cs.Bytes();
            {
              assert elems.cs.Bytes() == Spec.Structural(close.t, SpecView) + close.cs.Bytes();
            }
            Spec.Structural(open.t, SpecView) + SuffixedElementsSpec(elems.t) + (Spec.Structural(close.t, SpecView) + close.cs.Bytes());
            {
              Seq.Assoc'(Spec.Structural(open.t, SpecView) + SuffixedElementsSpec(elems.t), Spec.Structural(close.t, SpecView), close.cs.Bytes());
            }
            Spec.Structural(open.t, SpecView) + SuffixedElementsSpec(elems.t) + Spec.Structural(close.t, SpecView) + close.cs.Bytes();
            Spec.Bracketed(sp.t, SuffixedElementSpec) + close.cs.Bytes();
          }
          assert sp.StrictlySplitFrom?(cs, BracketedSpec);
          sp
        }

        function method {:opaque} {:fuel 0, 0} AppendWithSuffix(ghost cs0: FreshCursor, ghost json: ValueParser, elems: Split<seq<TSuffixedElement>>, elem: Split<TElement>, sep: Split<Structural<jcomma>>): (elems': Split<seq<TSuffixedElement>>)
          requires elems.cs.StrictlySplitFrom?(json.cs)
          requires elems.SplitFrom?(cs0, SuffixedElementsSpec)
          requires elem.StrictlySplitFrom?(elems.cs, ElementSpec)
          requires sep.StrictlySplitFrom?(elem.cs, (c: Structural<jcomma>) => Spec.Structural(c, SpecView))
          requires forall e: Suffixed<TElement, jcomma> {:trigger e.suffix} {:trigger e in elems.t} | e in elems.t :: e.suffix.NonEmpty?
          ensures elems'.StrictlySplitFrom?(cs0, SuffixedElementsSpec)
          ensures forall e: Suffixed<TElement, jcomma> {:trigger e.suffix} {:trigger e in elems'.t} | e in elems'.t :: e.suffix.NonEmpty?
          ensures elems'.cs.Length() < elems.cs.Length()
          ensures elems'.cs.StrictlySplitFrom?(json.cs)
          decreases cs0, json, elems, elem, sep
        {
          var suffixed: Suffixed<TElement, jcomma> := Suffixed(elem.t, NonEmpty(sep.t));
          var elems': Split<seq<Suffixed<TElement, jcomma>>> := SP(elems.t + [suffixed], sep.cs);
          assert cs0.Bytes() == SuffixedElementsSpec(elems'.t) + sep.cs.Bytes() by {
            assert {:focus} cs0.Bytes() == SuffixedElementsSpec(elems.t) + (ElementSpec(suffixed.t) + Spec.CommaSuffix(suffixed.suffix)) + sep.cs.Bytes() by {
              assert cs0.Bytes() == SuffixedElementsSpec(elems.t) + ElementSpec(suffixed.t) + Spec.CommaSuffix(suffixed.suffix) + sep.cs.Bytes() by {
                assert cs0.Bytes() == SuffixedElementsSpec(elems.t) + elems.cs.Bytes();
                assert elems.cs.Bytes() == ElementSpec(suffixed.t) + elem.cs.Bytes();
                assert elem.cs.Bytes() == Spec.CommaSuffix(suffixed.suffix) + sep.cs.Bytes();
                Seq.Assoc'(SuffixedElementsSpec(elems.t), ElementSpec(suffixed.t), elem.cs.Bytes());
                Seq.Assoc'(SuffixedElementsSpec(elems.t) + ElementSpec(suffixed.t), Spec.CommaSuffix(suffixed.suffix), sep.cs.Bytes());
              }
              Seq.Assoc(SuffixedElementsSpec(elems.t), ElementSpec(suffixed.t), Spec.CommaSuffix(suffixed.suffix));
            }
            assert SuffixedElementsSpec(elems.t) + (ElementSpec(suffixed.t) + Spec.CommaSuffix(suffixed.suffix)) + sep.cs.Bytes() == SuffixedElementsSpec(elems'.t) + sep.cs.Bytes() by {
              assert SuffixedElementsSpec(elems.t) + SuffixedElementSpec(suffixed) == SuffixedElementsSpec(elems.t + [suffixed]) by {
                SpecProperties.ConcatBytes_Linear(elems.t, [suffixed], SuffixedElementSpec);
                assert Spec.ConcatBytes(elems.t, SuffixedElementSpec) + Spec.ConcatBytes([suffixed], SuffixedElementSpec) == Spec.ConcatBytes(elems.t + [suffixed], SuffixedElementSpec);
              }
            }
          }
          assert elems'.StrictlySplitFrom?(cs0, SuffixedElementsSpec);
          assert forall e: Suffixed<TElement, jcomma> {:trigger e.suffix} {:trigger e in elems'.t} | e in elems'.t :: e.suffix.NonEmpty? by {
            assert elems'.t == elems.t + [suffixed];
          }
          assert {:split_here} elems'.cs.Length() < elems.cs.Length();
          elems'
        }

        function method {:opaque} {:fuel 0, 0} AppendLast(ghost cs0: FreshCursor, ghost json: ValueParser, elems: Split<seq<TSuffixedElement>>, elem: Split<TElement>, sep: Split<Structural<jclose>>): (elems': Split<seq<TSuffixedElement>>)
          requires elems.cs.StrictlySplitFrom?(json.cs)
          requires elems.SplitFrom?(cs0, SuffixedElementsSpec)
          requires elem.StrictlySplitFrom?(elems.cs, ElementSpec)
          requires sep.StrictlySplitFrom?(elem.cs, (c: Structural<jclose>) => Spec.Structural(c, SpecView))
          requires forall e: Suffixed<TElement, jcomma> {:trigger e.suffix} {:trigger e in elems.t} | e in elems.t :: e.suffix.NonEmpty?
          ensures elems'.StrictlySplitFrom?(cs0, SuffixedElementsSpec)
          ensures NoTrailingSuffix(elems'.t)
          ensures elems'.cs.Length() < elems.cs.Length()
          ensures elems'.cs.StrictlySplitFrom?(json.cs)
          ensures sep.StrictlySplitFrom?(elems'.cs, (c: Structural<jclose>) => Spec.Structural(c, SpecView))
          decreases cs0, json, elems, elem, sep
        {
          var suffixed: Suffixed<TElement, jcomma> := Suffixed(elem.t, Empty());
          var elems': Split<seq<Suffixed<TElement, jcomma>>> := SP(elems.t + [suffixed], elem.cs);
          assert cs0.Bytes() == SuffixedElementsSpec(elems'.t) + elem.cs.Bytes() by {
            assert cs0.Bytes() == SuffixedElementsSpec(elems.t) + ElementSpec(suffixed.t) + elem.cs.Bytes() by {
              assert elem.t == suffixed.t;
            }
            assert SuffixedElementsSpec(elems.t) + ElementSpec(suffixed.t) + elem.cs.Bytes() == SuffixedElementsSpec(elems'.t) + elem.cs.Bytes() by {
              assert SuffixedElementsSpec(elems.t) + SuffixedElementSpec(suffixed) == SuffixedElementsSpec(elems.t + [suffixed]) by {
                SpecProperties.ConcatBytes_Linear(elems.t, [suffixed], SuffixedElementSpec);
                assert Spec.ConcatBytes(elems.t, SuffixedElementSpec) + Spec.ConcatBytes([suffixed], SuffixedElementSpec) == Spec.ConcatBytes(elems.t + [suffixed], SuffixedElementSpec);
              }
            }
          }
          assert elems'.StrictlySplitFrom?(cs0, SuffixedElementsSpec);
          elems'
        }

        function method {:opaque} {:tailrecursion} {:fuel 0, 0} Elements(ghost cs0: FreshCursor, json: ValueParser, open: Split<Structural<jopen>>, elems: Split<seq<TSuffixedElement>>): (pr: ParseResult<TBracketed>)
          requires open.StrictlySplitFrom?(cs0, (c: Structural<jopen>) => Spec.Structural(c, SpecView))
          requires elems.cs.StrictlySplitFrom?(json.cs)
          requires elems.SplitFrom?(open.cs, SuffixedElementsSpec)
          requires forall e: Suffixed<TElement, jcomma> {:trigger e.suffix} {:trigger e in elems.t} | e in elems.t :: e.suffix.NonEmpty?
          ensures pr.Success? ==> pr.value.StrictlySplitFrom?(cs0, BracketedSpec)
          decreases elems.cs.Length()
        {
          var elem: Split<TElement> :- Element(elems.cs, json); var sep: Split<Structural<jopt>> := Core.TryStructural(elem.cs); var s0: opt_byte := sep.t.t.Peek(); if s0 == SEPARATOR as opt_byte then assert AppendWithSuffix.requires(open.cs, json, elems, elem, sep) by {
    assert {:focus} elems.cs.StrictlySplitFrom?(json.cs);
    assert elems.SplitFrom?(open.cs, SuffixedElementsSpec);
    assert elem.StrictlySplitFrom?(elems.cs, ElementSpec);
    assert sep.StrictlySplitFrom?(elem.cs, (c: Structural<jopt>) => Spec.Structural(c, SpecView));
    assert forall e: Suffixed<TElement, jcomma> {:trigger e.suffix} {:trigger e in elems.t} | e in elems.t :: e.suffix.NonEmpty?;
    assert {:split_here} true;
  } var elems: Split<seq<TSuffixedElement>> := AppendWithSuffix(open.cs, json, elems, elem, sep); Elements(cs0, json, open, elems) else if s0 == CLOSE as opt_byte then assert AppendLast.requires(open.cs, json, elems, elem, sep) by {
    assert sep.StrictlySplitFrom?(elem.cs, (c: Structural<jopt>) => Spec.Structural(c, SpecView));
    assert elems.cs.StrictlySplitFrom?(json.cs);
    assert elems.SplitFrom?(open.cs, SuffixedElementsSpec);
    assert elem.StrictlySplitFrom?(elems.cs, ElementSpec);
  } var elems': Split<seq<TSuffixedElement>> := AppendLast(open.cs, json, elems, elem, sep); assert elems'.SplitFrom?(open.cs, SuffixedElementsSpec) by {
    assert elems'.StrictlySplitFrom?(open.cs, SuffixedElementsSpec);
  } var bracketed: Split<TBracketed> := BracketedFromParts(cs0, open, elems', sep); assert bracketed.StrictlySplitFrom?(cs0, BracketedSpec); Success(bracketed) else var separator: byte := SEPARATOR; var pr: Result<Split<Bracketed<jopen, TElement, jcomma, jclose>>, CursorError<Errors.DeserializationError>> := Failure(ExpectingAnyByte([CLOSE, separator], s0)); pr
        }

        function method {:opaque} {:fuel 0, 0} Bracketed(cs: FreshCursor, json: ValueParser): (pr: ParseResult<TBracketed>)
          requires cs.SplitFrom?(json.cs)
          ensures pr.Success? ==> pr.value.StrictlySplitFrom?(cs, BracketedSpec)
          decreases cs, json
        {
          var open: Split<Structural<jopen>> :- Core.Structural(cs, Parsers.Parser(Open, SpecView)); assert open.cs.StrictlySplitFrom?(json.cs); var elems: Split<seq<Suffixed<TElement, jcomma>>> := SP([], open.cs); if open.cs.Peek() == CLOSE as opt_byte then var close: Split<Structural<jclose>> :- Core.Structural(open.cs, Parsers.Parser(Close, SpecView)); Success(BracketedFromParts(cs, open, elems, close)) else Elements(cs, json, open, elems)
        }

        lemma Valid(x: TBracketed)
          ensures x.l.t.Byte?(OPEN)
          ensures x.r.t.Byte?(CLOSE)
          ensures NoTrailingSuffix(x.data)
          ensures forall pf: Suffixed<TElement, jcomma> {:trigger pf.suffix} {:trigger pf in x.data} | pf in x.data :: pf.suffix.NonEmpty? ==> pf.suffix.t.t.Byte?(SEPARATOR)
          decreases x
        {
        }
      }

      module API {

        import opened BoundedInts

        import opened Wrappers

        import opened Vs = Utils.Views.Core

        import opened Grammar

        import opened Core

        import opened Errors

        import Cursors = Utils.Cursors

        import Values
        function method LiftCursorError(err: Cursors.CursorError<DeserializationError>): DeserializationError
          decreases err
        {
          match err
          case EOF() =>
            ReachedEOF
          case ExpectingByte(expected, b) =>
            ExpectingByte(expected, b)
          case ExpectingAnyByte(expected_sq, b) =>
            ExpectingAnyByte(expected_sq, b)
          case OtherError(err) =>
            err
        }

        function method {:opaque} {:fuel 0, 0} JSON(cs: Cursors.FreshCursor): (pr: DeserializationResult<Cursors.Split<JSON>>)
          ensures pr.Success? ==> pr.value.StrictlySplitFrom?(cs, Spec.JSON)
          decreases cs
        {
          Core.Structural(cs, Parsers.Parser(Values.Value, Spec.Value)).MapFailure(LiftCursorError)
        }

        function method {:opaque} {:fuel 0, 0} Text(v: View): (jsr: DeserializationResult<JSON>)
          ensures jsr.Success? ==> v.Bytes() == Spec.JSON(jsr.value)
          decreases v
        {
          var SP(text: JSON, cs: FreshCursor) :- JSON(Cursors.Cursor.OfView(v)); assert Cursors.SP(text, cs).BytesSplitFrom?(Cursors.Cursor.OfView(v), Spec.JSON); assert v.Bytes() == Spec.JSON(text) + cs.Bytes(); Need(cs.EOF?, Errors.ExpectingEOF); assert cs.Bytes() == []; Success(text)
        }

        function method {:opaque} {:fuel 0, 0} OfBytes(bs: bytes): (jsr: DeserializationResult<JSON>)
          ensures jsr.Success? ==> bs == Spec.JSON(jsr.value)
          decreases bs
        {
          Need(|bs| < TWO_TO_THE_32, Errors.IntOverflow); Text(Vs.View.OfBytes(bs))
        }
      }

      module Values {

        import opened BoundedInts

        import opened Wrappers

        import opened Grammar

        import opened Cursors = Utils.Cursors

        import opened Core

        import Strings

        import Numbers

        import Objects

        import Arrays

        import Constants

        import SpecProperties = ConcreteSyntax.SpecProperties
        function method {:opaque} {:fuel 0, 0} Value(cs: FreshCursor): (pr: ParseResult<Value>)
          ensures pr.Success? ==> pr.value.StrictlySplitFrom?(cs, Spec.Value)
          decreases cs.Length(), 1
        {
          var c: opt_byte := cs.Peek();
          if c == '{' as opt_byte then
            var SP(obj: jobject, cs': FreshCursor) :- Objects.Object(cs, ValueParser(cs)); var v: Value := Grammar.Object(obj); var sp: Split<Value> := SP(v, cs'); assert sp.StrictlySplitFrom?(cs, Spec.Value) by {
    assert SP(obj, cs').StrictlySplitFrom?(cs, Spec.Object);
    Spec.UnfoldValueObject(v);
  } Success(sp)
          else if c == '[' as opt_byte then
            var SP(arr: jarray, cs': FreshCursor) :- Arrays.Array(cs, ValueParser(cs)); var v: Value := Grammar.Array(arr); var sp: Split<Value> := SP(v, cs'); assert sp.StrictlySplitFrom?(cs, Spec.Value) by {
    assert SP(arr, cs').StrictlySplitFrom?(cs, Spec.Array);
    Spec.UnfoldValueArray(v);
  } Success(sp)
          else if c == '\""' as opt_byte then
            var SP(str: jstring, cs: FreshCursor) :- Strings.String(cs); Success(SP(Grammar.String(str), cs))
          else if c == 't' as opt_byte then
            var SP(cst: Vs.View, cs: FreshCursor) :- Constants.Constant(cs, TRUE); Success(SP(Grammar.Bool(cst), cs))
          else if c == 'f' as opt_byte then
            var SP(cst: Vs.View, cs: FreshCursor) :- Constants.Constant(cs, FALSE); Success(SP(Grammar.Bool(cst), cs))
          else if c == 'n' as opt_byte then
            var SP(cst: Vs.View, cs: FreshCursor) :- Constants.Constant(cs, NULL); Success(SP(Grammar.Null(cst), cs))
          else
            var SP(num: jnumber, cs': FreshCursor) :- Numbers.Number(cs); var v: Value := Grammar.Number(num); var sp: Split<Value> := SP(v, cs'); assert sp.StrictlySplitFrom?(cs, Spec.Value) by {
    assert SP(num, cs').StrictlySplitFrom?(cs, Spec.Number);
    Spec.UnfoldValueNumber(v);
  } assert sp.StrictlySplitFrom?(cs, Spec.Value); Success(sp)
        }

        function method {:opaque} {:fuel 0, 0} ValueParser(cs: FreshCursor): (p: ValueParser)
          ensures cs.SplitFrom?(p.cs)
          decreases cs.Length(), 0
        {
          var pre: FreshCursor -> bool := (ps': FreshCursor) => ps'.Length() < cs.Length();
          var fn: FreshCursor --> ParseResult<Value> := (ps': FreshCursor) requires pre(ps') => Value(ps');
          Parsers.SubParser(cs, pre, fn, Spec.Value)
        }
      }

      module Constants {

        import opened BoundedInts

        import opened Wrappers

        import opened Grammar

        import opened Core

        import opened Cursors = Utils.Cursors
        function method {:opaque} {:fuel 0, 0} Constant(cs: FreshCursor, expected: bytes): (pr: ParseResult<Vs.View>)
          requires |expected| < TWO_TO_THE_32
          ensures pr.Success? ==> pr.value.t.Bytes() == expected
          ensures pr.Success? ==> pr.value.SplitFrom?(cs, (_ /* _v2 */: View_) => expected)
          decreases cs, expected
        {
          var cs: Cursor :- cs.AssertBytes(expected); Success(cs.Split())
        }
      }

      module Strings {

        import opened Wrappers

        import opened BoundedInts

        import opened Grammar

        import opened Cursors = Utils.Cursors

        import opened LC = Utils.Lexers.Core

        import opened Strings = Utils.Lexers.Strings

        import opened Parsers = Utils.Parsers

        import opened Core
        function {:opaque} {:fuel 0, 0} StringBody(cs: Cursor): (pr: CursorResult<JSONError>)
          ensures pr.Success? ==> pr.value.AdvancedFrom?(cs)
          decreases cs
        {
          cs.SkipWhileLexer(Strings.StringBody, StringBodyLexerStart)
        } by method {
          reveal StringBody();
          var escaped := false;
          for point': uint32 := cs.point to cs.end
            invariant cs.(point := point').Valid?
            invariant cs.(point := point').SkipWhileLexer(Strings.StringBody, escaped) == StringBody(cs)
          {
            var byte := cs.s[point'];
            if byte == '\""' as byte && !escaped {
              return Success(Cursor(cs.s, cs.beg, point', cs.end));
            } else if byte == '\\' as byte {
              escaped := !escaped;
            } else {
              escaped := false;
            }
          }
          return Failure(EOF);
        }

        function method Quote(cs: FreshCursor): (pr: ParseResult<jquote>)
          ensures pr.Success? ==> pr.value.StrictlySplitFrom?(cs, SpecView)
          decreases cs
        {
          var cs: Cursor :- cs.AssertChar('\""'); Success(cs.Split())
        }

        function method {:opaque} {:fuel 0, 0} String(cs: FreshCursor): (pr: ParseResult<jstring>)
          ensures pr.Success? ==> pr.value.StrictlySplitFrom?(cs, Spec.String)
          decreases cs
        {
          var SP(lq: jquote, cs: FreshCursor) :- Quote(cs); var contents: Cursor :- StringBody(cs); var SP(contents: View, cs: FreshCursor) := contents.Split(); var SP(rq: jquote, cs: FreshCursor) :- Quote(cs); Success(SP(Grammar.JString(lq, contents, rq), cs))
        }
      }

      module Numbers {

        import opened BoundedInts

        import opened Wrappers

        import opened Grammar

        import opened Cursors = Utils.Cursors

        import opened Core
        function method {:opaque} {:fuel 0, 0} Digits(cs: FreshCursor): (sp: Split<jdigits>)
          ensures sp.SplitFrom?(cs, SpecView)
          decreases cs
        {
          cs.SkipWhile(Digit?).Split()
        }

        function method {:opaque} {:fuel 0, 0} NonEmptyDigits(cs: FreshCursor): (pr: ParseResult<jnum>)
          ensures pr.Success? ==> pr.value.StrictlySplitFrom?(cs, SpecView)
          decreases cs
        {
          var sp: Split<jdigits> := Digits(cs);
          Need(!sp.t.Empty?, OtherError(Errors.EmptyNumber)); Success(sp)
        }

        function method {:opaque} {:fuel 0, 0} NonZeroInt(cs: FreshCursor): (pr: ParseResult<jint>)
          requires cs.Peek() != '0' as opt_byte
          ensures pr.Success? ==> pr.value.StrictlySplitFrom?(cs, SpecView)
          decreases cs
        {
          NonEmptyDigits(cs)
        }

        function method {:opaque} {:fuel 0, 0} OptionalMinus(cs: FreshCursor): (sp: Split<jminus>)
          ensures sp.SplitFrom?(cs, SpecView)
          decreases cs
        {
          cs.SkipIf((c: uint8) => c == '-' as byte).Split()
        }

        function method {:opaque} {:fuel 0, 0} OptionalSign(cs: FreshCursor): (sp: Split<jsign>)
          ensures sp.SplitFrom?(cs, SpecView)
          decreases cs
        {
          cs.SkipIf((c: uint8) => c == '-' as byte || c == '+' as byte).Split()
        }

        function method {:opaque} {:fuel 0, 0} TrimmedInt(cs: FreshCursor): (pr: ParseResult<jint>)
          ensures pr.Success? ==> pr.value.StrictlySplitFrom?(cs, SpecView)
          decreases cs
        {
          var sp: Split<View> := cs.SkipIf((c: uint8) => c == '0' as byte).Split();
          if sp.t.Empty? then
            NonZeroInt(sp.cs)
          else
            Success(sp)
        }

        function method {:opaque} {:vcs_split_on_every_assert} {:fuel 0, 0} Exp(cs: FreshCursor): (pr: ParseResult<Maybe<jexp>>)
          ensures pr.Success? ==> pr.value.SplitFrom?(cs, (exp: Maybe<jexp>) => Spec.Maybe(exp, Spec.Exp))
          decreases cs
        {
          var SP(e: View, cs: FreshCursor) := cs.SkipIf((c: uint8) => c == 'e' as byte || c == 'E' as byte).Split();
          if e.Empty? then
            Success(SP(Empty(), cs))
          else
            assert e.Char?('e') || e.Char?('E'); var SP(sign: jsign, cs: FreshCursor) := OptionalSign(cs); var SP(num: jnum, cs: FreshCursor) :- NonEmptyDigits(cs); Success(SP(NonEmpty(JExp(e, sign, num)), cs))
        }

        function method {:opaque} {:fuel 0, 0} Frac(cs: FreshCursor): (pr: ParseResult<Maybe<jfrac>>)
          ensures pr.Success? ==> pr.value.SplitFrom?(cs, (frac: Maybe<jfrac>) => Spec.Maybe(frac, Spec.Frac))
          decreases cs
        {
          var SP(period: View, cs: FreshCursor) := cs.SkipIf((c: uint8) => c == '.' as byte).Split();
          if period.Empty? then
            Success(SP(Empty(), cs))
          else
            var SP(num: jnum, cs: FreshCursor) :- NonEmptyDigits(cs); Success(SP(NonEmpty(JFrac(period, num)), cs))
        }

        function method {:opaque} {:fuel 0, 0} NumberFromParts(ghost cs: Cursor, minus: Split<jminus>, num: Split<jint>, frac: Split<Maybe<jfrac>>, exp: Split<Maybe<jexp>>): (sp: Split<jnumber>)
          requires minus.SplitFrom?(cs, SpecView)
          requires num.StrictlySplitFrom?(minus.cs, SpecView)
          requires frac.SplitFrom?(num.cs, (frac: Maybe<jfrac>) => Spec.Maybe(frac, Spec.Frac))
          requires exp.SplitFrom?(frac.cs, (exp: Maybe<jexp>) => Spec.Maybe(exp, Spec.Exp))
          ensures sp.StrictlySplitFrom?(cs, Spec.Number)
          decreases cs, minus, num, frac, exp
        {
          var sp: Split<jnumber> := SP(Grammar.JNumber(minus.t, num.t, frac.t, exp.t), exp.cs);
          assert cs.Bytes() == Spec.Number(sp.t) + exp.cs.Bytes() by {
            assert cs.Bytes() == Spec.View(minus.t) + Spec.View(num.t) + Spec.Maybe(frac.t, Spec.Frac) + Spec.Maybe(exp.t, Spec.Exp) + exp.cs.Bytes() by {
              assert cs.Bytes() == Spec.View(minus.t) + minus.cs.Bytes();
              assert minus.cs.Bytes() == Spec.View(num.t) + num.cs.Bytes();
              assert num.cs.Bytes() == Spec.Maybe(frac.t, Spec.Frac) + frac.cs.Bytes();
              assert frac.cs.Bytes() == Spec.Maybe(exp.t, Spec.Exp) + exp.cs.Bytes();
              Seq.Assoc'(Spec.View(minus.t), Spec.View(num.t), num.cs.Bytes());
              Seq.Assoc'(Spec.View(minus.t) + Spec.View(num.t), Spec.Maybe(frac.t, Spec.Frac), frac.cs.Bytes());
              Seq.Assoc'(Spec.View(minus.t) + Spec.View(num.t) + Spec.Maybe(frac.t, Spec.Frac), Spec.Maybe(exp.t, Spec.Exp), exp.cs.Bytes());
            }
          }
          assert sp.StrictlySplitFrom?(cs, Spec.Number);
          sp
        }

        function method {:opaque} {:fuel 0, 0} Number(cs: FreshCursor): (pr: ParseResult<jnumber>)
          ensures pr.Success? ==> pr.value.StrictlySplitFrom?(cs, Spec.Number)
          decreases cs
        {
          var minus: Split<jminus> := OptionalMinus(cs);
          var num: Split<jint> :- TrimmedInt(minus.cs); var frac: Split<Maybe<jfrac>> :- Frac(num.cs); var exp: Split<Maybe<jexp>> :- Exp(frac.cs); Success(NumberFromParts(cs, minus, num, frac, exp))
        }
      }

      module ArrayParams refines SequenceParams {

        import opened Strings

        import opened Wrappers
        type TElement = Value

        const OPEN: byte := '[' as byte
        const CLOSE: byte := ']' as byte

        function method ElementSpec(t: TElement): bytes
          decreases t
        {
          Spec.Value(t)
        }

        function method {:opaque} {:fuel 0, 0} Element(cs: FreshCursor, json: ValueParser): (pr: ParseResult<TElement>)
          requires cs.StrictlySplitFrom?(json.cs)
          ensures pr.Success? ==> pr.value.StrictlySplitFrom?(cs, ElementSpec)
          decreases cs.Length()
        {
          json.fn(cs)
        }

        import opened BoundedInts

        import opened Grammar

        import opened Cursors = Utils.Cursors

        import opened Core
      }

      module Arrays refines Sequences {

        import opened Params = ArrayParams
        lemma /*{:_induction arr}*/ BracketedToArray(arr: jarray)
          ensures Spec.Bracketed(arr, SuffixedElementSpec) == Spec.Array(arr)
          decreases arr
        {
        }

        function method {:opaque} {:fuel 0, 0} Array(cs: FreshCursor, json: ValueParser): (pr: ParseResult<jarray>)
          requires cs.SplitFrom?(json.cs)
          ensures pr.Success? ==> pr.value.StrictlySplitFrom?(cs, Spec.Array)
          decreases cs, json
        {
          var sp: Split<TBracketed> :- Bracketed(cs, json); assert sp.StrictlySplitFrom?(cs, BracketedSpec); BracketedToArray(sp.t); Success(sp)
        }

        const SEPARATOR: byte := ',' as byte

        function SuffixedElementSpec(e: TSuffixedElement): bytes
          decreases e
        {
          ElementSpec(e.t) + Spec.CommaSuffix(e.suffix)
        }

        function BracketedSpec(ts: TBracketed): bytes
          decreases ts
        {
          Spec.Bracketed(ts, SuffixedElementSpec)
        }

        function SuffixedElementsSpec(ts: seq<TSuffixedElement>): bytes
          decreases ts
        {
          Spec.ConcatBytes(ts, SuffixedElementSpec)
        }

        function method {:opaque} {:fuel 0, 0} Open(cs: FreshCursor): (pr: ParseResult<jopen>)
          ensures pr.Success? ==> pr.value.StrictlySplitFrom?(cs, (_ /* _v0 */: View_) => [OPEN])
          decreases cs
        {
          var cs: Cursor :- cs.AssertByte(OPEN); Success(cs.Split())
        }

        function method {:opaque} {:fuel 0, 0} Close(cs: FreshCursor): (pr: ParseResult<jclose>)
          ensures pr.Success? ==> pr.value.StrictlySplitFrom?(cs, (_ /* _v1 */: View_) => [CLOSE])
          decreases cs
        {
          var cs: Cursor :- cs.AssertByte(CLOSE); Success(cs.Split())
        }

        function method {:opaque} {:fuel 0, 0} BracketedFromParts(ghost cs: Cursor, open: Split<Structural<jopen>>, elems: Split<seq<TSuffixedElement>>, close: Split<Structural<jclose>>): (sp: Split<TBracketed>)
          requires Grammar.NoTrailingSuffix(elems.t)
          requires open.StrictlySplitFrom?(cs, (c: Structural<jopen>) => Spec.Structural(c, SpecView))
          requires elems.SplitFrom?(open.cs, SuffixedElementsSpec)
          requires close.StrictlySplitFrom?(elems.cs, (c: Structural<jclose>) => Spec.Structural(c, SpecView))
          ensures sp.StrictlySplitFrom?(cs, BracketedSpec)
          decreases cs, open, elems, close
        {
          var sp: Split<Bracketed<jopen, TElement, jcomma, jclose>> := SP(Grammar.Bracketed(open.t, elems.t, close.t), close.cs);
          calc {
            cs.Bytes();
            Spec.Structural(open.t, SpecView) + open.cs.Bytes();
            {
              assert open.cs.Bytes() == SuffixedElementsSpec(elems.t) + elems.cs.Bytes();
            }
            Spec.Structural(open.t, SpecView) + (SuffixedElementsSpec(elems.t) + elems.cs.Bytes());
            {
              Seq.Assoc'(Spec.Structural(open.t, SpecView), SuffixedElementsSpec(elems.t), elems.cs.Bytes());
            }
            Spec.Structural(open.t, SpecView) + SuffixedElementsSpec(elems.t) + elems.cs.Bytes();
            {
              assert elems.cs.Bytes() == Spec.Structural(close.t, SpecView) + close.cs.Bytes();
            }
            Spec.Structural(open.t, SpecView) + SuffixedElementsSpec(elems.t) + (Spec.Structural(close.t, SpecView) + close.cs.Bytes());
            {
              Seq.Assoc'(Spec.Structural(open.t, SpecView) + SuffixedElementsSpec(elems.t), Spec.Structural(close.t, SpecView), close.cs.Bytes());
            }
            Spec.Structural(open.t, SpecView) + SuffixedElementsSpec(elems.t) + Spec.Structural(close.t, SpecView) + close.cs.Bytes();
            Spec.Bracketed(sp.t, SuffixedElementSpec) + close.cs.Bytes();
          }
          assert sp.StrictlySplitFrom?(cs, BracketedSpec);
          sp
        }

        function method {:opaque} {:fuel 0, 0} AppendWithSuffix(ghost cs0: FreshCursor, ghost json: ValueParser, elems: Split<seq<TSuffixedElement>>, elem: Split<TElement>, sep: Split<Structural<jcomma>>): (elems': Split<seq<TSuffixedElement>>)
          requires elems.cs.StrictlySplitFrom?(json.cs)
          requires elems.SplitFrom?(cs0, SuffixedElementsSpec)
          requires elem.StrictlySplitFrom?(elems.cs, ElementSpec)
          requires sep.StrictlySplitFrom?(elem.cs, (c: Structural<jcomma>) => Spec.Structural(c, SpecView))
          requires forall e: Suffixed<TElement, jcomma> {:trigger e.suffix} {:trigger e in elems.t} | e in elems.t :: e.suffix.NonEmpty?
          ensures elems'.StrictlySplitFrom?(cs0, SuffixedElementsSpec)
          ensures forall e: Suffixed<TElement, jcomma> {:trigger e.suffix} {:trigger e in elems'.t} | e in elems'.t :: e.suffix.NonEmpty?
          ensures elems'.cs.Length() < elems.cs.Length()
          ensures elems'.cs.StrictlySplitFrom?(json.cs)
          decreases cs0, json, elems, elem, sep
        {
          var suffixed: Suffixed<TElement, jcomma> := Suffixed(elem.t, NonEmpty(sep.t));
          var elems': Split<seq<Suffixed<Value, jcomma>>> := SP(elems.t + [suffixed], sep.cs);
          assert cs0.Bytes() == SuffixedElementsSpec(elems'.t) + sep.cs.Bytes() by {
            assert {:focus} cs0.Bytes() == SuffixedElementsSpec(elems.t) + (ElementSpec(suffixed.t) + Spec.CommaSuffix(suffixed.suffix)) + sep.cs.Bytes() by {
              assert cs0.Bytes() == SuffixedElementsSpec(elems.t) + ElementSpec(suffixed.t) + Spec.CommaSuffix(suffixed.suffix) + sep.cs.Bytes() by {
                assert cs0.Bytes() == SuffixedElementsSpec(elems.t) + elems.cs.Bytes();
                assert elems.cs.Bytes() == ElementSpec(suffixed.t) + elem.cs.Bytes();
                assert elem.cs.Bytes() == Spec.CommaSuffix(suffixed.suffix) + sep.cs.Bytes();
                Seq.Assoc'(SuffixedElementsSpec(elems.t), ElementSpec(suffixed.t), elem.cs.Bytes());
                Seq.Assoc'(SuffixedElementsSpec(elems.t) + ElementSpec(suffixed.t), Spec.CommaSuffix(suffixed.suffix), sep.cs.Bytes());
              }
              Seq.Assoc(SuffixedElementsSpec(elems.t), ElementSpec(suffixed.t), Spec.CommaSuffix(suffixed.suffix));
            }
            assert SuffixedElementsSpec(elems.t) + (ElementSpec(suffixed.t) + Spec.CommaSuffix(suffixed.suffix)) + sep.cs.Bytes() == SuffixedElementsSpec(elems'.t) + sep.cs.Bytes() by {
              assert SuffixedElementsSpec(elems.t) + SuffixedElementSpec(suffixed) == SuffixedElementsSpec(elems.t + [suffixed]) by {
                SpecProperties.ConcatBytes_Linear(elems.t, [suffixed], SuffixedElementSpec);
                assert Spec.ConcatBytes(elems.t, SuffixedElementSpec) + Spec.ConcatBytes([suffixed], SuffixedElementSpec) == Spec.ConcatBytes(elems.t + [suffixed], SuffixedElementSpec);
              }
            }
          }
          assert elems'.StrictlySplitFrom?(cs0, SuffixedElementsSpec);
          assert forall e: Suffixed<Value, jcomma> {:trigger e.suffix} {:trigger e in elems'.t} | e in elems'.t :: e.suffix.NonEmpty? by {
            assert elems'.t == elems.t + [suffixed];
          }
          assert {:split_here} elems'.cs.Length() < elems.cs.Length();
          elems'
        }

        function method {:opaque} {:fuel 0, 0} AppendLast(ghost cs0: FreshCursor, ghost json: ValueParser, elems: Split<seq<TSuffixedElement>>, elem: Split<TElement>, sep: Split<Structural<jclose>>): (elems': Split<seq<TSuffixedElement>>)
          requires elems.cs.StrictlySplitFrom?(json.cs)
          requires elems.SplitFrom?(cs0, SuffixedElementsSpec)
          requires elem.StrictlySplitFrom?(elems.cs, ElementSpec)
          requires sep.StrictlySplitFrom?(elem.cs, (c: Structural<jclose>) => Spec.Structural(c, SpecView))
          requires forall e: Suffixed<TElement, jcomma> {:trigger e.suffix} {:trigger e in elems.t} | e in elems.t :: e.suffix.NonEmpty?
          ensures elems'.StrictlySplitFrom?(cs0, SuffixedElementsSpec)
          ensures NoTrailingSuffix(elems'.t)
          ensures elems'.cs.Length() < elems.cs.Length()
          ensures elems'.cs.StrictlySplitFrom?(json.cs)
          ensures sep.StrictlySplitFrom?(elems'.cs, (c: Structural<jclose>) => Spec.Structural(c, SpecView))
          decreases cs0, json, elems, elem, sep
        {
          var suffixed: Suffixed<TElement, jcomma> := Suffixed(elem.t, Empty());
          var elems': Split<seq<Suffixed<Value, jcomma>>> := SP(elems.t + [suffixed], elem.cs);
          assert cs0.Bytes() == SuffixedElementsSpec(elems'.t) + elem.cs.Bytes() by {
            assert cs0.Bytes() == SuffixedElementsSpec(elems.t) + ElementSpec(suffixed.t) + elem.cs.Bytes() by {
              assert elem.t == suffixed.t;
            }
            assert SuffixedElementsSpec(elems.t) + ElementSpec(suffixed.t) + elem.cs.Bytes() == SuffixedElementsSpec(elems'.t) + elem.cs.Bytes() by {
              assert SuffixedElementsSpec(elems.t) + SuffixedElementSpec(suffixed) == SuffixedElementsSpec(elems.t + [suffixed]) by {
                SpecProperties.ConcatBytes_Linear(elems.t, [suffixed], SuffixedElementSpec);
                assert Spec.ConcatBytes(elems.t, SuffixedElementSpec) + Spec.ConcatBytes([suffixed], SuffixedElementSpec) == Spec.ConcatBytes(elems.t + [suffixed], SuffixedElementSpec);
              }
            }
          }
          assert elems'.StrictlySplitFrom?(cs0, SuffixedElementsSpec);
          elems'
        }

        function method {:opaque} {:tailrecursion} {:fuel 0, 0} Elements(ghost cs0: FreshCursor, json: ValueParser, open: Split<Structural<jopen>>, elems: Split<seq<TSuffixedElement>>): (pr: ParseResult<TBracketed>)
          requires open.StrictlySplitFrom?(cs0, (c: Structural<jopen>) => Spec.Structural(c, SpecView))
          requires elems.cs.StrictlySplitFrom?(json.cs)
          requires elems.SplitFrom?(open.cs, SuffixedElementsSpec)
          requires forall e: Suffixed<TElement, jcomma> {:trigger e.suffix} {:trigger e in elems.t} | e in elems.t :: e.suffix.NonEmpty?
          ensures pr.Success? ==> pr.value.StrictlySplitFrom?(cs0, BracketedSpec)
          decreases elems.cs.Length()
        {
          var elem: Split<TElement> :- Element(elems.cs, json); var sep: Split<Structural<jopt>> := Core.TryStructural(elem.cs); var s0: opt_byte := sep.t.t.Peek(); if s0 == SEPARATOR as opt_byte then assert AppendWithSuffix.requires(open.cs, json, elems, elem, sep) by {
    assert {:focus} elems.cs.StrictlySplitFrom?(json.cs);
    assert elems.SplitFrom?(open.cs, SuffixedElementsSpec);
    assert elem.StrictlySplitFrom?(elems.cs, ElementSpec);
    assert sep.StrictlySplitFrom?(elem.cs, (c: Structural<jopt>) => Spec.Structural(c, SpecView));
    assert forall e: Suffixed<TElement, jcomma> {:trigger e.suffix} {:trigger e in elems.t} | e in elems.t :: e.suffix.NonEmpty?;
    assert {:split_here} true;
  } var elems: Split<seq<TSuffixedElement>> := AppendWithSuffix(open.cs, json, elems, elem, sep); Elements(cs0, json, open, elems) else if s0 == CLOSE as opt_byte then assert AppendLast.requires(open.cs, json, elems, elem, sep) by {
    assert sep.StrictlySplitFrom?(elem.cs, (c: Structural<jopt>) => Spec.Structural(c, SpecView));
    assert elems.cs.StrictlySplitFrom?(json.cs);
    assert elems.SplitFrom?(open.cs, SuffixedElementsSpec);
    assert elem.StrictlySplitFrom?(elems.cs, ElementSpec);
  } var elems': Split<seq<TSuffixedElement>> := AppendLast(open.cs, json, elems, elem, sep); assert elems'.SplitFrom?(open.cs, SuffixedElementsSpec) by {
    assert elems'.StrictlySplitFrom?(open.cs, SuffixedElementsSpec);
  } var bracketed: Split<TBracketed> := BracketedFromParts(cs0, open, elems', sep); assert bracketed.StrictlySplitFrom?(cs0, BracketedSpec); Success(bracketed) else var separator: byte := SEPARATOR; var pr: Result<Split<Bracketed<jopen, Value, jcomma, jclose>>, CursorError<Errors.DeserializationError>> := Failure(ExpectingAnyByte([CLOSE, separator], s0)); pr
        }

        function method {:opaque} {:fuel 0, 0} Bracketed(cs: FreshCursor, json: ValueParser): (pr: ParseResult<TBracketed>)
          requires cs.SplitFrom?(json.cs)
          ensures pr.Success? ==> pr.value.StrictlySplitFrom?(cs, BracketedSpec)
          decreases cs, json
        {
          var open: Split<Structural<jopen>> :- Core.Structural(cs, Parsers.Parser(Open, SpecView)); assert open.cs.StrictlySplitFrom?(json.cs); var elems: Split<seq<Suffixed<Value, jcomma>>> := SP([], open.cs); if open.cs.Peek() == CLOSE as opt_byte then var close: Split<Structural<jclose>> :- Core.Structural(open.cs, Parsers.Parser(Close, SpecView)); Success(BracketedFromParts(cs, open, elems, close)) else Elements(cs, json, open, elems)
        }

        lemma Valid(x: TBracketed)
          ensures x.l.t.Byte?(OPEN)
          ensures x.r.t.Byte?(CLOSE)
          ensures NoTrailingSuffix(x.data)
          ensures forall pf: Suffixed<TElement, jcomma> {:trigger pf.suffix} {:trigger pf in x.data} | pf in x.data :: pf.suffix.NonEmpty? ==> pf.suffix.t.t.Byte?(SEPARATOR)
          decreases x
        {
          ghost var xlt: jopen := x.l.t;
          ghost var xrt: jclose := x.r.t;
          forall pf: Suffixed<TElement, jcomma> | pf in x.data
            ensures pf.suffix.NonEmpty? ==> pf.suffix.t.t.Byte?(SEPARATOR)
          {
            if pf.suffix.NonEmpty? {
              ghost var xtt := pf.suffix.t.t;
            }
          }
        }

        import opened Wrappers

        import opened BoundedInts

        import SpecProperties = ConcreteSyntax.SpecProperties

        import opened Vs = Utils.Views.Core

        import opened Grammar

        import opened Cursors = Utils.Cursors

        import Parsers = Utils.Parsers

        import opened Core

        type jopen = v: Vs.View
          | v.Byte?(OPEN)
          witness Vs.View.OfBytes([OPEN])

        type jclose = v: Vs.View
          | v.Byte?(CLOSE)
          witness Vs.View.OfBytes([CLOSE])

        type TBracketed = Bracketed<jopen, TElement, jcomma, jclose>

        type TSuffixedElement = Suffixed<TElement, jcomma>
      }

      module ObjectParams refines SequenceParams {

        import opened Wrappers

        import Strings
        type TElement = jKeyValue

        const OPEN: byte := '{' as byte
        const CLOSE: byte := '}' as byte

        function method Colon(cs: FreshCursor): (pr: ParseResult<jcolon>)
          ensures pr.Success? ==> pr.value.StrictlySplitFrom?(cs, SpecView)
          decreases cs
        {
          var cs: Cursor :- cs.AssertChar(':'); Success(cs.Split())
        }

        function method {:opaque} {:fuel 0, 0} KeyValueFromParts(ghost cs: Cursor, k: Split<jstring>, colon: Split<Structural<jcolon>>, v: Split<Value>): (sp: Split<jKeyValue>)
          requires k.StrictlySplitFrom?(cs, Spec.String)
          requires colon.StrictlySplitFrom?(k.cs, (c: Structural<jcolon>) => Spec.Structural(c, SpecView))
          requires v.StrictlySplitFrom?(colon.cs, Spec.Value)
          ensures sp.StrictlySplitFrom?(cs, ElementSpec)
          decreases cs, k, colon, v
        {
          var sp: Split<jKeyValue> := SP(Grammar.KeyValue(k.t, colon.t, v.t), v.cs);
          assert cs.Bytes() == Spec.KeyValue(sp.t) + v.cs.Bytes() by {
            assert cs.Bytes() == Spec.String(k.t) + Spec.Structural(colon.t, SpecView) + Spec.Value(v.t) + v.cs.Bytes() by {
              assert cs.Bytes() == Spec.String(k.t) + k.cs.Bytes();
              assert k.cs.Bytes() == Spec.Structural(colon.t, SpecView) + colon.cs.Bytes();
              assert colon.cs.Bytes() == Spec.Value(v.t) + v.cs.Bytes();
              Seq.Assoc'(Spec.String(k.t), Spec.Structural(colon.t, SpecView), colon.cs.Bytes());
              Seq.Assoc'(Spec.String(k.t) + Spec.Structural(colon.t, SpecView), Spec.Value(v.t), v.cs.Bytes());
            }
          }
          assert sp.StrictlySplitFrom?(cs, ElementSpec);
          sp
        }

        function method ElementSpec(t: TElement): bytes
          decreases t
        {
          Spec.KeyValue(t)
        }

        function method {:opaque} {:fuel 0, 0} Element(cs: FreshCursor, json: ValueParser): (pr: ParseResult<TElement>)
          requires cs.StrictlySplitFrom?(json.cs)
          ensures pr.Success? ==> pr.value.StrictlySplitFrom?(cs, ElementSpec)
          decreases cs.Length()
        {
          var k: Split<jstring> :- Strings.String(cs); assert k.cs.StrictlySplitFrom?(json.cs); var p: Parser_<jcolon, JSONError> := Parsers.Parser(Colon, SpecView); assert p.Valid?(); var colon: Split<Structural<jcolon>> :- Core.Structural(k.cs, p); assert colon.StrictlySplitFrom?(k.cs, (st: Structural<jcolon>) => Spec.Structural(st, p.spec)); assert colon.cs.StrictlySplitFrom?(json.cs); var v: Split<Value> :- json.fn(colon.cs); var kv: Split<jKeyValue> := KeyValueFromParts(cs, k, colon, v); Success(kv)
        }

        import opened BoundedInts

        import opened Grammar

        import opened Cursors = Utils.Cursors

        import opened Core
      }

      module Objects refines Sequences {

        import opened Params = ObjectParams
        lemma {:vcs_split_on_every_assert} /*{:_induction obj}*/ BracketedToObject(obj: jobject)
          ensures Spec.Bracketed(obj, SuffixedElementSpec) == Spec.Object(obj)
          decreases obj
        {
        }

        function method {:opaque} {:fuel 0, 0} Object(cs: FreshCursor, json: ValueParser): (pr: ParseResult<jobject>)
          requires cs.SplitFrom?(json.cs)
          ensures pr.Success? ==> pr.value.StrictlySplitFrom?(cs, Spec.Object)
          decreases cs, json
        {
          var sp: Split<TBracketed> :- Bracketed(cs, json); assert sp.StrictlySplitFrom?(cs, BracketedSpec); BracketedToObject(sp.t); Success(sp)
        }

        const SEPARATOR: byte := ',' as byte

        function SuffixedElementSpec(e: TSuffixedElement): bytes
          decreases e
        {
          ElementSpec(e.t) + Spec.CommaSuffix(e.suffix)
        }

        function BracketedSpec(ts: TBracketed): bytes
          decreases ts
        {
          Spec.Bracketed(ts, SuffixedElementSpec)
        }

        function SuffixedElementsSpec(ts: seq<TSuffixedElement>): bytes
          decreases ts
        {
          Spec.ConcatBytes(ts, SuffixedElementSpec)
        }

        function method {:opaque} {:fuel 0, 0} Open(cs: FreshCursor): (pr: ParseResult<jopen>)
          ensures pr.Success? ==> pr.value.StrictlySplitFrom?(cs, (_ /* _v0 */: View_) => [OPEN])
          decreases cs
        {
          var cs: Cursor :- cs.AssertByte(OPEN); Success(cs.Split())
        }

        function method {:opaque} {:fuel 0, 0} Close(cs: FreshCursor): (pr: ParseResult<jclose>)
          ensures pr.Success? ==> pr.value.StrictlySplitFrom?(cs, (_ /* _v1 */: View_) => [CLOSE])
          decreases cs
        {
          var cs: Cursor :- cs.AssertByte(CLOSE); Success(cs.Split())
        }

        function method {:opaque} {:fuel 0, 0} BracketedFromParts(ghost cs: Cursor, open: Split<Structural<jopen>>, elems: Split<seq<TSuffixedElement>>, close: Split<Structural<jclose>>): (sp: Split<TBracketed>)
          requires Grammar.NoTrailingSuffix(elems.t)
          requires open.StrictlySplitFrom?(cs, (c: Structural<jopen>) => Spec.Structural(c, SpecView))
          requires elems.SplitFrom?(open.cs, SuffixedElementsSpec)
          requires close.StrictlySplitFrom?(elems.cs, (c: Structural<jclose>) => Spec.Structural(c, SpecView))
          ensures sp.StrictlySplitFrom?(cs, BracketedSpec)
          decreases cs, open, elems, close
        {
          var sp: Split<Bracketed<jopen, TElement, jcomma, jclose>> := SP(Grammar.Bracketed(open.t, elems.t, close.t), close.cs);
          calc {
            cs.Bytes();
            Spec.Structural(open.t, SpecView) + open.cs.Bytes();
            {
              assert open.cs.Bytes() == SuffixedElementsSpec(elems.t) + elems.cs.Bytes();
            }
            Spec.Structural(open.t, SpecView) + (SuffixedElementsSpec(elems.t) + elems.cs.Bytes());
            {
              Seq.Assoc'(Spec.Structural(open.t, SpecView), SuffixedElementsSpec(elems.t), elems.cs.Bytes());
            }
            Spec.Structural(open.t, SpecView) + SuffixedElementsSpec(elems.t) + elems.cs.Bytes();
            {
              assert elems.cs.Bytes() == Spec.Structural(close.t, SpecView) + close.cs.Bytes();
            }
            Spec.Structural(open.t, SpecView) + SuffixedElementsSpec(elems.t) + (Spec.Structural(close.t, SpecView) + close.cs.Bytes());
            {
              Seq.Assoc'(Spec.Structural(open.t, SpecView) + SuffixedElementsSpec(elems.t), Spec.Structural(close.t, SpecView), close.cs.Bytes());
            }
            Spec.Structural(open.t, SpecView) + SuffixedElementsSpec(elems.t) + Spec.Structural(close.t, SpecView) + close.cs.Bytes();
            Spec.Bracketed(sp.t, SuffixedElementSpec) + close.cs.Bytes();
          }
          assert sp.StrictlySplitFrom?(cs, BracketedSpec);
          sp
        }

        function method {:opaque} {:fuel 0, 0} AppendWithSuffix(ghost cs0: FreshCursor, ghost json: ValueParser, elems: Split<seq<TSuffixedElement>>, elem: Split<TElement>, sep: Split<Structural<jcomma>>): (elems': Split<seq<TSuffixedElement>>)
          requires elems.cs.StrictlySplitFrom?(json.cs)
          requires elems.SplitFrom?(cs0, SuffixedElementsSpec)
          requires elem.StrictlySplitFrom?(elems.cs, ElementSpec)
          requires sep.StrictlySplitFrom?(elem.cs, (c: Structural<jcomma>) => Spec.Structural(c, SpecView))
          requires forall e: Suffixed<TElement, jcomma> {:trigger e.suffix} {:trigger e in elems.t} | e in elems.t :: e.suffix.NonEmpty?
          ensures elems'.StrictlySplitFrom?(cs0, SuffixedElementsSpec)
          ensures forall e: Suffixed<TElement, jcomma> {:trigger e.suffix} {:trigger e in elems'.t} | e in elems'.t :: e.suffix.NonEmpty?
          ensures elems'.cs.Length() < elems.cs.Length()
          ensures elems'.cs.StrictlySplitFrom?(json.cs)
          decreases cs0, json, elems, elem, sep
        {
          var suffixed: Suffixed<TElement, jcomma> := Suffixed(elem.t, NonEmpty(sep.t));
          var elems': Split<seq<Suffixed<jKeyValue, jcomma>>> := SP(elems.t + [suffixed], sep.cs);
          assert cs0.Bytes() == SuffixedElementsSpec(elems'.t) + sep.cs.Bytes() by {
            assert {:focus} cs0.Bytes() == SuffixedElementsSpec(elems.t) + (ElementSpec(suffixed.t) + Spec.CommaSuffix(suffixed.suffix)) + sep.cs.Bytes() by {
              assert cs0.Bytes() == SuffixedElementsSpec(elems.t) + ElementSpec(suffixed.t) + Spec.CommaSuffix(suffixed.suffix) + sep.cs.Bytes() by {
                assert cs0.Bytes() == SuffixedElementsSpec(elems.t) + elems.cs.Bytes();
                assert elems.cs.Bytes() == ElementSpec(suffixed.t) + elem.cs.Bytes();
                assert elem.cs.Bytes() == Spec.CommaSuffix(suffixed.suffix) + sep.cs.Bytes();
                Seq.Assoc'(SuffixedElementsSpec(elems.t), ElementSpec(suffixed.t), elem.cs.Bytes());
                Seq.Assoc'(SuffixedElementsSpec(elems.t) + ElementSpec(suffixed.t), Spec.CommaSuffix(suffixed.suffix), sep.cs.Bytes());
              }
              Seq.Assoc(SuffixedElementsSpec(elems.t), ElementSpec(suffixed.t), Spec.CommaSuffix(suffixed.suffix));
            }
            assert SuffixedElementsSpec(elems.t) + (ElementSpec(suffixed.t) + Spec.CommaSuffix(suffixed.suffix)) + sep.cs.Bytes() == SuffixedElementsSpec(elems'.t) + sep.cs.Bytes() by {
              assert SuffixedElementsSpec(elems.t) + SuffixedElementSpec(suffixed) == SuffixedElementsSpec(elems.t + [suffixed]) by {
                SpecProperties.ConcatBytes_Linear(elems.t, [suffixed], SuffixedElementSpec);
                assert Spec.ConcatBytes(elems.t, SuffixedElementSpec) + Spec.ConcatBytes([suffixed], SuffixedElementSpec) == Spec.ConcatBytes(elems.t + [suffixed], SuffixedElementSpec);
              }
            }
          }
          assert elems'.StrictlySplitFrom?(cs0, SuffixedElementsSpec);
          assert forall e: Suffixed<jKeyValue, jcomma> {:trigger e.suffix} {:trigger e in elems'.t} | e in elems'.t :: e.suffix.NonEmpty? by {
            assert elems'.t == elems.t + [suffixed];
          }
          assert {:split_here} elems'.cs.Length() < elems.cs.Length();
          elems'
        }

        function method {:opaque} {:fuel 0, 0} AppendLast(ghost cs0: FreshCursor, ghost json: ValueParser, elems: Split<seq<TSuffixedElement>>, elem: Split<TElement>, sep: Split<Structural<jclose>>): (elems': Split<seq<TSuffixedElement>>)
          requires elems.cs.StrictlySplitFrom?(json.cs)
          requires elems.SplitFrom?(cs0, SuffixedElementsSpec)
          requires elem.StrictlySplitFrom?(elems.cs, ElementSpec)
          requires sep.StrictlySplitFrom?(elem.cs, (c: Structural<jclose>) => Spec.Structural(c, SpecView))
          requires forall e: Suffixed<TElement, jcomma> {:trigger e.suffix} {:trigger e in elems.t} | e in elems.t :: e.suffix.NonEmpty?
          ensures elems'.StrictlySplitFrom?(cs0, SuffixedElementsSpec)
          ensures NoTrailingSuffix(elems'.t)
          ensures elems'.cs.Length() < elems.cs.Length()
          ensures elems'.cs.StrictlySplitFrom?(json.cs)
          ensures sep.StrictlySplitFrom?(elems'.cs, (c: Structural<jclose>) => Spec.Structural(c, SpecView))
          decreases cs0, json, elems, elem, sep
        {
          var suffixed: Suffixed<TElement, jcomma> := Suffixed(elem.t, Empty());
          var elems': Split<seq<Suffixed<jKeyValue, jcomma>>> := SP(elems.t + [suffixed], elem.cs);
          assert cs0.Bytes() == SuffixedElementsSpec(elems'.t) + elem.cs.Bytes() by {
            assert cs0.Bytes() == SuffixedElementsSpec(elems.t) + ElementSpec(suffixed.t) + elem.cs.Bytes() by {
              assert elem.t == suffixed.t;
            }
            assert SuffixedElementsSpec(elems.t) + ElementSpec(suffixed.t) + elem.cs.Bytes() == SuffixedElementsSpec(elems'.t) + elem.cs.Bytes() by {
              assert SuffixedElementsSpec(elems.t) + SuffixedElementSpec(suffixed) == SuffixedElementsSpec(elems.t + [suffixed]) by {
                SpecProperties.ConcatBytes_Linear(elems.t, [suffixed], SuffixedElementSpec);
                assert Spec.ConcatBytes(elems.t, SuffixedElementSpec) + Spec.ConcatBytes([suffixed], SuffixedElementSpec) == Spec.ConcatBytes(elems.t + [suffixed], SuffixedElementSpec);
              }
            }
          }
          assert elems'.StrictlySplitFrom?(cs0, SuffixedElementsSpec);
          elems'
        }

        function method {:opaque} {:tailrecursion} {:fuel 0, 0} Elements(ghost cs0: FreshCursor, json: ValueParser, open: Split<Structural<jopen>>, elems: Split<seq<TSuffixedElement>>): (pr: ParseResult<TBracketed>)
          requires open.StrictlySplitFrom?(cs0, (c: Structural<jopen>) => Spec.Structural(c, SpecView))
          requires elems.cs.StrictlySplitFrom?(json.cs)
          requires elems.SplitFrom?(open.cs, SuffixedElementsSpec)
          requires forall e: Suffixed<TElement, jcomma> {:trigger e.suffix} {:trigger e in elems.t} | e in elems.t :: e.suffix.NonEmpty?
          ensures pr.Success? ==> pr.value.StrictlySplitFrom?(cs0, BracketedSpec)
          decreases elems.cs.Length()
        {
          var elem: Split<TElement> :- Element(elems.cs, json); var sep: Split<Structural<jopt>> := Core.TryStructural(elem.cs); var s0: opt_byte := sep.t.t.Peek(); if s0 == SEPARATOR as opt_byte then assert AppendWithSuffix.requires(open.cs, json, elems, elem, sep) by {
    assert {:focus} elems.cs.StrictlySplitFrom?(json.cs);
    assert elems.SplitFrom?(open.cs, SuffixedElementsSpec);
    assert elem.StrictlySplitFrom?(elems.cs, ElementSpec);
    assert sep.StrictlySplitFrom?(elem.cs, (c: Structural<jopt>) => Spec.Structural(c, SpecView));
    assert forall e: Suffixed<TElement, jcomma> {:trigger e.suffix} {:trigger e in elems.t} | e in elems.t :: e.suffix.NonEmpty?;
    assert {:split_here} true;
  } var elems: Split<seq<TSuffixedElement>> := AppendWithSuffix(open.cs, json, elems, elem, sep); Elements(cs0, json, open, elems) else if s0 == CLOSE as opt_byte then assert AppendLast.requires(open.cs, json, elems, elem, sep) by {
    assert sep.StrictlySplitFrom?(elem.cs, (c: Structural<jopt>) => Spec.Structural(c, SpecView));
    assert elems.cs.StrictlySplitFrom?(json.cs);
    assert elems.SplitFrom?(open.cs, SuffixedElementsSpec);
    assert elem.StrictlySplitFrom?(elems.cs, ElementSpec);
  } var elems': Split<seq<TSuffixedElement>> := AppendLast(open.cs, json, elems, elem, sep); assert elems'.SplitFrom?(open.cs, SuffixedElementsSpec) by {
    assert elems'.StrictlySplitFrom?(open.cs, SuffixedElementsSpec);
  } var bracketed: Split<TBracketed> := BracketedFromParts(cs0, open, elems', sep); assert bracketed.StrictlySplitFrom?(cs0, BracketedSpec); Success(bracketed) else var separator: byte := SEPARATOR; var pr: Result<Split<Bracketed<jopen, jKeyValue, jcomma, jclose>>, CursorError<Errors.DeserializationError>> := Failure(ExpectingAnyByte([CLOSE, separator], s0)); pr
        }

        function method {:opaque} {:fuel 0, 0} Bracketed(cs: FreshCursor, json: ValueParser): (pr: ParseResult<TBracketed>)
          requires cs.SplitFrom?(json.cs)
          ensures pr.Success? ==> pr.value.StrictlySplitFrom?(cs, BracketedSpec)
          decreases cs, json
        {
          var open: Split<Structural<jopen>> :- Core.Structural(cs, Parsers.Parser(Open, SpecView)); assert open.cs.StrictlySplitFrom?(json.cs); var elems: Split<seq<Suffixed<jKeyValue, jcomma>>> := SP([], open.cs); if open.cs.Peek() == CLOSE as opt_byte then var close: Split<Structural<jclose>> :- Core.Structural(open.cs, Parsers.Parser(Close, SpecView)); Success(BracketedFromParts(cs, open, elems, close)) else Elements(cs, json, open, elems)
        }

        lemma Valid(x: TBracketed)
          ensures x.l.t.Byte?(OPEN)
          ensures x.r.t.Byte?(CLOSE)
          ensures NoTrailingSuffix(x.data)
          ensures forall pf: Suffixed<TElement, jcomma> {:trigger pf.suffix} {:trigger pf in x.data} | pf in x.data :: pf.suffix.NonEmpty? ==> pf.suffix.t.t.Byte?(SEPARATOR)
          decreases x
        {
          ghost var xlt: jopen := x.l.t;
          ghost var xrt: jclose := x.r.t;
          forall pf: Suffixed<TElement, jcomma> | pf in x.data
            ensures pf.suffix.NonEmpty? ==> pf.suffix.t.t.Byte?(SEPARATOR)
          {
            if pf.suffix.NonEmpty? {
              ghost var xtt := pf.suffix.t.t;
            }
          }
        }

        import opened Wrappers

        import opened BoundedInts

        import SpecProperties = ConcreteSyntax.SpecProperties

        import opened Vs = Utils.Views.Core

        import opened Grammar

        import opened Cursors = Utils.Cursors

        import Parsers = Utils.Parsers

        import opened Core

        type jopen = v: Vs.View
          | v.Byte?(OPEN)
          witness Vs.View.OfBytes([OPEN])

        type jclose = v: Vs.View
          | v.Byte?(CLOSE)
          witness Vs.View.OfBytes([CLOSE])

        type TBracketed = Bracketed<jopen, TElement, jcomma, jclose>

        type TSuffixedElement = Suffixed<TElement, jcomma>
      }
    }
  }

  module ConcreteSyntax {

    module {:options ""-functionSyntax:4""} Spec {

      import opened BoundedInts

      import Vs = Utils.Views.Core

      import opened Grammar
      function method View(v: Vs.View): bytes
        decreases v
      {
        v.Bytes()
      }

      function method Structural<T>(self: Structural<T>, fT: T -> bytes): bytes
        decreases self
      {
        View(self.before) + fT(self.t) + View(self.after)
      }

      function method StructuralView(self: Structural<Vs.View>): bytes
        decreases self
      {
        Structural<Vs.View>(self, View)
      }

      function method Maybe<T>(self: Maybe<T>, fT: T -> bytes): (bs: bytes)
        ensures self.Empty? ==> bs == []
        ensures self.NonEmpty? ==> bs == fT(self.t)
        decreases self
      {
        if self.Empty? then
          []
        else
          fT(self.t)
      }

      function method ConcatBytes<T>(ts: seq<T>, fT: T --> bytes): bytes
        requires forall d: T {:trigger fT.requires(d)} {:trigger d in ts} | d in ts :: fT.requires(d)
        decreases ts
      {
        if |ts| == 0 then
          []
        else
          fT(ts[0]) + ConcatBytes(ts[1..], fT)
      }

      function method Bracketed<D, S>(self: Bracketed<Vs.View, D, S, Vs.View>, fDatum: Suffixed<D, S> --> bytes): bytes
        requires forall d: Suffixed<D, S> {:trigger fDatum.requires(d)} | d < self :: fDatum.requires(d)
        decreases self
      {
        StructuralView(self.l) + ConcatBytes(self.data, fDatum) + StructuralView(self.r)
      }

      function method KeyValue(self: jKeyValue): bytes
        decreases self
      {
        String(self.k) + StructuralView(self.colon) + Value(self.v)
      }

      function method Frac(self: jfrac): bytes
        decreases self
      {
        View(self.period) + View(self.num)
      }

      function method Exp(self: jexp): bytes
        decreases self
      {
        View(self.e) + View(self.sign) + View(self.num)
      }

      function method Number(self: jnumber): bytes
        decreases self
      {
        View(self.minus) + View(self.num) + Maybe(self.frac, Frac) + Maybe(self.exp, Exp)
      }

      function method String(self: jstring): bytes
        decreases self
      {
        View(self.lq) + View(self.contents) + View(self.rq)
      }

      function method CommaSuffix(c: Maybe<Structural<jcomma>>): bytes
        decreases c
      {
        Maybe<Structural<Vs.View>>(c, StructuralView)
      }

      function method Member(self: jmember): bytes
        decreases self
      {
        KeyValue(self.t) + CommaSuffix(self.suffix)
      }

      function method Item(self: jitem): bytes
        decreases self
      {
        Value(self.t) + CommaSuffix(self.suffix)
      }

      function method Object(obj: jobject): bytes
        decreases obj
      {
        Bracketed(obj, (d: jmember) requires d < obj => Member(d))
      }

      function method Array(arr: jarray): bytes
        decreases arr
      {
        Bracketed(arr, (d: jitem) requires d < arr => Item(d))
      }

      function method Value(self: Value): bytes
        decreases self
      {
        match self {
          case Null(n) =>
            View(n)
          case Bool(b) =>
            View(b)
          case String(str) =>
            String(str)
          case Number(num) =>
            Number(num)
          case Object(obj) =>
            Object(obj)
          case Array(arr) =>
            Array(arr)
        }
      }

      lemma /*{:_induction v}*/ UnfoldValueNumber(v: Value)
        requires v.Number?
        ensures Value(v) == Number(v.num)
        decreases v
      {
      }

      lemma /*{:_induction v}*/ UnfoldValueObject(v: Value)
        requires v.Object?
        ensures Value(v) == Object(v.obj)
        decreases v
      {
      }

      lemma /*{:_induction v}*/ UnfoldValueArray(v: Value)
        requires v.Array?
        ensures Value(v) == Array(v.arr)
        decreases v
      {
      }

      function method JSON(js: JSON): bytes
        decreases js
      {
        Structural(js, Value)
      }
    }

    module {:options ""-functionSyntax:4""} SpecProperties {

      import opened BoundedInts

      import Vs = Utils.Views.Core

      import opened Grammar

      import Spec
      lemma Bracketed_Morphism<D, S>(bracketed: Bracketed<Vs.View, D, S, Vs.View>)
        ensures forall pd0: Suffixed<D, S> --> bytes, pd1: Suffixed<D, S> --> bytes {:trigger Spec.Bracketed(bracketed, pd1), Spec.Bracketed(bracketed, pd0)} | (forall d: Suffixed<D, S> {:trigger pd0.requires(d)} | d < bracketed :: pd0.requires(d)) && (forall d: Suffixed<D, S> {:trigger pd1.requires(d)} | d < bracketed :: pd1.requires(d)) && forall d: Suffixed<D, S> {:trigger pd1(d)} {:trigger pd0(d)} | d < bracketed :: pd0(d) == pd1(d) :: Spec.Bracketed(bracketed, pd0) == Spec.Bracketed(bracketed, pd1)
        decreases bracketed
      {
      }

      lemma {:induction ts} /*{:_induction ts}*/ ConcatBytes_Morphism<T>(ts: seq<T>, pt0: T --> bytes, pt1: T --> bytes)
        requires forall d: T {:trigger pt0.requires(d)} {:trigger d in ts} | d in ts :: pt0.requires(d)
        requires forall d: T {:trigger pt1.requires(d)} {:trigger d in ts} | d in ts :: pt1.requires(d)
        requires forall d: T {:trigger pt1(d)} {:trigger pt0(d)} {:trigger d in ts} | d in ts :: pt0(d) == pt1(d)
        ensures Spec.ConcatBytes(ts, pt0) == Spec.ConcatBytes(ts, pt1)
        decreases ts
      {
      }

      lemma {:induction ts0} /*{:_induction ts0}*/ ConcatBytes_Linear<T>(ts0: seq<T>, ts1: seq<T>, pt: T --> bytes)
        requires forall d: T {:trigger pt.requires(d)} {:trigger d in ts0} | d in ts0 :: pt.requires(d)
        requires forall d: T {:trigger pt.requires(d)} {:trigger d in ts1} | d in ts1 :: pt.requires(d)
        ensures Spec.ConcatBytes(ts0 + ts1, pt) == Spec.ConcatBytes(ts0, pt) + Spec.ConcatBytes(ts1, pt)
        decreases ts0, ts1
      {
      }
    }
  }
}
")]

namespace Dafny {
  internal class ArrayHelpers {
    public static T[] InitNewArray1<T>(T z, BigInteger size0) {
      int s0 = (int)size0;
      T[] a = new T[s0];
      for (int i0 = 0; i0 < s0; i0++) {
        a[i0] = z;
      }
      return a;
    }
  }
} // end of namespace Dafny
internal static class FuncExtensions {
  public static Func<U, UResult> DowncastClone<T, TResult, U, UResult>(this Func<T, TResult> F, Func<U, T> ArgConv, Func<TResult, UResult> ResConv) {
    return arg => ResConv(F(ArgConv(arg)));
  }
  public static Func<UResult> DowncastClone<TResult, UResult>(this Func<TResult> F, Func<TResult, UResult> ResConv) {
    return () => ResConv(F());
  }
  public static Func<U1, U2, UResult> DowncastClone<T1, T2, TResult, U1, U2, UResult>(this Func<T1, T2, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<TResult, UResult> ResConv) {
    return (arg1, arg2) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2)));
  }
  public static Func<U1, U2, U3, UResult> DowncastClone<T1, T2, T3, TResult, U1, U2, U3, UResult>(this Func<T1, T2, T3, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<U3, T3> ArgConv3, Func<TResult, UResult> ResConv) {
    return (arg1, arg2, arg3) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2), ArgConv3(arg3)));
  }
  public static Func<U1, U2, U3, U4, UResult> DowncastClone<T1, T2, T3, T4, TResult, U1, U2, U3, U4, UResult>(this Func<T1, T2, T3, T4, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<U3, T3> ArgConv3, Func<U4, T4> ArgConv4, Func<TResult, UResult> ResConv) {
    return (arg1, arg2, arg3, arg4) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2), ArgConv3(arg3), ArgConv4(arg4)));
  }
  public static Func<U1, U2, U3, U4, U5, UResult> DowncastClone<T1, T2, T3, T4, T5, TResult, U1, U2, U3, U4, U5, UResult>(this Func<T1, T2, T3, T4, T5, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<U3, T3> ArgConv3, Func<U4, T4> ArgConv4, Func<U5, T5> ArgConv5, Func<TResult, UResult> ResConv) {
    return (arg1, arg2, arg3, arg4, arg5) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2), ArgConv3(arg3), ArgConv4(arg4), ArgConv5(arg5)));
  }
}
namespace _System {

  public partial class nat {
    private static readonly Dafny.TypeDescriptor<BigInteger> _TYPE = new Dafny.TypeDescriptor<BigInteger>(BigInteger.Zero);
    public static Dafny.TypeDescriptor<BigInteger> _TypeDescriptor() {
      return _TYPE;
    }
  }
} // end of namespace _System
namespace Wrappers_Compile {

  public interface _IOption<out T> {
    bool is_None { get; }
    bool is_Some { get; }
    T dtor_value { get; }
    _IOption<__T> DowncastClone<__T>(Func<T, __T> converter0);
    Wrappers_Compile._IResult<T, Dafny.ISequence<char>> ToResult();
    Wrappers_Compile._IResult<T, __R> ToResult_k<__R>(__R error);
    bool IsFailure();
    Wrappers_Compile._IOption<__U> PropagateFailure<__U>();
    T Extract();
  }
  public abstract class Option<T> : _IOption<T> {
    public Option() { }
    public static Wrappers_Compile._IOption<T> Default() {
      return create_None();
    }
    public static Dafny.TypeDescriptor<Wrappers_Compile._IOption<T>> _TypeDescriptor() {
      return new Dafny.TypeDescriptor<Wrappers_Compile._IOption<T>>(Wrappers_Compile.Option<T>.Default());
    }
    public static _IOption<T> create_None() {
      return new Option_None<T>();
    }
    public static _IOption<T> create_Some(T @value) {
      return new Option_Some<T>(@value);
    }
    public bool is_None { get { return this is Option_None<T>; } }
    public bool is_Some { get { return this is Option_Some<T>; } }
    public T dtor_value {
      get {
        var d = this;
        return ((Option_Some<T>)d)._value;
      }
    }
    public abstract _IOption<__T> DowncastClone<__T>(Func<T, __T> converter0);
    public Wrappers_Compile._IResult<T, Dafny.ISequence<char>> ToResult() {
      Wrappers_Compile._IOption<T> _source0 = this;
      if (_source0.is_None) {
        return Wrappers_Compile.Result<T, Dafny.ISequence<char>>.create_Failure(Dafny.Sequence<char>.FromString("Option is None"));
      } else {
        T _0___mcc_h0 = _source0.dtor_value;
        T _1_v = _0___mcc_h0;
        return Wrappers_Compile.Result<T, Dafny.ISequence<char>>.create_Success(_1_v);
      }
    }
    public Wrappers_Compile._IResult<T, __R> ToResult_k<__R>(__R error) {
      Wrappers_Compile._IOption<T> _source1 = this;
      if (_source1.is_None) {
        return Wrappers_Compile.Result<T, __R>.create_Failure(error);
      } else {
        T _2___mcc_h0 = _source1.dtor_value;
        T _3_v = _2___mcc_h0;
        return Wrappers_Compile.Result<T, __R>.create_Success(_3_v);
      }
    }
    public static T UnwrapOr(Wrappers_Compile._IOption<T> _this, T @default) {
      Wrappers_Compile._IOption<T> _source2 = _this;
      if (_source2.is_None) {
        return @default;
      } else {
        T _4___mcc_h0 = _source2.dtor_value;
        T _5_v = _4___mcc_h0;
        return _5_v;
      }
    }
    public bool IsFailure() {
      return (this).is_None;
    }
    public Wrappers_Compile._IOption<__U> PropagateFailure<__U>() {
      return Wrappers_Compile.Option<__U>.create_None();
    }
    public T Extract() {
      return (this).dtor_value;
    }
  }
  public class Option_None<T> : Option<T> {
    public Option_None() {
    }
    public override _IOption<__T> DowncastClone<__T>(Func<T, __T> converter0) {
      if (this is _IOption<__T> dt) { return dt; }
      return new Option_None<__T>();
    }
    public override bool Equals(object other) {
      var oth = other as Wrappers_Compile.Option_None<T>;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "Wrappers_Compile.Option.None";
      return s;
    }
  }
  public class Option_Some<T> : Option<T> {
    public readonly T _value;
    public Option_Some(T @value) {
      this._value = @value;
    }
    public override _IOption<__T> DowncastClone<__T>(Func<T, __T> converter0) {
      if (this is _IOption<__T> dt) { return dt; }
      return new Option_Some<__T>(converter0(_value));
    }
    public override bool Equals(object other) {
      var oth = other as Wrappers_Compile.Option_Some<T>;
      return oth != null && object.Equals(this._value, oth._value);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._value));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Wrappers_Compile.Option.Some";
      s += "(";
      s += Dafny.Helpers.ToString(this._value);
      s += ")";
      return s;
    }
  }

  public interface _IResult<out T, out R> {
    bool is_Success { get; }
    bool is_Failure { get; }
    T dtor_value { get; }
    R dtor_error { get; }
    _IResult<__T, __R> DowncastClone<__T, __R>(Func<T, __T> converter0, Func<R, __R> converter1);
    Wrappers_Compile._IOption<T> ToOption();
    bool IsFailure();
    Wrappers_Compile._IResult<__U, R> PropagateFailure<__U>();
    T Extract();
  }
  public abstract class Result<T, R> : _IResult<T, R> {
    public Result() { }
    public static Wrappers_Compile._IResult<T, R> Default(T _default_T) {
      return create_Success(_default_T);
    }
    public static Dafny.TypeDescriptor<Wrappers_Compile._IResult<T, R>> _TypeDescriptor(Dafny.TypeDescriptor<T> _td_T) {
      return new Dafny.TypeDescriptor<Wrappers_Compile._IResult<T, R>>(Wrappers_Compile.Result<T, R>.Default(_td_T.Default()));
    }
    public static _IResult<T, R> create_Success(T @value) {
      return new Result_Success<T, R>(@value);
    }
    public static _IResult<T, R> create_Failure(R error) {
      return new Result_Failure<T, R>(error);
    }
    public bool is_Success { get { return this is Result_Success<T, R>; } }
    public bool is_Failure { get { return this is Result_Failure<T, R>; } }
    public T dtor_value {
      get {
        var d = this;
        return ((Result_Success<T, R>)d)._value;
      }
    }
    public R dtor_error {
      get {
        var d = this;
        return ((Result_Failure<T, R>)d)._error;
      }
    }
    public abstract _IResult<__T, __R> DowncastClone<__T, __R>(Func<T, __T> converter0, Func<R, __R> converter1);
    public Wrappers_Compile._IOption<T> ToOption() {
      Wrappers_Compile._IResult<T, R> _source3 = this;
      if (_source3.is_Success) {
        T _6___mcc_h0 = _source3.dtor_value;
        T _7_s = _6___mcc_h0;
        return Wrappers_Compile.Option<T>.create_Some(_7_s);
      } else {
        R _8___mcc_h1 = _source3.dtor_error;
        R _9_e = _8___mcc_h1;
        return Wrappers_Compile.Option<T>.create_None();
      }
    }
    public static T UnwrapOr(Wrappers_Compile._IResult<T, R> _this, T @default) {
      Wrappers_Compile._IResult<T, R> _source4 = _this;
      if (_source4.is_Success) {
        T _10___mcc_h0 = _source4.dtor_value;
        T _11_s = _10___mcc_h0;
        return _11_s;
      } else {
        R _12___mcc_h1 = _source4.dtor_error;
        R _13_e = _12___mcc_h1;
        return @default;
      }
    }
    public bool IsFailure() {
      return (this).is_Failure;
    }
    public Wrappers_Compile._IResult<__U, R> PropagateFailure<__U>() {
      return Wrappers_Compile.Result<__U, R>.create_Failure((this).dtor_error);
    }
    public static Wrappers_Compile._IResult<T, __NewR> MapFailure<__NewR>(Wrappers_Compile._IResult<T, R> _this, Func<R, __NewR> reWrap) {
      Wrappers_Compile._IResult<T, R> _source5 = _this;
      if (_source5.is_Success) {
        T _14___mcc_h0 = _source5.dtor_value;
        T _15_s = _14___mcc_h0;
        return Wrappers_Compile.Result<T, __NewR>.create_Success(_15_s);
      } else {
        R _16___mcc_h1 = _source5.dtor_error;
        R _17_e = _16___mcc_h1;
        return Wrappers_Compile.Result<T, __NewR>.create_Failure(Dafny.Helpers.Id<Func<R, __NewR>>(reWrap)(_17_e));
      }
    }
    public T Extract() {
      return (this).dtor_value;
    }
  }
  public class Result_Success<T, R> : Result<T, R> {
    public readonly T _value;
    public Result_Success(T @value) {
      this._value = @value;
    }
    public override _IResult<__T, __R> DowncastClone<__T, __R>(Func<T, __T> converter0, Func<R, __R> converter1) {
      if (this is _IResult<__T, __R> dt) { return dt; }
      return new Result_Success<__T, __R>(converter0(_value));
    }
    public override bool Equals(object other) {
      var oth = other as Wrappers_Compile.Result_Success<T, R>;
      return oth != null && object.Equals(this._value, oth._value);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._value));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Wrappers_Compile.Result.Success";
      s += "(";
      s += Dafny.Helpers.ToString(this._value);
      s += ")";
      return s;
    }
  }
  public class Result_Failure<T, R> : Result<T, R> {
    public readonly R _error;
    public Result_Failure(R error) {
      this._error = error;
    }
    public override _IResult<__T, __R> DowncastClone<__T, __R>(Func<T, __T> converter0, Func<R, __R> converter1) {
      if (this is _IResult<__T, __R> dt) { return dt; }
      return new Result_Failure<__T, __R>(converter1(_error));
    }
    public override bool Equals(object other) {
      var oth = other as Wrappers_Compile.Result_Failure<T, R>;
      return oth != null && object.Equals(this._error, oth._error);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._error));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Wrappers_Compile.Result.Failure";
      s += "(";
      s += Dafny.Helpers.ToString(this._error);
      s += ")";
      return s;
    }
  }

  public interface _IOutcome<E> {
    bool is_Pass { get; }
    bool is_Fail { get; }
    E dtor_error { get; }
    _IOutcome<__E> DowncastClone<__E>(Func<E, __E> converter0);
    bool IsFailure();
    Wrappers_Compile._IResult<__U, E> PropagateFailure<__U>();
  }
  public abstract class Outcome<E> : _IOutcome<E> {
    public Outcome() { }
    public static Wrappers_Compile._IOutcome<E> Default() {
      return create_Pass();
    }
    public static Dafny.TypeDescriptor<Wrappers_Compile._IOutcome<E>> _TypeDescriptor() {
      return new Dafny.TypeDescriptor<Wrappers_Compile._IOutcome<E>>(Wrappers_Compile.Outcome<E>.Default());
    }
    public static _IOutcome<E> create_Pass() {
      return new Outcome_Pass<E>();
    }
    public static _IOutcome<E> create_Fail(E error) {
      return new Outcome_Fail<E>(error);
    }
    public bool is_Pass { get { return this is Outcome_Pass<E>; } }
    public bool is_Fail { get { return this is Outcome_Fail<E>; } }
    public E dtor_error {
      get {
        var d = this;
        return ((Outcome_Fail<E>)d)._error;
      }
    }
    public abstract _IOutcome<__E> DowncastClone<__E>(Func<E, __E> converter0);
    public bool IsFailure() {
      return (this).is_Fail;
    }
    public Wrappers_Compile._IResult<__U, E> PropagateFailure<__U>() {
      return Wrappers_Compile.Result<__U, E>.create_Failure((this).dtor_error);
    }
  }
  public class Outcome_Pass<E> : Outcome<E> {
    public Outcome_Pass() {
    }
    public override _IOutcome<__E> DowncastClone<__E>(Func<E, __E> converter0) {
      if (this is _IOutcome<__E> dt) { return dt; }
      return new Outcome_Pass<__E>();
    }
    public override bool Equals(object other) {
      var oth = other as Wrappers_Compile.Outcome_Pass<E>;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "Wrappers_Compile.Outcome.Pass";
      return s;
    }
  }
  public class Outcome_Fail<E> : Outcome<E> {
    public readonly E _error;
    public Outcome_Fail(E error) {
      this._error = error;
    }
    public override _IOutcome<__E> DowncastClone<__E>(Func<E, __E> converter0) {
      if (this is _IOutcome<__E> dt) { return dt; }
      return new Outcome_Fail<__E>(converter0(_error));
    }
    public override bool Equals(object other) {
      var oth = other as Wrappers_Compile.Outcome_Fail<E>;
      return oth != null && object.Equals(this._error, oth._error);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._error));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Wrappers_Compile.Outcome.Fail";
      s += "(";
      s += Dafny.Helpers.ToString(this._error);
      s += ")";
      return s;
    }
  }

  public partial class __default {
    public static Wrappers_Compile._IOutcome<__E> Need<__E>(bool condition, __E error)
    {
      if (condition) {
        return Wrappers_Compile.Outcome<__E>.create_Pass();
      } else {
        return Wrappers_Compile.Outcome<__E>.create_Fail(error);
      }
    }
  }
} // end of namespace Wrappers_Compile
namespace DafnyLibraries {

  public interface MutableMapTrait<K, V> {
    Dafny.IMap<K,V> content();
    void Put(K k, V v);
    Dafny.ISet<K> Keys();
    bool HasKey(K k);
    Dafny.ISet<V> Values();
    Dafny.ISet<_System._ITuple2<K, V>> Items();
    V Select(K k);
    void Remove(K k);
    BigInteger Size();
  }
  public class _Companion_MutableMapTrait<K, V> {
  }

  public partial class MutableMap<K, V> : DafnyLibraries.MutableMapTrait<K, V> {
    public Wrappers_Compile._IOption<V> SelectOpt(K k) {
      if ((this).HasKey(k)) {
        return Wrappers_Compile.Option<V>.create_Some((this).Select(k));
      } else {
        return Wrappers_Compile.Option<V>.create_None();
      }
    }
  }

} // end of namespace DafnyLibraries
namespace Relations_Compile {

} // end of namespace Relations_Compile
namespace Seq_mMergeSort_Compile {

  public partial class __default {
    public static Dafny.ISequence<__T> MergeSortBy<__T>(Dafny.ISequence<__T> a, Func<__T, __T, bool> lessThanOrEq)
    {
      if ((new BigInteger((a).Count)) <= (BigInteger.One)) {
        return a;
      } else {
        BigInteger _18_splitIndex = Dafny.Helpers.EuclideanDivision(new BigInteger((a).Count), new BigInteger(2));
        Dafny.ISequence<__T> _19_left = (a).Take(_18_splitIndex);
        Dafny.ISequence<__T> _20_right = (a).Drop(_18_splitIndex);
        Dafny.ISequence<__T> _21_leftSorted = Seq_mMergeSort_Compile.__default.MergeSortBy<__T>(_19_left, lessThanOrEq);
        Dafny.ISequence<__T> _22_rightSorted = Seq_mMergeSort_Compile.__default.MergeSortBy<__T>(_20_right, lessThanOrEq);
        return Seq_mMergeSort_Compile.__default.MergeSortedWith<__T>(_21_leftSorted, _22_rightSorted, lessThanOrEq);
      }
    }
    public static Dafny.ISequence<__T> MergeSortedWith<__T>(Dafny.ISequence<__T> left, Dafny.ISequence<__T> right, Func<__T, __T, bool> lessThanOrEq)
    {
      Dafny.ISequence<__T> _23___accumulator = Dafny.Sequence<__T>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((left).Count)).Sign == 0) {
        return Dafny.Sequence<__T>.Concat(_23___accumulator, right);
      } else if ((new BigInteger((right).Count)).Sign == 0) {
        return Dafny.Sequence<__T>.Concat(_23___accumulator, left);
      } else if (Dafny.Helpers.Id<Func<__T, __T, bool>>(lessThanOrEq)((left).Select(BigInteger.Zero), (right).Select(BigInteger.Zero))) {
        _23___accumulator = Dafny.Sequence<__T>.Concat(_23___accumulator, Dafny.Sequence<__T>.FromElements((left).Select(BigInteger.Zero)));
        Dafny.ISequence<__T> _in0 = (left).Drop(BigInteger.One);
        Dafny.ISequence<__T> _in1 = right;
        Func<__T, __T, bool> _in2 = lessThanOrEq;
        left = _in0;
        right = _in1;
        lessThanOrEq = _in2;
        goto TAIL_CALL_START;
      } else {
        _23___accumulator = Dafny.Sequence<__T>.Concat(_23___accumulator, Dafny.Sequence<__T>.FromElements((right).Select(BigInteger.Zero)));
        Dafny.ISequence<__T> _in3 = left;
        Dafny.ISequence<__T> _in4 = (right).Drop(BigInteger.One);
        Func<__T, __T, bool> _in5 = lessThanOrEq;
        left = _in3;
        right = _in4;
        lessThanOrEq = _in5;
        goto TAIL_CALL_START;
      }
    }
  }
} // end of namespace Seq_mMergeSort_Compile
namespace Math_Compile {

  public partial class __default {
    public static BigInteger Min(BigInteger a, BigInteger b)
    {
      if ((a) < (b)) {
        return a;
      } else {
        return b;
      }
    }
    public static BigInteger Max(BigInteger a, BigInteger b)
    {
      if ((a) < (b)) {
        return b;
      } else {
        return a;
      }
    }
    public static BigInteger Abs(BigInteger a) {
      if ((a).Sign != -1) {
        return a;
      } else {
        return (BigInteger.Zero) - (a);
      }
    }
  }
} // end of namespace Math_Compile
namespace Seq_Compile {

  public partial class __default {
    public static __T First<__T>(Dafny.ISequence<__T> xs) {
      return (xs).Select(BigInteger.Zero);
    }
    public static Dafny.ISequence<__T> DropFirst<__T>(Dafny.ISequence<__T> xs) {
      return (xs).Drop(BigInteger.One);
    }
    public static __T Last<__T>(Dafny.ISequence<__T> xs) {
      return (xs).Select((new BigInteger((xs).Count)) - (BigInteger.One));
    }
    public static Dafny.ISequence<__T> DropLast<__T>(Dafny.ISequence<__T> xs) {
      return (xs).Take((new BigInteger((xs).Count)) - (BigInteger.One));
    }
    public static __T[] ToArray<__T>(Dafny.ISequence<__T> xs)
    {
      __T[] a = new __T[0];
      Func<BigInteger, __T> _init0 = Dafny.Helpers.Id<Func<Dafny.ISequence<__T>, Func<BigInteger, __T>>>((_24_xs) => ((System.Func<BigInteger, __T>)((_25_i) => {
        return (_24_xs).Select(_25_i);
      })))(xs);
      __T[] _nw0 = new __T[Dafny.Helpers.ToIntChecked(new BigInteger((xs).Count), "array size exceeds memory limit")];
      for (var _i0_0 = 0; _i0_0 < new BigInteger(_nw0.Length); _i0_0++) {
        _nw0[(int)(_i0_0)] = _init0(_i0_0);
      }
      a = _nw0;
      return a;
    }
    public static Dafny.ISet<__T> ToSet<__T>(Dafny.ISequence<__T> xs) {
      return Dafny.Helpers.Id<Func<Dafny.ISequence<__T>, Dafny.ISet<__T>>>((_26_xs) => ((System.Func<Dafny.ISet<__T>>)(() => {
        var _coll0 = new System.Collections.Generic.List<__T>();
        foreach (__T _compr_0 in (_26_xs).Elements) {
          __T _27_x = (__T)_compr_0;
          if ((_26_xs).Contains(_27_x)) {
            _coll0.Add(_27_x);
          }
        }
        return Dafny.Set<__T>.FromCollection(_coll0);
      }))())(xs);
    }
    public static BigInteger IndexOf<__T>(Dafny.ISequence<__T> xs, __T v)
    {
      BigInteger _28___accumulator = BigInteger.Zero;
    TAIL_CALL_START: ;
      if (object.Equals((xs).Select(BigInteger.Zero), v)) {
        return (BigInteger.Zero) + (_28___accumulator);
      } else {
        _28___accumulator = (_28___accumulator) + (BigInteger.One);
        Dafny.ISequence<__T> _in6 = (xs).Drop(BigInteger.One);
        __T _in7 = v;
        xs = _in6;
        v = _in7;
        goto TAIL_CALL_START;
      }
    }
    public static Wrappers_Compile._IOption<BigInteger> IndexOfOption<__T>(Dafny.ISequence<__T> xs, __T v)
    {
      if ((new BigInteger((xs).Count)).Sign == 0) {
        return Wrappers_Compile.Option<BigInteger>.create_None();
      } else if (object.Equals((xs).Select(BigInteger.Zero), v)) {
        return Wrappers_Compile.Option<BigInteger>.create_Some(BigInteger.Zero);
      } else {
        Wrappers_Compile._IOption<BigInteger> _29_o_k = Seq_Compile.__default.IndexOfOption<__T>((xs).Drop(BigInteger.One), v);
        if ((_29_o_k).is_Some) {
          return Wrappers_Compile.Option<BigInteger>.create_Some(((_29_o_k).dtor_value) + (BigInteger.One));
        } else {
          return Wrappers_Compile.Option<BigInteger>.create_None();
        }
      }
    }
    public static BigInteger LastIndexOf<__T>(Dafny.ISequence<__T> xs, __T v)
    {
    TAIL_CALL_START: ;
      if (object.Equals((xs).Select((new BigInteger((xs).Count)) - (BigInteger.One)), v)) {
        return (new BigInteger((xs).Count)) - (BigInteger.One);
      } else {
        Dafny.ISequence<__T> _in8 = (xs).Take((new BigInteger((xs).Count)) - (BigInteger.One));
        __T _in9 = v;
        xs = _in8;
        v = _in9;
        goto TAIL_CALL_START;
      }
    }
    public static Wrappers_Compile._IOption<BigInteger> LastIndexOfOption<__T>(Dafny.ISequence<__T> xs, __T v)
    {
    TAIL_CALL_START: ;
      if ((new BigInteger((xs).Count)).Sign == 0) {
        return Wrappers_Compile.Option<BigInteger>.create_None();
      } else if (object.Equals((xs).Select((new BigInteger((xs).Count)) - (BigInteger.One)), v)) {
        return Wrappers_Compile.Option<BigInteger>.create_Some((new BigInteger((xs).Count)) - (BigInteger.One));
      } else {
        Dafny.ISequence<__T> _in10 = (xs).Take((new BigInteger((xs).Count)) - (BigInteger.One));
        __T _in11 = v;
        xs = _in10;
        v = _in11;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<__T> Remove<__T>(Dafny.ISequence<__T> xs, BigInteger pos)
    {
      return Dafny.Sequence<__T>.Concat((xs).Take(pos), (xs).Drop((pos) + (BigInteger.One)));
    }
    public static Dafny.ISequence<__T> RemoveValue<__T>(Dafny.ISequence<__T> xs, __T v)
    {
      if (!(xs).Contains(v)) {
        return xs;
      } else {
        BigInteger _30_i = Seq_Compile.__default.IndexOf<__T>(xs, v);
        return Dafny.Sequence<__T>.Concat((xs).Take(_30_i), (xs).Drop((_30_i) + (BigInteger.One)));
      }
    }
    public static Dafny.ISequence<__T> Insert<__T>(Dafny.ISequence<__T> xs, __T a, BigInteger pos)
    {
      return Dafny.Sequence<__T>.Concat(Dafny.Sequence<__T>.Concat((xs).Take(pos), Dafny.Sequence<__T>.FromElements(a)), (xs).Drop(pos));
    }
    public static Dafny.ISequence<__T> Reverse<__T>(Dafny.ISequence<__T> xs) {
      Dafny.ISequence<__T> _31___accumulator = Dafny.Sequence<__T>.FromElements();
    TAIL_CALL_START: ;
      if ((xs).Equals(Dafny.Sequence<__T>.FromElements())) {
        return Dafny.Sequence<__T>.Concat(_31___accumulator, Dafny.Sequence<__T>.FromElements());
      } else {
        _31___accumulator = Dafny.Sequence<__T>.Concat(_31___accumulator, Dafny.Sequence<__T>.FromElements((xs).Select((new BigInteger((xs).Count)) - (BigInteger.One))));
        Dafny.ISequence<__T> _in12 = (xs).Subsequence(BigInteger.Zero, (new BigInteger((xs).Count)) - (BigInteger.One));
        xs = _in12;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<__T> Repeat<__T>(__T v, BigInteger length)
    {
      Dafny.ISequence<__T> _32___accumulator = Dafny.Sequence<__T>.FromElements();
    TAIL_CALL_START: ;
      if ((length).Sign == 0) {
        return Dafny.Sequence<__T>.Concat(_32___accumulator, Dafny.Sequence<__T>.FromElements());
      } else {
        _32___accumulator = Dafny.Sequence<__T>.Concat(_32___accumulator, Dafny.Sequence<__T>.FromElements(v));
        __T _in13 = v;
        BigInteger _in14 = (length) - (BigInteger.One);
        v = _in13;
        length = _in14;
        goto TAIL_CALL_START;
      }
    }
    public static _System._ITuple2<Dafny.ISequence<__A>, Dafny.ISequence<__B>> Unzip<__A, __B>(Dafny.ISequence<_System._ITuple2<__A, __B>> xs) {
      if ((new BigInteger((xs).Count)).Sign == 0) {
        return _System.Tuple2<Dafny.ISequence<__A>, Dafny.ISequence<__B>>.create(Dafny.Sequence<__A>.FromElements(), Dafny.Sequence<__B>.FromElements());
      } else {
        _System._ITuple2<Dafny.ISequence<__A>, Dafny.ISequence<__B>> _let_tmp_rhs0 = Seq_Compile.__default.Unzip<__A, __B>(Seq_Compile.__default.DropLast<_System._ITuple2<__A, __B>>(xs));
        Dafny.ISequence<__A> _33_a = _let_tmp_rhs0.dtor__0;
        Dafny.ISequence<__B> _34_b = _let_tmp_rhs0.dtor__1;
        return _System.Tuple2<Dafny.ISequence<__A>, Dafny.ISequence<__B>>.create(Dafny.Sequence<__A>.Concat(_33_a, Dafny.Sequence<__A>.FromElements((Seq_Compile.__default.Last<_System._ITuple2<__A, __B>>(xs)).dtor__0)), Dafny.Sequence<__B>.Concat(_34_b, Dafny.Sequence<__B>.FromElements((Seq_Compile.__default.Last<_System._ITuple2<__A, __B>>(xs)).dtor__1)));
      }
    }
    public static Dafny.ISequence<_System._ITuple2<__A, __B>> Zip<__A, __B>(Dafny.ISequence<__A> xs, Dafny.ISequence<__B> ys)
    {
      Dafny.ISequence<_System._ITuple2<__A, __B>> _35___accumulator = Dafny.Sequence<_System._ITuple2<__A, __B>>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((xs).Count)).Sign == 0) {
        return Dafny.Sequence<_System._ITuple2<__A, __B>>.Concat(Dafny.Sequence<_System._ITuple2<__A, __B>>.FromElements(), _35___accumulator);
      } else {
        _35___accumulator = Dafny.Sequence<_System._ITuple2<__A, __B>>.Concat(Dafny.Sequence<_System._ITuple2<__A, __B>>.FromElements(_System.Tuple2<__A, __B>.create(Seq_Compile.__default.Last<__A>(xs), Seq_Compile.__default.Last<__B>(ys))), _35___accumulator);
        Dafny.ISequence<__A> _in15 = Seq_Compile.__default.DropLast<__A>(xs);
        Dafny.ISequence<__B> _in16 = Seq_Compile.__default.DropLast<__B>(ys);
        xs = _in15;
        ys = _in16;
        goto TAIL_CALL_START;
      }
    }
    public static BigInteger Max(Dafny.ISequence<BigInteger> xs) {
      if ((new BigInteger((xs).Count)) == (BigInteger.One)) {
        return (xs).Select(BigInteger.Zero);
      } else {
        return Math_Compile.__default.Max((xs).Select(BigInteger.Zero), Seq_Compile.__default.Max((xs).Drop(BigInteger.One)));
      }
    }
    public static BigInteger Min(Dafny.ISequence<BigInteger> xs) {
      if ((new BigInteger((xs).Count)) == (BigInteger.One)) {
        return (xs).Select(BigInteger.Zero);
      } else {
        return Math_Compile.__default.Min((xs).Select(BigInteger.Zero), Seq_Compile.__default.Min((xs).Drop(BigInteger.One)));
      }
    }
    public static Dafny.ISequence<__T> Flatten<__T>(Dafny.ISequence<Dafny.ISequence<__T>> xs) {
      Dafny.ISequence<__T> _36___accumulator = Dafny.Sequence<__T>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((xs).Count)).Sign == 0) {
        return Dafny.Sequence<__T>.Concat(_36___accumulator, Dafny.Sequence<__T>.FromElements());
      } else {
        _36___accumulator = Dafny.Sequence<__T>.Concat(_36___accumulator, (xs).Select(BigInteger.Zero));
        Dafny.ISequence<Dafny.ISequence<__T>> _in17 = (xs).Drop(BigInteger.One);
        xs = _in17;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<__T> FlattenReverse<__T>(Dafny.ISequence<Dafny.ISequence<__T>> xs) {
      Dafny.ISequence<__T> _37___accumulator = Dafny.Sequence<__T>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((xs).Count)).Sign == 0) {
        return Dafny.Sequence<__T>.Concat(Dafny.Sequence<__T>.FromElements(), _37___accumulator);
      } else {
        _37___accumulator = Dafny.Sequence<__T>.Concat(Seq_Compile.__default.Last<Dafny.ISequence<__T>>(xs), _37___accumulator);
        Dafny.ISequence<Dafny.ISequence<__T>> _in18 = Seq_Compile.__default.DropLast<Dafny.ISequence<__T>>(xs);
        xs = _in18;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<__R> Map<__T, __R>(Func<__T, __R> f, Dafny.ISequence<__T> xs)
    {
      return ((System.Func<Dafny.ISequence<__R>>) (() => {
        BigInteger dim0 = new BigInteger((xs).Count);
        var arr0 = new __R[Dafny.Helpers.ToIntChecked(dim0, "array size exceeds memory limit")];
        for (int i0 = 0; i0 < dim0; i0++) {
          var _38_i = (BigInteger) i0;
          arr0[(int)(_38_i)] = Dafny.Helpers.Id<Func<__T, __R>>(f)((xs).Select(_38_i));
        }
        return Dafny.Sequence<__R>.FromArray(arr0);
      }))();
    }
    public static Wrappers_Compile._IResult<Dafny.ISequence<__R>, __E> MapWithResult<__T, __R, __E>(Func<__T, Wrappers_Compile._IResult<__R, __E>> f, Dafny.ISequence<__T> xs)
    {
      if ((new BigInteger((xs).Count)).Sign == 0) {
        return Wrappers_Compile.Result<Dafny.ISequence<__R>, __E>.create_Success(Dafny.Sequence<__R>.FromElements());
      } else {
        Wrappers_Compile._IResult<__R, __E> _39_valueOrError0 = Dafny.Helpers.Id<Func<__T, Wrappers_Compile._IResult<__R, __E>>>(f)((xs).Select(BigInteger.Zero));
        if ((_39_valueOrError0).IsFailure()) {
          return (_39_valueOrError0).PropagateFailure<Dafny.ISequence<__R>>();
        } else {
          __R _40_head = (_39_valueOrError0).Extract();
          Wrappers_Compile._IResult<Dafny.ISequence<__R>, __E> _41_valueOrError1 = Seq_Compile.__default.MapWithResult<__T, __R, __E>(f, (xs).Drop(BigInteger.One));
          if ((_41_valueOrError1).IsFailure()) {
            return (_41_valueOrError1).PropagateFailure<Dafny.ISequence<__R>>();
          } else {
            Dafny.ISequence<__R> _42_tail = (_41_valueOrError1).Extract();
            return Wrappers_Compile.Result<Dafny.ISequence<__R>, __E>.create_Success(Dafny.Sequence<__R>.Concat(Dafny.Sequence<__R>.FromElements(_40_head), _42_tail));
          }
        }
      }
    }
    public static Dafny.ISequence<__T> Filter<__T>(Func<__T, bool> f, Dafny.ISequence<__T> xs)
    {
      Dafny.ISequence<__T> _43___accumulator = Dafny.Sequence<__T>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((xs).Count)).Sign == 0) {
        return Dafny.Sequence<__T>.Concat(_43___accumulator, Dafny.Sequence<__T>.FromElements());
      } else {
        _43___accumulator = Dafny.Sequence<__T>.Concat(_43___accumulator, ((Dafny.Helpers.Id<Func<__T, bool>>(f)((xs).Select(BigInteger.Zero))) ? (Dafny.Sequence<__T>.FromElements((xs).Select(BigInteger.Zero))) : (Dafny.Sequence<__T>.FromElements())));
        Func<__T, bool> _in19 = f;
        Dafny.ISequence<__T> _in20 = (xs).Drop(BigInteger.One);
        f = _in19;
        xs = _in20;
        goto TAIL_CALL_START;
      }
    }
    public static __A FoldLeft<__A, __T>(Func<__A, __T, __A> f, __A init, Dafny.ISequence<__T> xs)
    {
    TAIL_CALL_START: ;
      if ((new BigInteger((xs).Count)).Sign == 0) {
        return init;
      } else {
        Func<__A, __T, __A> _in21 = f;
        __A _in22 = Dafny.Helpers.Id<Func<__A, __T, __A>>(f)(init, (xs).Select(BigInteger.Zero));
        Dafny.ISequence<__T> _in23 = (xs).Drop(BigInteger.One);
        f = _in21;
        init = _in22;
        xs = _in23;
        goto TAIL_CALL_START;
      }
    }
    public static __A FoldRight<__A, __T>(Func<__T, __A, __A> f, Dafny.ISequence<__T> xs, __A init)
    {
      if ((new BigInteger((xs).Count)).Sign == 0) {
        return init;
      } else {
        return Dafny.Helpers.Id<Func<__T, __A, __A>>(f)((xs).Select(BigInteger.Zero), Seq_Compile.__default.FoldRight<__A, __T>(f, (xs).Drop(BigInteger.One), init));
      }
    }
    public static Dafny.ISequence<__R> FlatMap<__T, __R>(Func<__T, Dafny.ISequence<__R>> f, Dafny.ISequence<__T> xs)
    {
      Dafny.ISequence<__R> result = Dafny.Sequence<__R>.Empty;
      result = Dafny.Sequence<__R>.FromElements();
      BigInteger _lo0 = BigInteger.Zero;
      for (BigInteger _44_i = new BigInteger((xs).Count); _lo0 < _44_i; ) {
        _44_i--;
        Dafny.ISequence<__R> _45_next;
        _45_next = Dafny.Helpers.Id<Func<__T, Dafny.ISequence<__R>>>(f)((xs).Select(_44_i));
        result = Dafny.Sequence<__R>.Concat(_45_next, result);
      }
      return result;
    }
    public static Dafny.ISequence<__T> SetToSeq<__T>(Dafny.ISet<__T> s)
    {
      Dafny.ISequence<__T> xs = Dafny.Sequence<__T>.Empty;
      xs = Dafny.Sequence<__T>.FromElements();
      Dafny.ISet<__T> _46_left;
      _46_left = s;
      while (!(_46_left).Equals(Dafny.Set<__T>.FromElements())) {
        __T _47_x;
        foreach (__T _assign_such_that_0 in (_46_left).Elements) {
          _47_x = (__T)_assign_such_that_0;
          if ((_46_left).Contains(_47_x)) {
            goto after__ASSIGN_SUCH_THAT_0;
          }
        }
        throw new System.Exception("assign-such-that search produced no value (line 872)");
      after__ASSIGN_SUCH_THAT_0: ;
        _46_left = Dafny.Set<__T>.Difference(_46_left, Dafny.Set<__T>.FromElements(_47_x));
        xs = Dafny.Sequence<__T>.Concat(xs, Dafny.Sequence<__T>.FromElements(_47_x));
      }
      return xs;
    }
    public static Dafny.ISequence<__T> SetToSortedSeq<__T>(Dafny.ISet<__T> s, Func<__T, __T, bool> R)
    {
      Dafny.ISequence<__T> xs = Dafny.Sequence<__T>.Empty;
      Dafny.ISequence<__T> _out0;
      _out0 = Seq_Compile.__default.SetToSeq<__T>(s);
      xs = _out0;
      xs = Seq_mMergeSort_Compile.__default.MergeSortBy<__T>(xs, R);
      return xs;
    }
  }
} // end of namespace Seq_Compile
namespace Actions_Compile {

  public interface _IActionInvoke<A, R> {
    bool is_ActionInvoke { get; }
    A dtor_input { get; }
    R dtor_output { get; }
    _IActionInvoke<__A, __R> DowncastClone<__A, __R>(Func<A, __A> converter0, Func<R, __R> converter1);
  }
  public class ActionInvoke<A, R> : _IActionInvoke<A, R> {
    public readonly A _input;
    public readonly R _output;
    public ActionInvoke(A input, R output) {
      this._input = input;
      this._output = output;
    }
    public _IActionInvoke<__A, __R> DowncastClone<__A, __R>(Func<A, __A> converter0, Func<R, __R> converter1) {
      if (this is _IActionInvoke<__A, __R> dt) { return dt; }
      return new ActionInvoke<__A, __R>(converter0(_input), converter1(_output));
    }
    public override bool Equals(object other) {
      var oth = other as Actions_Compile.ActionInvoke<A, R>;
      return oth != null && object.Equals(this._input, oth._input) && object.Equals(this._output, oth._output);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._input));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._output));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Actions_Compile.ActionInvoke.ActionInvoke";
      s += "(";
      s += Dafny.Helpers.ToString(this._input);
      s += ", ";
      s += Dafny.Helpers.ToString(this._output);
      s += ")";
      return s;
    }
    public static Actions_Compile._IActionInvoke<A, R> Default(A _default_A, R _default_R) {
      return create(_default_A, _default_R);
    }
    public static Dafny.TypeDescriptor<Actions_Compile._IActionInvoke<A, R>> _TypeDescriptor(Dafny.TypeDescriptor<A> _td_A, Dafny.TypeDescriptor<R> _td_R) {
      return new Dafny.TypeDescriptor<Actions_Compile._IActionInvoke<A, R>>(Actions_Compile.ActionInvoke<A, R>.Default(_td_A.Default(), _td_R.Default()));
    }
    public static _IActionInvoke<A, R> create(A input, R output) {
      return new ActionInvoke<A, R>(input, output);
    }
    public static _IActionInvoke<A, R> create_ActionInvoke(A input, R output) {
      return create(input, output);
    }
    public bool is_ActionInvoke { get { return true; } }
    public A dtor_input {
      get {
        return this._input;
      }
    }
    public R dtor_output {
      get {
        return this._output;
      }
    }
  }

  public interface Action<A, R> {
    R Invoke(A a);
  }
  public class _Companion_Action<A, R> {
  }

  public interface ActionWithResult<A, R, E> : Actions_Compile.Action<A, Wrappers_Compile._IResult<R, E>> {
  }
  public class _Companion_ActionWithResult<A, R, E> {
  }

  public interface DeterministicAction<A, R> {
    R Invoke(A a);
  }
  public class _Companion_DeterministicAction<A, R> {
  }

  public interface DeterministicActionWithResult<A, R, E> : Actions_Compile.DeterministicAction<A, Wrappers_Compile._IResult<R, E>> {
  }
  public class _Companion_DeterministicActionWithResult<A, R, E> {
  }

  public partial class __default {
    public static Dafny.ISequence<__R> DeterministicMap<__A, __R>(Actions_Compile.DeterministicAction<__A, __R> action, Dafny.ISequence<__A> s)
    {
      Dafny.ISequence<__R> res = Dafny.Sequence<__R>.Empty;
      Dafny.ISequence<__R> _48_rs;
      _48_rs = Dafny.Sequence<__R>.FromElements();
      BigInteger _hi0 = new BigInteger((s).Count);
      for (BigInteger _49_i = BigInteger.Zero; _49_i < _hi0; _49_i++) {
        __R _50_r;
        __R _out1;
        _out1 = (action).Invoke((s).Select(_49_i));
        _50_r = _out1;
        _48_rs = Dafny.Sequence<__R>.Concat(_48_rs, Dafny.Sequence<__R>.FromElements(_50_r));
      }
      res = _48_rs;
      return res;
      return res;
    }
    public static Wrappers_Compile._IResult<Dafny.ISequence<__R>, __E> DeterministicMapWithResult<__A, __R, __E>(Actions_Compile.DeterministicActionWithResult<__A, __R, __E> action, Dafny.ISequence<__A> s)
    {
      Wrappers_Compile._IResult<Dafny.ISequence<__R>, __E> res = Wrappers_Compile.Result<Dafny.ISequence<__R>, __E>.Default(Dafny.Sequence<__R>.Empty);
      Dafny.ISequence<__R> _51_rs;
      _51_rs = Dafny.Sequence<__R>.FromElements();
      BigInteger _hi1 = new BigInteger((s).Count);
      for (BigInteger _52_i = BigInteger.Zero; _52_i < _hi1; _52_i++) {
        __R _53_r;
        Wrappers_Compile._IResult<__R, __E> _54_valueOrError0 = default(Wrappers_Compile._IResult<__R, __E>);
        Wrappers_Compile._IResult<__R, __E> _out2;
        _out2 = (action).Invoke((s).Select(_52_i));
        _54_valueOrError0 = _out2;
        if ((_54_valueOrError0).IsFailure()) {
          res = (_54_valueOrError0).PropagateFailure<Dafny.ISequence<__R>>();
          return res;
        }
        _53_r = (_54_valueOrError0).Extract();
        _51_rs = Dafny.Sequence<__R>.Concat(_51_rs, Dafny.Sequence<__R>.FromElements(_53_r));
      }
      res = Wrappers_Compile.Result<Dafny.ISequence<__R>, __E>.create_Success(_51_rs);
      return res;
      return res;
    }
    public static Dafny.ISequence<__R> DeterministicFlatMap<__A, __R>(Actions_Compile.DeterministicAction<__A, Dafny.ISequence<__R>> action, Dafny.ISequence<__A> s)
    {
      Dafny.ISequence<__R> res = Dafny.Sequence<__R>.Empty;
      Dafny.ISequence<__R> _55_rs;
      _55_rs = Dafny.Sequence<__R>.FromElements();
      BigInteger _hi2 = new BigInteger((s).Count);
      for (BigInteger _56_i = BigInteger.Zero; _56_i < _hi2; _56_i++) {
        Dafny.ISequence<__R> _57_r;
        Dafny.ISequence<__R> _out3;
        _out3 = (action).Invoke((s).Select(_56_i));
        _57_r = _out3;
        _55_rs = Dafny.Sequence<__R>.Concat(_55_rs, _57_r);
      }
      res = _55_rs;
      return res;
      return res;
    }
    public static Wrappers_Compile._IResult<Dafny.ISequence<__R>, __E> DeterministicFlatMapWithResult<__A, __R, __E>(Actions_Compile.DeterministicActionWithResult<__A, Dafny.ISequence<__R>, __E> action, Dafny.ISequence<__A> s)
    {
      Wrappers_Compile._IResult<Dafny.ISequence<__R>, __E> res = Wrappers_Compile.Result<Dafny.ISequence<__R>, __E>.Default(Dafny.Sequence<__R>.Empty);
      Dafny.ISequence<__R> _58_rs;
      _58_rs = Dafny.Sequence<__R>.FromElements();
      BigInteger _hi3 = new BigInteger((s).Count);
      for (BigInteger _59_i = BigInteger.Zero; _59_i < _hi3; _59_i++) {
        Dafny.ISequence<__R> _60_r;
        Wrappers_Compile._IResult<Dafny.ISequence<__R>, __E> _61_valueOrError0 = Wrappers_Compile.Result<Dafny.ISequence<__R>, __E>.Default(Dafny.Sequence<__R>.Empty);
        Wrappers_Compile._IResult<Dafny.ISequence<__R>, __E> _out4;
        _out4 = (action).Invoke((s).Select(_59_i));
        _61_valueOrError0 = _out4;
        if ((_61_valueOrError0).IsFailure()) {
          res = (_61_valueOrError0).PropagateFailure<Dafny.ISequence<__R>>();
          return res;
        }
        _60_r = (_61_valueOrError0).Extract();
        _58_rs = Dafny.Sequence<__R>.Concat(_58_rs, _60_r);
      }
      Wrappers_Compile._IResult<Dafny.ISequence<__R>, __E> _rhs0 = Wrappers_Compile.Result<Dafny.ISequence<__R>, __E>.create_Success(_58_rs);
      res = _rhs0;
      return res;
      return res;
    }
    public static Dafny.ISequence<__A> Filter<__A>(Actions_Compile.DeterministicAction<__A, bool> action, Dafny.ISequence<__A> s)
    {
      Dafny.ISequence<__A> res = Dafny.Sequence<__A>.Empty;
      Dafny.ISequence<__A> _62_rs;
      _62_rs = Dafny.Sequence<__A>.FromElements();
      BigInteger _hi4 = new BigInteger((s).Count);
      for (BigInteger _63_i = BigInteger.Zero; _63_i < _hi4; _63_i++) {
        bool _64_r;
        bool _out5;
        _out5 = (action).Invoke((s).Select(_63_i));
        _64_r = _out5;
        if (_64_r) {
          _62_rs = Dafny.Sequence<__A>.Concat(_62_rs, Dafny.Sequence<__A>.FromElements((s).Select(_63_i)));
        }
      }
      res = _62_rs;
      return res;
      return res;
    }
    public static Wrappers_Compile._IResult<Dafny.ISequence<__A>, __E> FilterWithResult<__A, __E>(Actions_Compile.DeterministicActionWithResult<__A, bool, __E> action, Dafny.ISequence<__A> s)
    {
      Wrappers_Compile._IResult<Dafny.ISequence<__A>, __E> res = Wrappers_Compile.Result<Dafny.ISequence<__A>, __E>.Default(Dafny.Sequence<__A>.Empty);
      Dafny.ISequence<__A> _65_rs;
      _65_rs = Dafny.Sequence<__A>.FromElements();
      BigInteger _hi5 = new BigInteger((s).Count);
      for (BigInteger _66_i = BigInteger.Zero; _66_i < _hi5; _66_i++) {
        bool _67_r;
        Wrappers_Compile._IResult<bool, __E> _68_valueOrError0 = Wrappers_Compile.Result<bool, __E>.Default(false);
        Wrappers_Compile._IResult<bool, __E> _out6;
        _out6 = (action).Invoke((s).Select(_66_i));
        _68_valueOrError0 = _out6;
        if ((_68_valueOrError0).IsFailure()) {
          res = (_68_valueOrError0).PropagateFailure<Dafny.ISequence<__A>>();
          return res;
        }
        _67_r = (_68_valueOrError0).Extract();
        if (_67_r) {
          _65_rs = Dafny.Sequence<__A>.Concat(_65_rs, Dafny.Sequence<__A>.FromElements((s).Select(_66_i)));
        }
      }
      res = Wrappers_Compile.Result<Dafny.ISequence<__A>, __E>.create_Success(_65_rs);
      return res;
      return res;
    }
    public static Wrappers_Compile._IResult<__B, Dafny.ISequence<__E>> ReduceToSuccess<__A, __B, __E>(Actions_Compile.ActionWithResult<__A, __B, __E> action, Dafny.ISequence<__A> s)
    {
      Wrappers_Compile._IResult<__B, Dafny.ISequence<__E>> res = default(Wrappers_Compile._IResult<__B, Dafny.ISequence<__E>>);
      Dafny.ISequence<Wrappers_Compile._IResult<__B, __E>> _69_attemptedResults;
      _69_attemptedResults = Dafny.Sequence<Wrappers_Compile._IResult<__B, __E>>.FromElements();
      BigInteger _hi6 = new BigInteger((s).Count);
      for (BigInteger _70_i = BigInteger.Zero; _70_i < _hi6; _70_i++) {
        Wrappers_Compile._IResult<__B, __E> _71_attempt;
        Wrappers_Compile._IResult<__B, __E> _out7;
        _out7 = (action).Invoke((s).Select(_70_i));
        _71_attempt = _out7;
        _69_attemptedResults = Dafny.Sequence<Wrappers_Compile._IResult<__B, __E>>.Concat(_69_attemptedResults, Dafny.Sequence<Wrappers_Compile._IResult<__B, __E>>.FromElements(_71_attempt));
        if ((_71_attempt).is_Success) {
          Wrappers_Compile._IResult<__B, Dafny.ISequence<__E>> _rhs1 = Wrappers_Compile.Result<__B, Dafny.ISequence<__E>>.create_Success((_71_attempt).dtor_value);
          res = _rhs1;
          return res;
        }
      }
      res = Wrappers_Compile.Result<__B, Dafny.ISequence<__E>>.create_Failure(Seq_Compile.__default.Map<Wrappers_Compile._IResult<__B, __E>, __E>((Wrappers_Compile._IResult<__B, __E> _eta0) => Actions_Compile.__default.pluckErrors<__B, __E>(_eta0), _69_attemptedResults));
      return res;
    }
    public static __E pluckErrors<__B, __E>(Wrappers_Compile._IResult<__B, __E> r) {
      return (r).dtor_error;
    }
  }
} // end of namespace Actions_Compile
namespace BoundedInts_Compile {

  public partial class uint8 {
    public static System.Collections.Generic.IEnumerable<byte> IntegerRange(BigInteger lo, BigInteger hi) {
      for (var j = lo; j < hi; j++) { yield return (byte)j; }
    }
    private static readonly Dafny.TypeDescriptor<byte> _TYPE = new Dafny.TypeDescriptor<byte>(0);
    public static Dafny.TypeDescriptor<byte> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class uint16 {
    public static System.Collections.Generic.IEnumerable<ushort> IntegerRange(BigInteger lo, BigInteger hi) {
      for (var j = lo; j < hi; j++) { yield return (ushort)j; }
    }
    private static readonly Dafny.TypeDescriptor<ushort> _TYPE = new Dafny.TypeDescriptor<ushort>(0);
    public static Dafny.TypeDescriptor<ushort> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class uint32 {
    public static System.Collections.Generic.IEnumerable<uint> IntegerRange(BigInteger lo, BigInteger hi) {
      for (var j = lo; j < hi; j++) { yield return (uint)j; }
    }
    private static readonly Dafny.TypeDescriptor<uint> _TYPE = new Dafny.TypeDescriptor<uint>(0);
    public static Dafny.TypeDescriptor<uint> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class uint64 {
    public static System.Collections.Generic.IEnumerable<ulong> IntegerRange(BigInteger lo, BigInteger hi) {
      for (var j = lo; j < hi; j++) { yield return (ulong)j; }
    }
    private static readonly Dafny.TypeDescriptor<ulong> _TYPE = new Dafny.TypeDescriptor<ulong>(0);
    public static Dafny.TypeDescriptor<ulong> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class int8 {
    public static System.Collections.Generic.IEnumerable<sbyte> IntegerRange(BigInteger lo, BigInteger hi) {
      for (var j = lo; j < hi; j++) { yield return (sbyte)j; }
    }
    private static readonly Dafny.TypeDescriptor<sbyte> _TYPE = new Dafny.TypeDescriptor<sbyte>(0);
    public static Dafny.TypeDescriptor<sbyte> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class int16 {
    public static System.Collections.Generic.IEnumerable<short> IntegerRange(BigInteger lo, BigInteger hi) {
      for (var j = lo; j < hi; j++) { yield return (short)j; }
    }
    private static readonly Dafny.TypeDescriptor<short> _TYPE = new Dafny.TypeDescriptor<short>(0);
    public static Dafny.TypeDescriptor<short> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class int32 {
    public static System.Collections.Generic.IEnumerable<int> IntegerRange(BigInteger lo, BigInteger hi) {
      for (var j = lo; j < hi; j++) { yield return (int)j; }
    }
    private static readonly Dafny.TypeDescriptor<int> _TYPE = new Dafny.TypeDescriptor<int>(0);
    public static Dafny.TypeDescriptor<int> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class int64 {
    public static System.Collections.Generic.IEnumerable<long> IntegerRange(BigInteger lo, BigInteger hi) {
      for (var j = lo; j < hi; j++) { yield return (long)j; }
    }
    private static readonly Dafny.TypeDescriptor<long> _TYPE = new Dafny.TypeDescriptor<long>(0);
    public static Dafny.TypeDescriptor<long> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class nat8 {
    public static System.Collections.Generic.IEnumerable<byte> IntegerRange(BigInteger lo, BigInteger hi) {
      for (var j = lo; j < hi; j++) { yield return (byte)j; }
    }
    private static readonly Dafny.TypeDescriptor<byte> _TYPE = new Dafny.TypeDescriptor<byte>(0);
    public static Dafny.TypeDescriptor<byte> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class nat16 {
    public static System.Collections.Generic.IEnumerable<ushort> IntegerRange(BigInteger lo, BigInteger hi) {
      for (var j = lo; j < hi; j++) { yield return (ushort)j; }
    }
    private static readonly Dafny.TypeDescriptor<ushort> _TYPE = new Dafny.TypeDescriptor<ushort>(0);
    public static Dafny.TypeDescriptor<ushort> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class nat32 {
    public static System.Collections.Generic.IEnumerable<uint> IntegerRange(BigInteger lo, BigInteger hi) {
      for (var j = lo; j < hi; j++) { yield return (uint)j; }
    }
    private static readonly Dafny.TypeDescriptor<uint> _TYPE = new Dafny.TypeDescriptor<uint>(0);
    public static Dafny.TypeDescriptor<uint> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class nat64 {
    public static System.Collections.Generic.IEnumerable<ulong> IntegerRange(BigInteger lo, BigInteger hi) {
      for (var j = lo; j < hi; j++) { yield return (ulong)j; }
    }
    private static readonly Dafny.TypeDescriptor<ulong> _TYPE = new Dafny.TypeDescriptor<ulong>(0);
    public static Dafny.TypeDescriptor<ulong> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class opt__byte {
    public static System.Collections.Generic.IEnumerable<short> IntegerRange(BigInteger lo, BigInteger hi) {
      for (var j = lo; j < hi; j++) { yield return (short)j; }
    }
    private static readonly Dafny.TypeDescriptor<short> _TYPE = new Dafny.TypeDescriptor<short>(0);
    public static Dafny.TypeDescriptor<short> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class __default {
    public static BigInteger TWO__TO__THE__8 { get {
      return new BigInteger(256);
    } }
    public static BigInteger TWO__TO__THE__16 { get {
      return new BigInteger(65536);
    } }
    public static BigInteger TWO__TO__THE__32 { get {
      return new BigInteger(4294967296L);
    } }
    public static BigInteger TWO__TO__THE__64 { get {
      return BigInteger.Parse("18446744073709551616");
    } }
    public static byte UINT8__MAX { get {
      return (byte)(255);
    } }
    public static ushort UINT16__MAX { get {
      return (ushort)(65535);
    } }
    public static uint UINT32__MAX { get {
      return 4294967295U;
    } }
    public static ulong UINT64__MAX { get {
      return 18446744073709551615UL;
    } }
    public static sbyte INT8__MIN { get {
      return (sbyte)(-128);
    } }
    public static sbyte INT8__MAX { get {
      return (sbyte)(127);
    } }
    public static short INT16__MIN { get {
      return (short)(-32768);
    } }
    public static short INT16__MAX { get {
      return (short)(32767);
    } }
    public static int INT32__MIN { get {
      return -2147483648;
    } }
    public static int INT32__MAX { get {
      return 2147483647;
    } }
    public static long INT64__MIN { get {
      return -9223372036854775808L;
    } }
    public static long INT64__MAX { get {
      return 9223372036854775807L;
    } }
    public static byte NAT8__MAX { get {
      return (byte)(127);
    } }
    public static ushort NAT16__MAX { get {
      return (ushort)(32767);
    } }
    public static uint NAT32__MAX { get {
      return 2147483647U;
    } }
    public static ulong NAT64__MAX { get {
      return 9223372036854775807UL;
    } }
    public static BigInteger TWO__TO__THE__0 { get {
      return BigInteger.One;
    } }
    public static BigInteger TWO__TO__THE__1 { get {
      return new BigInteger(2);
    } }
    public static BigInteger TWO__TO__THE__2 { get {
      return new BigInteger(4);
    } }
    public static BigInteger TWO__TO__THE__4 { get {
      return new BigInteger(16);
    } }
    public static BigInteger TWO__TO__THE__5 { get {
      return new BigInteger(32);
    } }
    public static BigInteger TWO__TO__THE__24 { get {
      return new BigInteger(16777216);
    } }
    public static BigInteger TWO__TO__THE__40 { get {
      return new BigInteger(1099511627776L);
    } }
    public static BigInteger TWO__TO__THE__48 { get {
      return new BigInteger(281474976710656L);
    } }
    public static BigInteger TWO__TO__THE__56 { get {
      return new BigInteger(72057594037927936L);
    } }
    public static BigInteger TWO__TO__THE__128 { get {
      return BigInteger.Parse("340282366920938463463374607431768211456");
    } }
    public static BigInteger TWO__TO__THE__256 { get {
      return BigInteger.Parse("115792089237316195423570985008687907853269984665640564039457584007913129639936");
    } }
    public static BigInteger TWO__TO__THE__512 { get {
      return BigInteger.Parse("13407807929942597099574024998205846127479365820592393377723561443721764030073546976801874298166903427690031858186486050853753882811946569946433649006084096");
    } }
  }
} // end of namespace BoundedInts_Compile
namespace StandardLibrary_mUInt_Compile {

  public partial class seq16<T> {
    public static Dafny.TypeDescriptor<Dafny.ISequence<T>> _TypeDescriptor(Dafny.TypeDescriptor<T> _td_T) {
      return new Dafny.TypeDescriptor<Dafny.ISequence<T>>(Dafny.Sequence<T>.Empty);
    }
  }

  public partial class seq32<T> {
    public static Dafny.TypeDescriptor<Dafny.ISequence<T>> _TypeDescriptor(Dafny.TypeDescriptor<T> _td_T) {
      return new Dafny.TypeDescriptor<Dafny.ISequence<T>>(Dafny.Sequence<T>.Empty);
    }
  }

  public partial class seq64<T> {
    public static Dafny.TypeDescriptor<Dafny.ISequence<T>> _TypeDescriptor(Dafny.TypeDescriptor<T> _td_T) {
      return new Dafny.TypeDescriptor<Dafny.ISequence<T>>(Dafny.Sequence<T>.Empty);
    }
  }

  public partial class __default {
    public static bool UInt8Less(byte a, byte b)
    {
      return (a) < (b);
    }
    public static bool HasUint16Len<__T>(Dafny.ISequence<__T> s) {
      return (new BigInteger((s).Count)) < (StandardLibrary_mUInt_Compile.__default.UINT16__LIMIT);
    }
    public static bool HasUint32Len<__T>(Dafny.ISequence<__T> s) {
      return (new BigInteger((s).Count)) < (StandardLibrary_mUInt_Compile.__default.UINT32__LIMIT);
    }
    public static bool HasUint64Len<__T>(Dafny.ISequence<__T> s) {
      return (new BigInteger((s).Count)) < (StandardLibrary_mUInt_Compile.__default.UINT64__LIMIT);
    }
    public static Dafny.ISequence<byte> UInt16ToSeq(ushort x) {
      byte _72_b0 = (byte)((ushort)((x) / ((ushort)(256))));
      byte _73_b1 = (byte)((ushort)((x) % ((ushort)(256))));
      return Dafny.Sequence<byte>.FromElements(_72_b0, _73_b1);
    }
    public static ushort SeqToUInt16(Dafny.ISequence<byte> s) {
      ushort _74_x0 = (ushort)(((ushort)((s).Select(BigInteger.Zero))) * ((ushort)(256)));
      return (ushort)((_74_x0) + ((ushort)((s).Select(BigInteger.One))));
    }
    public static Dafny.ISequence<byte> UInt32ToSeq(uint x) {
      byte _75_b0 = (byte)((x) / (16777216U));
      uint _76_x0 = (x) - (((uint)(_75_b0)) * (16777216U));
      byte _77_b1 = (byte)((_76_x0) / (65536U));
      uint _78_x1 = (_76_x0) - (((uint)(_77_b1)) * (65536U));
      byte _79_b2 = (byte)((_78_x1) / (256U));
      byte _80_b3 = (byte)((_78_x1) % (256U));
      return Dafny.Sequence<byte>.FromElements(_75_b0, _77_b1, _79_b2, _80_b3);
    }
    public static uint SeqToUInt32(Dafny.ISequence<byte> s) {
      uint _81_x0 = ((uint)((s).Select(BigInteger.Zero))) * (16777216U);
      uint _82_x1 = (_81_x0) + (((uint)((s).Select(BigInteger.One))) * (65536U));
      uint _83_x2 = (_82_x1) + (((uint)((s).Select(new BigInteger(2)))) * (256U));
      return (_83_x2) + ((uint)((s).Select(new BigInteger(3))));
    }
    public static Dafny.ISequence<byte> UInt64ToSeq(ulong x) {
      byte _84_b0 = (byte)((x) / (72057594037927936UL));
      ulong _85_x0 = (x) - (((ulong)(_84_b0)) * (72057594037927936UL));
      byte _86_b1 = (byte)((_85_x0) / (281474976710656UL));
      ulong _87_x1 = (_85_x0) - (((ulong)(_86_b1)) * (281474976710656UL));
      byte _88_b2 = (byte)((_87_x1) / (1099511627776UL));
      ulong _89_x2 = (_87_x1) - (((ulong)(_88_b2)) * (1099511627776UL));
      byte _90_b3 = (byte)((_89_x2) / (4294967296UL));
      ulong _91_x3 = (_89_x2) - (((ulong)(_90_b3)) * (4294967296UL));
      byte _92_b4 = (byte)((_91_x3) / (16777216UL));
      ulong _93_x4 = (_91_x3) - (((ulong)(_92_b4)) * (16777216UL));
      byte _94_b5 = (byte)((_93_x4) / (65536UL));
      ulong _95_x5 = (_93_x4) - (((ulong)(_94_b5)) * (65536UL));
      byte _96_b6 = (byte)((_95_x5) / (256UL));
      byte _97_b7 = (byte)((_95_x5) % (256UL));
      return Dafny.Sequence<byte>.FromElements(_84_b0, _86_b1, _88_b2, _90_b3, _92_b4, _94_b5, _96_b6, _97_b7);
    }
    public static ulong SeqToUInt64(Dafny.ISequence<byte> s) {
      ulong _98_x0 = ((ulong)((s).Select(BigInteger.Zero))) * (72057594037927936UL);
      ulong _99_x1 = (_98_x0) + (((ulong)((s).Select(BigInteger.One))) * (281474976710656UL));
      ulong _100_x2 = (_99_x1) + (((ulong)((s).Select(new BigInteger(2)))) * (1099511627776UL));
      ulong _101_x3 = (_100_x2) + (((ulong)((s).Select(new BigInteger(3)))) * (4294967296UL));
      ulong _102_x4 = (_101_x3) + (((ulong)((s).Select(new BigInteger(4)))) * (16777216UL));
      ulong _103_x5 = (_102_x4) + (((ulong)((s).Select(new BigInteger(5)))) * (65536UL));
      ulong _104_x6 = (_103_x5) + (((ulong)((s).Select(new BigInteger(6)))) * (256UL));
      ulong _105_x = (_104_x6) + ((ulong)((s).Select(new BigInteger(7))));
      return _105_x;
    }
    public static BigInteger UINT16__LIMIT { get {
      return (new BigInteger(BoundedInts_Compile.__default.UINT16__MAX)) + (BigInteger.One);
    } }
    public static BigInteger UINT32__LIMIT { get {
      return (new BigInteger(BoundedInts_Compile.__default.UINT32__MAX)) + (BigInteger.One);
    } }
    public static BigInteger UINT64__LIMIT { get {
      return (new BigInteger(BoundedInts_Compile.__default.UINT64__MAX)) + (BigInteger.One);
    } }
    public static BigInteger INT32__MAX__LIMIT { get {
      return new BigInteger(BoundedInts_Compile.__default.INT32__MAX);
    } }
    public static BigInteger INT64__MAX__LIMIT { get {
      return new BigInteger(BoundedInts_Compile.__default.INT64__MAX);
    } }
  }
} // end of namespace StandardLibrary_mUInt_Compile
namespace String_Compile {

  public partial class __default {
    public static Dafny.ISequence<BigInteger> Int2Digits(BigInteger n, BigInteger @base)
    {
      Dafny.ISequence<BigInteger> _106___accumulator = Dafny.Sequence<BigInteger>.FromElements();
    TAIL_CALL_START: ;
      if ((n).Sign == 0) {
        return Dafny.Sequence<BigInteger>.Concat(Dafny.Sequence<BigInteger>.FromElements(), _106___accumulator);
      } else {
        _106___accumulator = Dafny.Sequence<BigInteger>.Concat(Dafny.Sequence<BigInteger>.FromElements(Dafny.Helpers.EuclideanModulus(n, @base)), _106___accumulator);
        BigInteger _in24 = Dafny.Helpers.EuclideanDivision(n, @base);
        BigInteger _in25 = @base;
        n = _in24;
        @base = _in25;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<char> Digits2String(Dafny.ISequence<BigInteger> digits, Dafny.ISequence<char> chars)
    {
      Dafny.ISequence<char> _107___accumulator = Dafny.Sequence<char>.FromElements();
    TAIL_CALL_START: ;
      if ((digits).Equals(Dafny.Sequence<BigInteger>.FromElements())) {
        return Dafny.Sequence<char>.Concat(_107___accumulator, Dafny.Sequence<char>.FromString(""));
      } else {
        _107___accumulator = Dafny.Sequence<char>.Concat(_107___accumulator, Dafny.Sequence<char>.FromElements((chars).Select((digits).Select(BigInteger.Zero))));
        Dafny.ISequence<BigInteger> _in26 = (digits).Drop(BigInteger.One);
        Dafny.ISequence<char> _in27 = chars;
        digits = _in26;
        chars = _in27;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<char> Int2String(BigInteger n, Dafny.ISequence<char> chars)
    {
      BigInteger _108_base = new BigInteger((chars).Count);
      if ((n).Sign == 0) {
        return Dafny.Sequence<char>.FromString("0");
      } else if ((n).Sign == 1) {
        return String_Compile.__default.Digits2String(String_Compile.__default.Int2Digits(n, _108_base), chars);
      } else {
        return Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.FromString("-"), String_Compile.__default.Digits2String(String_Compile.__default.Int2Digits((BigInteger.Zero) - (n), _108_base), chars));
      }
    }
    public static Dafny.ISequence<char> Base10Int2String(BigInteger n) {
      return String_Compile.__default.Int2String(n, String_Compile.__default.Base10);
    }
    public static Dafny.ISequence<char> Base10 { get {
      return Dafny.Sequence<char>.FromElements('0', '1', '2', '3', '4', '5', '6', '7', '8', '9');
    } }
  }
} // end of namespace String_Compile
namespace StandardLibrary_Compile {

  public partial class __default {
    public static Dafny.ISequence<__T> Join<__T>(Dafny.ISequence<Dafny.ISequence<__T>> ss, Dafny.ISequence<__T> joiner)
    {
      Dafny.ISequence<__T> _109___accumulator = Dafny.Sequence<__T>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((ss).Count)) == (BigInteger.One)) {
        return Dafny.Sequence<__T>.Concat(_109___accumulator, (ss).Select(BigInteger.Zero));
      } else {
        _109___accumulator = Dafny.Sequence<__T>.Concat(_109___accumulator, Dafny.Sequence<__T>.Concat((ss).Select(BigInteger.Zero), joiner));
        Dafny.ISequence<Dafny.ISequence<__T>> _in28 = (ss).Drop(BigInteger.One);
        Dafny.ISequence<__T> _in29 = joiner;
        ss = _in28;
        joiner = _in29;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<Dafny.ISequence<__T>> Split<__T>(Dafny.ISequence<__T> s, __T delim)
    {
      Dafny.ISequence<Dafny.ISequence<__T>> _110___accumulator = Dafny.Sequence<Dafny.ISequence<__T>>.FromElements();
    TAIL_CALL_START: ;
      Wrappers_Compile._IOption<BigInteger> _111_i = StandardLibrary_Compile.__default.FindIndexMatching<__T>(s, delim, BigInteger.Zero);
      if ((_111_i).is_Some) {
        _110___accumulator = Dafny.Sequence<Dafny.ISequence<__T>>.Concat(_110___accumulator, Dafny.Sequence<Dafny.ISequence<__T>>.FromElements((s).Take((_111_i).dtor_value)));
        Dafny.ISequence<__T> _in30 = (s).Drop(((_111_i).dtor_value) + (BigInteger.One));
        __T _in31 = delim;
        s = _in30;
        delim = _in31;
        goto TAIL_CALL_START;
      } else {
        return Dafny.Sequence<Dafny.ISequence<__T>>.Concat(_110___accumulator, Dafny.Sequence<Dafny.ISequence<__T>>.FromElements(s));
      }
    }
    public static _System._ITuple2<Dafny.ISequence<__T>, Dafny.ISequence<__T>> SplitOnce<__T>(Dafny.ISequence<__T> s, __T delim)
    {
      Wrappers_Compile._IOption<BigInteger> _112_i = StandardLibrary_Compile.__default.FindIndexMatching<__T>(s, delim, BigInteger.Zero);
      return _System.Tuple2<Dafny.ISequence<__T>, Dafny.ISequence<__T>>.create((s).Take((_112_i).dtor_value), (s).Drop(((_112_i).dtor_value) + (BigInteger.One)));
    }
    public static Wrappers_Compile._IOption<_System._ITuple2<Dafny.ISequence<__T>, Dafny.ISequence<__T>>> SplitOnce_q<__T>(Dafny.ISequence<__T> s, __T delim)
    {
      Wrappers_Compile._IOption<BigInteger> _113_valueOrError0 = StandardLibrary_Compile.__default.FindIndexMatching<__T>(s, delim, BigInteger.Zero);
      if ((_113_valueOrError0).IsFailure()) {
        return (_113_valueOrError0).PropagateFailure<_System._ITuple2<Dafny.ISequence<__T>, Dafny.ISequence<__T>>>();
      } else {
        BigInteger _114_i = (_113_valueOrError0).Extract();
        return Wrappers_Compile.Option<_System._ITuple2<Dafny.ISequence<__T>, Dafny.ISequence<__T>>>.create_Some(_System.Tuple2<Dafny.ISequence<__T>, Dafny.ISequence<__T>>.create((s).Take(_114_i), (s).Drop((_114_i) + (BigInteger.One))));
      }
    }
    public static Wrappers_Compile._IOption<BigInteger> FindIndexMatching<__T>(Dafny.ISequence<__T> s, __T c, BigInteger i)
    {
      return StandardLibrary_Compile.__default.FindIndex<__T>(s, Dafny.Helpers.Id<Func<__T, Func<__T, bool>>>((_115_c) => ((System.Func<__T, bool>)((_116_x) => {
        return object.Equals(_116_x, _115_c);
      })))(c), i);
    }
    public static Wrappers_Compile._IOption<BigInteger> FindIndex<__T>(Dafny.ISequence<__T> s, Func<__T, bool> f, BigInteger i)
    {
    TAIL_CALL_START: ;
      if ((i) == (new BigInteger((s).Count))) {
        return Wrappers_Compile.Option<BigInteger>.create_None();
      } else if (Dafny.Helpers.Id<Func<__T, bool>>(f)((s).Select(i))) {
        return Wrappers_Compile.Option<BigInteger>.create_Some(i);
      } else {
        Dafny.ISequence<__T> _in32 = s;
        Func<__T, bool> _in33 = f;
        BigInteger _in34 = (i) + (BigInteger.One);
        s = _in32;
        f = _in33;
        i = _in34;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<__T> Filter<__T>(Dafny.ISequence<__T> s, Func<__T, bool> f)
    {
      Dafny.ISequence<__T> _117___accumulator = Dafny.Sequence<__T>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((s).Count)).Sign == 0) {
        return Dafny.Sequence<__T>.Concat(_117___accumulator, Dafny.Sequence<__T>.FromElements());
      } else if (Dafny.Helpers.Id<Func<__T, bool>>(f)((s).Select(BigInteger.Zero))) {
        _117___accumulator = Dafny.Sequence<__T>.Concat(_117___accumulator, Dafny.Sequence<__T>.FromElements((s).Select(BigInteger.Zero)));
        Dafny.ISequence<__T> _in35 = (s).Drop(BigInteger.One);
        Func<__T, bool> _in36 = f;
        s = _in35;
        f = _in36;
        goto TAIL_CALL_START;
      } else {
        Dafny.ISequence<__T> _in37 = (s).Drop(BigInteger.One);
        Func<__T, bool> _in38 = f;
        s = _in37;
        f = _in38;
        goto TAIL_CALL_START;
      }
    }
    public static BigInteger Min(BigInteger a, BigInteger b)
    {
      if ((a) < (b)) {
        return a;
      } else {
        return b;
      }
    }
    public static Dafny.ISequence<__T> Fill<__T>(__T @value, BigInteger n)
    {
      return ((System.Func<Dafny.ISequence<__T>>) (() => {
        BigInteger dim1 = n;
        var arr1 = new __T[Dafny.Helpers.ToIntChecked(dim1, "array size exceeds memory limit")];
        for (int i1 = 0; i1 < dim1; i1++) {
          var _118___v0 = (BigInteger) i1;
          arr1[(int)(_118___v0)] = @value;
        }
        return Dafny.Sequence<__T>.FromArray(arr1);
      }))();
    }
    public static __T[] SeqToArray<__T>(Dafny.ISequence<__T> s)
    {
      __T[] a = new __T[0];
      Func<BigInteger, __T> _init1 = Dafny.Helpers.Id<Func<Dafny.ISequence<__T>, Func<BigInteger, __T>>>((_119_s) => ((System.Func<BigInteger, __T>)((_120_i) => {
        return (_119_s).Select(_120_i);
      })))(s);
      __T[] _nw1 = new __T[Dafny.Helpers.ToIntChecked(new BigInteger((s).Count), "array size exceeds memory limit")];
      for (var _i0_1 = 0; _i0_1 < new BigInteger(_nw1.Length); _i0_1++) {
        _nw1[(int)(_i0_1)] = _init1(_i0_1);
      }
      a = _nw1;
      return a;
    }
    public static bool LexicographicLessOrEqual<__T>(Dafny.ISequence<__T> a, Dafny.ISequence<__T> b, Func<__T, __T, bool> less)
    {
      return Dafny.Helpers.Id<Func<Dafny.ISequence<__T>, Dafny.ISequence<__T>, Func<__T, __T, bool>, bool>>((_121_a, _122_b, _123_less) => Dafny.Helpers.Quantifier<BigInteger>(Dafny.Helpers.IntegerRange(BigInteger.Zero, (new BigInteger((_121_a).Count)) + (BigInteger.One)), false, (((_exists_var_0) => {
        BigInteger _124_k = (BigInteger)_exists_var_0;
        return (((_124_k).Sign != -1) && ((_124_k) <= (new BigInteger((_121_a).Count)))) && (StandardLibrary_Compile.__default.LexicographicLessOrEqualAux<__T>(_121_a, _122_b, _123_less, _124_k));
      }))))(a, b, less);
    }
    public static bool LexicographicLessOrEqualAux<__T>(Dafny.ISequence<__T> a, Dafny.ISequence<__T> b, Func<__T, __T, bool> less, BigInteger lengthOfCommonPrefix)
    {
      return (((lengthOfCommonPrefix) <= (new BigInteger((b).Count))) && (Dafny.Helpers.Id<Func<BigInteger, Dafny.ISequence<__T>, Dafny.ISequence<__T>, bool>>((_125_lengthOfCommonPrefix, _126_a, _127_b) => Dafny.Helpers.Quantifier<BigInteger>(Dafny.Helpers.IntegerRange(BigInteger.Zero, _125_lengthOfCommonPrefix), true, (((_forall_var_0) => {
        BigInteger _128_i = (BigInteger)_forall_var_0;
        return !(((_128_i).Sign != -1) && ((_128_i) < (_125_lengthOfCommonPrefix))) || (object.Equals((_126_a).Select(_128_i), (_127_b).Select(_128_i)));
      }))))(lengthOfCommonPrefix, a, b))) && (((lengthOfCommonPrefix) == (new BigInteger((a).Count))) || (((lengthOfCommonPrefix) < (new BigInteger((b).Count))) && (Dafny.Helpers.Id<Func<__T, __T, bool>>(less)((a).Select(lengthOfCommonPrefix), (b).Select(lengthOfCommonPrefix)))));
    }
    public static Dafny.ISequence<Dafny.ISequence<__T>> SetToOrderedSequence<__T>(Dafny.ISet<Dafny.ISequence<__T>> s, Func<__T, __T, bool> less)
    {
      Dafny.ISequence<Dafny.ISequence<__T>> _129___accumulator = Dafny.Sequence<Dafny.ISequence<__T>>.FromElements();
    TAIL_CALL_START: ;
      var _pat_let_tv0 = s;
      var _pat_let_tv1 = less;
      if ((s).Equals(Dafny.Set<Dafny.ISequence<__T>>.FromElements())) {
        return Dafny.Sequence<Dafny.ISequence<__T>>.Concat(_129___accumulator, Dafny.Sequence<Dafny.ISequence<__T>>.FromElements());
      } else {
        return Dafny.Helpers.Let<int, Dafny.ISequence<Dafny.ISequence<__T>>>(0, _let_dummy_0 =>  {
          Dafny.ISequence<__T> _130_a = default(Dafny.ISequence<__T>);
          foreach (Dafny.ISequence<__T> _assign_such_that_1 in (s).Elements) {
            _130_a = (Dafny.ISequence<__T>)_assign_such_that_1;
            if (((s).Contains(_130_a)) && (StandardLibrary_Compile.__default.IsMinimum<__T>(_130_a, s, less))) {
              goto after__ASSIGN_SUCH_THAT_1;
            }
          }
          throw new System.Exception("assign-such-that search produced no value (line 369)");
        after__ASSIGN_SUCH_THAT_1: ;
          return Dafny.Sequence<Dafny.ISequence<__T>>.Concat(Dafny.Sequence<Dafny.ISequence<__T>>.FromElements(_130_a), StandardLibrary_Compile.__default.SetToOrderedSequence<__T>(Dafny.Set<Dafny.ISequence<__T>>.Difference(_pat_let_tv0, Dafny.Set<Dafny.ISequence<__T>>.FromElements(_130_a)), _pat_let_tv1));
        }
        );
      }
    }
    public static bool IsMinimum<__T>(Dafny.ISequence<__T> a, Dafny.ISet<Dafny.ISequence<__T>> s, Func<__T, __T, bool> less)
    {
      return ((s).Contains(a)) && (Dafny.Helpers.Id<Func<Dafny.ISet<Dafny.ISequence<__T>>, Dafny.ISequence<__T>, Func<__T, __T, bool>, bool>>((_131_s, _132_a, _133_less) => Dafny.Helpers.Quantifier<Dafny.ISequence<__T>>((_131_s).Elements, true, (((_forall_var_1) => {
        Dafny.ISequence<__T> _134_z = (Dafny.ISequence<__T>)_forall_var_1;
        return !((_131_s).Contains(_134_z)) || (StandardLibrary_Compile.__default.LexicographicLessOrEqual<__T>(_132_a, _134_z, _133_less));
      }))))(s, a, less));
    }
  }
} // end of namespace StandardLibrary_Compile
namespace Base64_Compile {

  public partial class index {
    public static System.Collections.Generic.IEnumerable<byte> IntegerRange(BigInteger lo, BigInteger hi) {
      for (var j = lo; j < hi; j++) { yield return (byte)j; }
    }
    private static readonly Dafny.TypeDescriptor<byte> _TYPE = new Dafny.TypeDescriptor<byte>(0);
    public static Dafny.TypeDescriptor<byte> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class uint24 {
    public static System.Collections.Generic.IEnumerable<uint> IntegerRange(BigInteger lo, BigInteger hi) {
      for (var j = lo; j < hi; j++) { yield return (uint)j; }
    }
    private static readonly Dafny.TypeDescriptor<uint> _TYPE = new Dafny.TypeDescriptor<uint>(0);
    public static Dafny.TypeDescriptor<uint> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class __default {
    public static bool IsBase64Char(char c) {
      return (((((c) == ('+')) || ((c) == ('/'))) || ((('0') <= (c)) && ((c) <= ('9')))) || ((('A') <= (c)) && ((c) <= ('Z')))) || ((('a') <= (c)) && ((c) <= ('z')));
    }
    public static bool IsUnpaddedBase64String(Dafny.ISequence<char> s) {
      return ((Dafny.Helpers.EuclideanModulus(new BigInteger((s).Count), new BigInteger(4))).Sign == 0) && (Dafny.Helpers.Id<Func<Dafny.ISequence<char>, bool>>((_135_s) => Dafny.Helpers.Quantifier<char>((_135_s).UniqueElements, true, (((_forall_var_2) => {
        char _136_k = (char)_forall_var_2;
        return !((_135_s).Contains(_136_k)) || (Base64_Compile.__default.IsBase64Char(_136_k));
      }))))(s));
    }
    public static char IndexToChar(byte i) {
      if ((i) == ((byte)(63))) {
        return '/';
      } else if ((i) == ((byte)(62))) {
        return '+';
      } else if ((((byte)(52)) <= (i)) && ((i) <= ((byte)(61)))) {
        return (char)((byte)((i) - ((byte)(4))));
      } else if ((((byte)(26)) <= (i)) && ((i) <= ((byte)(51)))) {
        return (char)(((char)(i)) + ((char)(new BigInteger(71))));
      } else {
        return (char)(((char)(i)) + ((char)(new BigInteger(65))));
      }
    }
    public static byte CharToIndex(char c) {
      if ((c) == ('/')) {
        return (byte)(63);
      } else if ((c) == ('+')) {
        return (byte)(62);
      } else if ((('0') <= (c)) && ((c) <= ('9'))) {
        return (byte)((char)((c) + ((char)(new BigInteger(4)))));
      } else if ((('a') <= (c)) && ((c) <= ('z'))) {
        return (byte)((char)((c) - ((char)(new BigInteger(71)))));
      } else {
        return (byte)((char)((c) - ((char)(new BigInteger(65)))));
      }
    }
    public static Dafny.ISequence<byte> UInt24ToSeq(uint x) {
      byte _137_b0 = (byte)((x) / (65536U));
      uint _138_x0 = (x) - (((uint)(_137_b0)) * (65536U));
      byte _139_b1 = (byte)((_138_x0) / (256U));
      byte _140_b2 = (byte)((_138_x0) % (256U));
      return Dafny.Sequence<byte>.FromElements(_137_b0, _139_b1, _140_b2);
    }
    public static uint SeqToUInt24(Dafny.ISequence<byte> s) {
      return ((((uint)((s).Select(BigInteger.Zero))) * (65536U)) + (((uint)((s).Select(BigInteger.One))) * (256U))) + ((uint)((s).Select(new BigInteger(2))));
    }
    public static Dafny.ISequence<byte> UInt24ToIndexSeq(uint x) {
      byte _141_b0 = (byte)((x) / (262144U));
      uint _142_x0 = (x) - (((uint)(_141_b0)) * (262144U));
      byte _143_b1 = (byte)((_142_x0) / (4096U));
      uint _144_x1 = (_142_x0) - (((uint)(_143_b1)) * (4096U));
      byte _145_b2 = (byte)((_144_x1) / (64U));
      byte _146_b3 = (byte)((_144_x1) % (64U));
      return Dafny.Sequence<byte>.FromElements(_141_b0, _143_b1, _145_b2, _146_b3);
    }
    public static uint IndexSeqToUInt24(Dafny.ISequence<byte> s) {
      return (((((uint)((s).Select(BigInteger.Zero))) * (262144U)) + (((uint)((s).Select(BigInteger.One))) * (4096U))) + (((uint)((s).Select(new BigInteger(2)))) * (64U))) + ((uint)((s).Select(new BigInteger(3))));
    }
    public static Dafny.ISequence<byte> DecodeBlock(Dafny.ISequence<byte> s) {
      return Base64_Compile.__default.UInt24ToSeq(Base64_Compile.__default.IndexSeqToUInt24(s));
    }
    public static Dafny.ISequence<byte> EncodeBlock(Dafny.ISequence<byte> s) {
      return Base64_Compile.__default.UInt24ToIndexSeq(Base64_Compile.__default.SeqToUInt24(s));
    }
    public static Dafny.ISequence<byte> DecodeRecursively(Dafny.ISequence<byte> s) {
      Dafny.ISequence<byte> _147___accumulator = Dafny.Sequence<byte>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((s).Count)).Sign == 0) {
        return Dafny.Sequence<byte>.Concat(_147___accumulator, Dafny.Sequence<byte>.FromElements());
      } else {
        _147___accumulator = Dafny.Sequence<byte>.Concat(_147___accumulator, Base64_Compile.__default.DecodeBlock((s).Take(new BigInteger(4))));
        Dafny.ISequence<byte> _in39 = (s).Drop(new BigInteger(4));
        s = _in39;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<byte> EncodeRecursively(Dafny.ISequence<byte> b) {
      Dafny.ISequence<byte> _148___accumulator = Dafny.Sequence<byte>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((b).Count)).Sign == 0) {
        return Dafny.Sequence<byte>.Concat(_148___accumulator, Dafny.Sequence<byte>.FromElements());
      } else {
        _148___accumulator = Dafny.Sequence<byte>.Concat(_148___accumulator, Base64_Compile.__default.EncodeBlock((b).Take(new BigInteger(3))));
        Dafny.ISequence<byte> _in40 = (b).Drop(new BigInteger(3));
        b = _in40;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<byte> FromCharsToIndices(Dafny.ISequence<char> s) {
      return ((System.Func<Dafny.ISequence<byte>>) (() => {
        BigInteger dim2 = new BigInteger((s).Count);
        var arr2 = new byte[Dafny.Helpers.ToIntChecked(dim2, "array size exceeds memory limit")];
        for (int i2 = 0; i2 < dim2; i2++) {
          var _149_i = (BigInteger) i2;
          arr2[(int)(_149_i)] = Base64_Compile.__default.CharToIndex((s).Select(_149_i));
        }
        return Dafny.Sequence<byte>.FromArray(arr2);
      }))();
    }
    public static Dafny.ISequence<char> FromIndicesToChars(Dafny.ISequence<byte> b) {
      return ((System.Func<Dafny.ISequence<char>>) (() => {
        BigInteger dim3 = new BigInteger((b).Count);
        var arr3 = new char[Dafny.Helpers.ToIntChecked(dim3, "array size exceeds memory limit")];
        for (int i3 = 0; i3 < dim3; i3++) {
          var _150_i = (BigInteger) i3;
          arr3[(int)(_150_i)] = Base64_Compile.__default.IndexToChar((b).Select(_150_i));
        }
        return Dafny.Sequence<char>.FromArray(arr3);
      }))();
    }
    public static Dafny.ISequence<byte> DecodeUnpadded(Dafny.ISequence<char> s) {
      return Base64_Compile.__default.DecodeRecursively(Base64_Compile.__default.FromCharsToIndices(s));
    }
    public static Dafny.ISequence<char> EncodeUnpadded(Dafny.ISequence<byte> b) {
      return Base64_Compile.__default.FromIndicesToChars(Base64_Compile.__default.EncodeRecursively(b));
    }
    public static bool Is1Padding(Dafny.ISequence<char> s) {
      return ((((((new BigInteger((s).Count)) == (new BigInteger(4))) && (Base64_Compile.__default.IsBase64Char((s).Select(BigInteger.Zero)))) && (Base64_Compile.__default.IsBase64Char((s).Select(BigInteger.One)))) && (Base64_Compile.__default.IsBase64Char((s).Select(new BigInteger(2))))) && (((byte)((Base64_Compile.__default.CharToIndex((s).Select(new BigInteger(2)))) % ((byte)(4)))) == ((byte)(0)))) && (((s).Select(new BigInteger(3))) == ('='));
    }
    public static Dafny.ISequence<byte> Decode1Padding(Dafny.ISequence<char> s) {
      Dafny.ISequence<byte> _151_d = Base64_Compile.__default.DecodeBlock(Dafny.Sequence<byte>.FromElements(Base64_Compile.__default.CharToIndex((s).Select(BigInteger.Zero)), Base64_Compile.__default.CharToIndex((s).Select(BigInteger.One)), Base64_Compile.__default.CharToIndex((s).Select(new BigInteger(2))), (byte)(0)));
      return Dafny.Sequence<byte>.FromElements((_151_d).Select(BigInteger.Zero), (_151_d).Select(BigInteger.One));
    }
    public static Dafny.ISequence<char> Encode1Padding(Dafny.ISequence<byte> b) {
      Dafny.ISequence<byte> _152_e = Base64_Compile.__default.EncodeBlock(Dafny.Sequence<byte>.FromElements((b).Select(BigInteger.Zero), (b).Select(BigInteger.One), (byte)(0)));
      return Dafny.Sequence<char>.FromElements(Base64_Compile.__default.IndexToChar((_152_e).Select(BigInteger.Zero)), Base64_Compile.__default.IndexToChar((_152_e).Select(BigInteger.One)), Base64_Compile.__default.IndexToChar((_152_e).Select(new BigInteger(2))), '=');
    }
    public static bool Is2Padding(Dafny.ISequence<char> s) {
      return ((((((new BigInteger((s).Count)) == (new BigInteger(4))) && (Base64_Compile.__default.IsBase64Char((s).Select(BigInteger.Zero)))) && (Base64_Compile.__default.IsBase64Char((s).Select(BigInteger.One)))) && (((byte)((Base64_Compile.__default.CharToIndex((s).Select(BigInteger.One))) % ((byte)(16)))) == ((byte)(0)))) && (((s).Select(new BigInteger(2))) == ('='))) && (((s).Select(new BigInteger(3))) == ('='));
    }
    public static Dafny.ISequence<byte> Decode2Padding(Dafny.ISequence<char> s) {
      Dafny.ISequence<byte> _153_d = Base64_Compile.__default.DecodeBlock(Dafny.Sequence<byte>.FromElements(Base64_Compile.__default.CharToIndex((s).Select(BigInteger.Zero)), Base64_Compile.__default.CharToIndex((s).Select(BigInteger.One)), (byte)(0), (byte)(0)));
      return Dafny.Sequence<byte>.FromElements((_153_d).Select(BigInteger.Zero));
    }
    public static Dafny.ISequence<char> Encode2Padding(Dafny.ISequence<byte> b) {
      Dafny.ISequence<byte> _154_e = Base64_Compile.__default.EncodeBlock(Dafny.Sequence<byte>.FromElements((b).Select(BigInteger.Zero), (byte)(0), (byte)(0)));
      return Dafny.Sequence<char>.FromElements(Base64_Compile.__default.IndexToChar((_154_e).Select(BigInteger.Zero)), Base64_Compile.__default.IndexToChar((_154_e).Select(BigInteger.One)), '=', '=');
    }
    public static bool IsBase64String(Dafny.ISequence<char> s) {
      BigInteger _155_finalBlockStart = (new BigInteger((s).Count)) - (new BigInteger(4));
      return ((Dafny.Helpers.EuclideanModulus(new BigInteger((s).Count), new BigInteger(4))).Sign == 0) && ((Base64_Compile.__default.IsUnpaddedBase64String(s)) || ((Base64_Compile.__default.IsUnpaddedBase64String((s).Take(_155_finalBlockStart))) && ((Base64_Compile.__default.Is1Padding((s).Drop(_155_finalBlockStart))) || (Base64_Compile.__default.Is2Padding((s).Drop(_155_finalBlockStart))))));
    }
    public static Dafny.ISequence<byte> DecodeValid(Dafny.ISequence<char> s) {
      if ((s).Equals(Dafny.Sequence<char>.FromElements())) {
        return Dafny.Sequence<byte>.FromElements();
      } else {
        BigInteger _156_finalBlockStart = (new BigInteger((s).Count)) - (new BigInteger(4));
        Dafny.ISequence<char> _157_prefix = (s).Take(_156_finalBlockStart);
        Dafny.ISequence<char> _158_suffix = (s).Drop(_156_finalBlockStart);
        if (Base64_Compile.__default.Is1Padding(_158_suffix)) {
          return Dafny.Sequence<byte>.Concat(Base64_Compile.__default.DecodeUnpadded(_157_prefix), Base64_Compile.__default.Decode1Padding(_158_suffix));
        } else if (Base64_Compile.__default.Is2Padding(_158_suffix)) {
          return Dafny.Sequence<byte>.Concat(Base64_Compile.__default.DecodeUnpadded(_157_prefix), Base64_Compile.__default.Decode2Padding(_158_suffix));
        } else {
          return Base64_Compile.__default.DecodeUnpadded(s);
        }
      }
    }
    public static Wrappers_Compile._IResult<Dafny.ISequence<byte>, Dafny.ISequence<char>> Decode(Dafny.ISequence<char> s) {
      if (Base64_Compile.__default.IsBase64String(s)) {
        return Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>>.create_Success(Base64_Compile.__default.DecodeValid(s));
      } else {
        return Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>>.create_Failure(Dafny.Sequence<char>.FromString("The encoding is malformed"));
      }
    }
    public static Dafny.ISequence<char> Encode(Dafny.ISequence<byte> b) {
      if ((Dafny.Helpers.EuclideanModulus(new BigInteger((b).Count), new BigInteger(3))).Sign == 0) {
        Dafny.ISequence<char> _159_s = Base64_Compile.__default.EncodeUnpadded(b);
        return _159_s;
      } else if ((Dafny.Helpers.EuclideanModulus(new BigInteger((b).Count), new BigInteger(3))) == (BigInteger.One)) {
        Dafny.ISequence<char> _160_s1 = Base64_Compile.__default.EncodeUnpadded((b).Take((new BigInteger((b).Count)) - (BigInteger.One)));
        Dafny.ISequence<char> _161_s2 = Base64_Compile.__default.Encode2Padding((b).Drop((new BigInteger((b).Count)) - (BigInteger.One)));
        Dafny.ISequence<char> _162_s = Dafny.Sequence<char>.Concat(_160_s1, _161_s2);
        return _162_s;
      } else {
        Dafny.ISequence<char> _163_s1 = Base64_Compile.__default.EncodeUnpadded((b).Take((new BigInteger((b).Count)) - (new BigInteger(2))));
        Dafny.ISequence<char> _164_s2 = Base64_Compile.__default.Encode1Padding((b).Drop((new BigInteger((b).Count)) - (new BigInteger(2))));
        Dafny.ISequence<char> _165_s = Dafny.Sequence<char>.Concat(_163_s1, _164_s2);
        return _165_s;
      }
    }
  }
} // end of namespace Base64_Compile
namespace Base64Lemmas_Compile {

} // end of namespace Base64Lemmas_Compile
namespace ConcurrentCall {

  public interface Callee {
    void call(uint serialPos, uint concurrentPos);
  }
  public class _Companion_Callee {
  }

} // end of namespace ConcurrentCall
namespace FloatCompare_Compile {

  public partial class CompareType {
    public static System.Collections.Generic.IEnumerable<sbyte> IntegerRange(BigInteger lo, BigInteger hi) {
      for (var j = lo; j < hi; j++) { yield return (sbyte)j; }
    }
    private static readonly Dafny.TypeDescriptor<sbyte> _TYPE = new Dafny.TypeDescriptor<sbyte>(0);
    public static Dafny.TypeDescriptor<sbyte> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class __default {
    public static BigInteger StrToIntInner(Dafny.ISequence<char> s, BigInteger acc)
    {
    TAIL_CALL_START: ;
      if ((new BigInteger((s).Count)).Sign == 0) {
        return acc;
      } else if ((('0') <= ((s).Select(BigInteger.Zero))) && (((s).Select(BigInteger.Zero)) <= ('9'))) {
        Dafny.ISequence<char> _in41 = (s).Drop(BigInteger.One);
        BigInteger _in42 = (((acc) * (new BigInteger(10))) + (new BigInteger((s).Select(BigInteger.Zero)))) - (new BigInteger('0'));
        s = _in41;
        acc = _in42;
        goto TAIL_CALL_START;
      } else {
        Dafny.ISequence<char> _in43 = (s).Drop(BigInteger.One);
        BigInteger _in44 = acc;
        s = _in43;
        acc = _in44;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<char> SkipLeadingSpace(Dafny.ISequence<char> val) {
    TAIL_CALL_START: ;
      if (((new BigInteger((val).Count)).Sign == 1) && (((val).Select(BigInteger.Zero)) <= (' '))) {
        Dafny.ISequence<char> _in45 = (val).Drop(BigInteger.One);
        val = _in45;
        goto TAIL_CALL_START;
      } else {
        return val;
      }
    }
    public static BigInteger StrToInt(Dafny.ISequence<char> s, BigInteger acc)
    {
      Dafny.ISequence<char> _166_tmp = FloatCompare_Compile.__default.SkipLeadingSpace(s);
      if ((new BigInteger((_166_tmp).Count)).Sign == 0) {
        return BigInteger.Zero;
      } else if (((_166_tmp).Select(BigInteger.Zero)) == ('-')) {
        return (BigInteger.Zero) - (FloatCompare_Compile.__default.StrToIntInner(s, BigInteger.Zero));
      } else {
        return FloatCompare_Compile.__default.StrToIntInner(s, BigInteger.Zero);
      }
    }
    public static Wrappers_Compile._IOption<_System._ITuple2<Dafny.ISequence<char>, Dafny.ISequence<char>>> SplitE(Dafny.ISequence<char> x) {
      Wrappers_Compile._IOption<_System._ITuple2<Dafny.ISequence<char>, Dafny.ISequence<char>>> _167_parts = StandardLibrary_Compile.__default.SplitOnce_q<char>(x, 'e');
      if ((_167_parts).is_Some) {
        return _167_parts;
      } else {
        return StandardLibrary_Compile.__default.SplitOnce_q<char>(x, 'E');
      }
    }
    public static _System._ITuple2<Dafny.ISequence<char>, BigInteger> SplitExp(Dafny.ISequence<char> x) {
      Wrappers_Compile._IOption<_System._ITuple2<Dafny.ISequence<char>, Dafny.ISequence<char>>> _168_parts = FloatCompare_Compile.__default.SplitE(x);
      if ((_168_parts).is_Some) {
        return _System.Tuple2<Dafny.ISequence<char>, BigInteger>.create(((_168_parts).dtor_value).dtor__0, FloatCompare_Compile.__default.StrToInt(((_168_parts).dtor_value).dtor__1, BigInteger.Zero));
      } else {
        return _System.Tuple2<Dafny.ISequence<char>, BigInteger>.create(x, BigInteger.Zero);
      }
    }
    public static Dafny.ISequence<char> SkipLeadingZeros(Dafny.ISequence<char> val) {
    TAIL_CALL_START: ;
      if (((new BigInteger((val).Count)).Sign == 1) && (((val).Select(BigInteger.Zero)) == ('0'))) {
        Dafny.ISequence<char> _in46 = (val).Drop(BigInteger.One);
        val = _in46;
        goto TAIL_CALL_START;
      } else {
        return val;
      }
    }
    public static Dafny.ISequence<char> SkipTrailingZeros(Dafny.ISequence<char> val) {
    TAIL_CALL_START: ;
      if (((new BigInteger((val).Count)).Sign == 1) && (((val).Select((new BigInteger((val).Count)) - (BigInteger.One))) == ('0'))) {
        Dafny.ISequence<char> _in47 = (val).Take((new BigInteger((val).Count)) - (BigInteger.One));
        val = _in47;
        goto TAIL_CALL_START;
      } else {
        return val;
      }
    }
    public static _System._ITuple2<Dafny.ISequence<char>, Dafny.ISequence<char>> SplitDot(Dafny.ISequence<char> x) {
      Wrappers_Compile._IOption<_System._ITuple2<Dafny.ISequence<char>, Dafny.ISequence<char>>> _169_parts = StandardLibrary_Compile.__default.SplitOnce_q<char>(x, '.');
      if ((_169_parts).is_Some) {
        return _System.Tuple2<Dafny.ISequence<char>, Dafny.ISequence<char>>.create(FloatCompare_Compile.__default.SkipLeadingZeros(((_169_parts).dtor_value).dtor__0), FloatCompare_Compile.__default.SkipTrailingZeros(((_169_parts).dtor_value).dtor__1));
      } else {
        return _System.Tuple2<Dafny.ISequence<char>, Dafny.ISequence<char>>.create(FloatCompare_Compile.__default.SkipLeadingZeros(x), Dafny.Sequence<char>.FromString(""));
      }
    }
    public static sbyte StrCmp(Dafny.ISequence<char> x, Dafny.ISequence<char> y)
    {
    TAIL_CALL_START: ;
      if (((new BigInteger((x).Count)).Sign == 0) && ((new BigInteger((y).Count)).Sign == 0)) {
        return (sbyte)(0);
      } else if ((new BigInteger((x).Count)).Sign == 0) {
        return (sbyte)(-1);
      } else if ((new BigInteger((y).Count)).Sign == 0) {
        return (sbyte)(1);
      } else if (((x).Select(BigInteger.Zero)) < ((y).Select(BigInteger.Zero))) {
        return (sbyte)(-1);
      } else if (((x).Select(BigInteger.Zero)) > ((y).Select(BigInteger.Zero))) {
        return (sbyte)(1);
      } else {
        Dafny.ISequence<char> _in48 = (x).Drop(BigInteger.One);
        Dafny.ISequence<char> _in49 = (y).Drop(BigInteger.One);
        x = _in48;
        y = _in49;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<char> AppendZeros(Dafny.ISequence<char> x, BigInteger newLength)
    {
      return Dafny.Sequence<char>.Concat(x, ((System.Func<Dafny.ISequence<char>>) (() => {
        BigInteger dim4 = (newLength) - (new BigInteger((x).Count));
        var arr4 = new char[Dafny.Helpers.ToIntChecked(dim4, "array size exceeds memory limit")];
        for (int i4 = 0; i4 < dim4; i4++) {
          var _170_i = (BigInteger) i4;
          arr4[(int)(_170_i)] = '0';
        }
        return Dafny.Sequence<char>.FromArray(arr4);
      }))());
    }
    public static sbyte CompareFloatInner(Dafny.ISequence<char> x, Dafny.ISequence<char> y)
    {
      _System._ITuple2<Dafny.ISequence<char>, BigInteger> _171_xParts = FloatCompare_Compile.__default.SplitExp(x);
      _System._ITuple2<Dafny.ISequence<char>, BigInteger> _172_yParts = FloatCompare_Compile.__default.SplitExp(y);
      _System._ITuple2<Dafny.ISequence<char>, Dafny.ISequence<char>> _173_xNum = FloatCompare_Compile.__default.SplitDot((_171_xParts).dtor__0);
      _System._ITuple2<Dafny.ISequence<char>, Dafny.ISequence<char>> _174_yNum = FloatCompare_Compile.__default.SplitDot((_172_yParts).dtor__0);
      Dafny.ISequence<char> _175_xDigits = FloatCompare_Compile.__default.SkipLeadingZeros(Dafny.Sequence<char>.Concat((_173_xNum).dtor__0, (_173_xNum).dtor__1));
      Dafny.ISequence<char> _176_yDigits = FloatCompare_Compile.__default.SkipLeadingZeros(Dafny.Sequence<char>.Concat((_174_yNum).dtor__0, (_174_yNum).dtor__1));
      BigInteger _177_xExp = ((_171_xParts).dtor__1) - (new BigInteger(((_173_xNum).dtor__1).Count));
      BigInteger _178_yExp = ((_172_yParts).dtor__1) - (new BigInteger(((_174_yNum).dtor__1).Count));
      BigInteger _179_logX = (_177_xExp) + (new BigInteger((_175_xDigits).Count));
      BigInteger _180_logY = (_178_yExp) + (new BigInteger((_176_yDigits).Count));
      if ((_179_logX) > (_180_logY)) {
        return (sbyte)(1);
      } else if ((_180_logY) > (_179_logX)) {
        return (sbyte)(-1);
      } else if ((new BigInteger((_175_xDigits).Count)) < (new BigInteger((_176_yDigits).Count))) {
        return FloatCompare_Compile.__default.StrCmp(FloatCompare_Compile.__default.AppendZeros(_175_xDigits, new BigInteger((_176_yDigits).Count)), _176_yDigits);
      } else if ((new BigInteger((_176_yDigits).Count)) < (new BigInteger((_175_xDigits).Count))) {
        return FloatCompare_Compile.__default.StrCmp(_175_xDigits, FloatCompare_Compile.__default.AppendZeros(_176_yDigits, new BigInteger((_175_xDigits).Count)));
      } else {
        return FloatCompare_Compile.__default.StrCmp(_175_xDigits, _176_yDigits);
      }
    }
    public static bool IsNegative(Dafny.ISequence<char> x) {
      return ((new BigInteger((x).Count)).Sign == 1) && (((x).Select(BigInteger.Zero)) == ('-'));
    }
    public static Dafny.ISequence<char> SkipLeadingPlus(Dafny.ISequence<char> x) {
      if (((new BigInteger((x).Count)).Sign == 1) && (((x).Select(BigInteger.Zero)) == ('+'))) {
        return (x).Drop(BigInteger.One);
      } else {
        return x;
      }
    }
    public static bool IsZero(Dafny.ISequence<char> x) {
    TAIL_CALL_START: ;
      if ((new BigInteger((x).Count)).Sign == 0) {
        return true;
      } else if ((((x).Select(BigInteger.Zero)) == ('0')) || (((x).Select(BigInteger.Zero)) == ('.'))) {
        Dafny.ISequence<char> _in50 = (x).Drop(BigInteger.One);
        x = _in50;
        goto TAIL_CALL_START;
      } else if ((('1') <= ((x).Select(BigInteger.Zero))) && (((x).Select(BigInteger.Zero)) <= ('9'))) {
        return false;
      } else {
        return true;
      }
    }
    public static Dafny.ISequence<char> RecognizeZero(Dafny.ISequence<char> x) {
      if (FloatCompare_Compile.__default.IsNegative(x)) {
        if (FloatCompare_Compile.__default.IsZero((x).Drop(BigInteger.One))) {
          return Dafny.Sequence<char>.FromString("0");
        } else {
          return x;
        }
      } else if (FloatCompare_Compile.__default.IsZero(x)) {
        return Dafny.Sequence<char>.FromString("0");
      } else {
        return x;
      }
    }
    public static Dafny.ISequence<char> CleanNumber(Dafny.ISequence<char> x) {
      return FloatCompare_Compile.__default.RecognizeZero(FloatCompare_Compile.__default.SkipLeadingPlus(FloatCompare_Compile.__default.SkipLeadingSpace(x)));
    }
    public static sbyte CompareFloat(Dafny.ISequence<char> x, Dafny.ISequence<char> y)
    {
      Dafny.ISequence<char> _181_x = FloatCompare_Compile.__default.CleanNumber(x);
      Dafny.ISequence<char> _182_y = FloatCompare_Compile.__default.CleanNumber(y);
      if ((FloatCompare_Compile.__default.IsNegative(_181_x)) && (FloatCompare_Compile.__default.IsNegative(_182_y))) {
        return FloatCompare_Compile.__default.CompareFloatInner((_182_y).Drop(BigInteger.One), (_181_x).Drop(BigInteger.One));
      } else if (FloatCompare_Compile.__default.IsNegative(_181_x)) {
        return (sbyte)(-1);
      } else if (FloatCompare_Compile.__default.IsNegative(_182_y)) {
        return (sbyte)(1);
      } else {
        return FloatCompare_Compile.__default.CompareFloatInner(_181_x, _182_y);
      }
    }
    public static sbyte Less { get {
      return (sbyte)(-1);
    } }
    public static sbyte Equal { get {
      return (sbyte)(0);
    } }
    public static sbyte Greater { get {
      return (sbyte)(1);
    } }
  }
} // end of namespace FloatCompare_Compile
namespace HexStrings_Compile {

  public partial class HexString {
    private static readonly Dafny.TypeDescriptor<Dafny.ISequence<char>> _TYPE = new Dafny.TypeDescriptor<Dafny.ISequence<char>>(Dafny.Sequence<char>.Empty);
    public static Dafny.TypeDescriptor<Dafny.ISequence<char>> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class LooseHexString {
    private static readonly Dafny.TypeDescriptor<Dafny.ISequence<char>> _TYPE = new Dafny.TypeDescriptor<Dafny.ISequence<char>>(Dafny.Sequence<char>.Empty);
    public static Dafny.TypeDescriptor<Dafny.ISequence<char>> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class __default {
    public static char HexChar(byte x) {
      if ((x) < ((byte)(10))) {
        return (char)(('0') + ((char)(x)));
      } else {
        return (char)(('a') + ((char)((byte)((x) - ((byte)(10))))));
      }
    }
    public static bool IsLooseHexChar(char ch) {
      return (((('0') <= (ch)) && ((ch) <= ('9'))) || ((('a') <= (ch)) && ((ch) <= ('f')))) || ((('A') <= (ch)) && ((ch) <= ('F')));
    }
    public static bool IsHexChar(char ch) {
      return ((('0') <= (ch)) && ((ch) <= ('9'))) || ((('a') <= (ch)) && ((ch) <= ('f')));
    }
    public static bool IsHexString(Dafny.ISequence<char> s) {
      return Dafny.Helpers.Id<Func<Dafny.ISequence<char>, bool>>((_183_s) => Dafny.Helpers.Quantifier<char>((_183_s).UniqueElements, true, (((_forall_var_3) => {
        char _184_ch = (char)_forall_var_3;
        return !((_183_s).Contains(_184_ch)) || (HexStrings_Compile.__default.IsHexChar(_184_ch));
      }))))(s);
    }
    public static bool IsLooseHexString(Dafny.ISequence<char> s) {
      return Dafny.Helpers.Id<Func<Dafny.ISequence<char>, bool>>((_185_s) => Dafny.Helpers.Quantifier<char>((_185_s).UniqueElements, true, (((_forall_var_4) => {
        char _186_ch = (char)_forall_var_4;
        return !((_185_s).Contains(_186_ch)) || (HexStrings_Compile.__default.IsLooseHexChar(_186_ch));
      }))))(s);
    }
    public static byte HexVal(char ch) {
      if ((('0') <= (ch)) && ((ch) <= ('9'))) {
        return (byte)(((byte)(ch)) - ((byte)('0')));
      } else if ((('a') <= (ch)) && ((ch) <= ('f'))) {
        return (byte)(((byte)(((byte)(ch)) - ((byte)('a')))) + ((byte)(10)));
      } else {
        return (byte)(((byte)(((byte)(ch)) - ((byte)('A')))) + ((byte)(10)));
      }
    }
    public static Dafny.ISequence<char> HexStr(byte x) {
      if ((x) < ((byte)(16))) {
        Dafny.ISequence<char> _187_res = Dafny.Sequence<char>.FromElements('0', HexStrings_Compile.__default.HexChar(x));
        return _187_res;
      } else {
        Dafny.ISequence<char> _188_res = Dafny.Sequence<char>.FromElements(HexStrings_Compile.__default.HexChar((byte)((byte)((x) / ((byte)(16))))), HexStrings_Compile.__default.HexChar((byte)((byte)((x) % ((byte)(16))))));
        return _188_res;
      }
    }
    public static byte HexValue(Dafny.ISequence<char> x) {
      return (byte)(((byte)((HexStrings_Compile.__default.HexVal((x).Select(BigInteger.Zero))) * ((byte)(16)))) + (HexStrings_Compile.__default.HexVal((x).Select(BigInteger.One))));
    }
    public static Dafny.ISequence<char> ToHexString(Dafny.ISequence<byte> val) {
      Dafny.ISequence<char> _189___accumulator = Dafny.Sequence<char>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((val).Count)).Sign == 0) {
        return Dafny.Sequence<char>.Concat(_189___accumulator, Dafny.Sequence<char>.FromElements());
      } else {
        _189___accumulator = Dafny.Sequence<char>.Concat(_189___accumulator, HexStrings_Compile.__default.HexStr((val).Select(BigInteger.Zero)));
        Dafny.ISequence<byte> _in51 = (val).Drop(BigInteger.One);
        val = _in51;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<byte> FromHexString(Dafny.ISequence<char> data) {
      Dafny.ISequence<byte> _190___accumulator = Dafny.Sequence<byte>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((data).Count)).Sign == 0) {
        return Dafny.Sequence<byte>.Concat(_190___accumulator, Dafny.Sequence<byte>.FromElements());
      } else if ((Dafny.Helpers.EuclideanModulus(new BigInteger((data).Count), new BigInteger(2))) == (BigInteger.One)) {
        _190___accumulator = Dafny.Sequence<byte>.Concat(_190___accumulator, Dafny.Sequence<byte>.FromElements(HexStrings_Compile.__default.HexVal((data).Select(BigInteger.Zero))));
        Dafny.ISequence<char> _in52 = (data).Drop(BigInteger.One);
        data = _in52;
        goto TAIL_CALL_START;
      } else {
        _190___accumulator = Dafny.Sequence<byte>.Concat(_190___accumulator, Dafny.Sequence<byte>.FromElements(HexStrings_Compile.__default.HexValue((data).Take(new BigInteger(2)))));
        Dafny.ISequence<char> _in53 = (data).Drop(new BigInteger(2));
        data = _in53;
        goto TAIL_CALL_START;
      }
    }
  }
} // end of namespace HexStrings_Compile
namespace SortedSets {

} // end of namespace SortedSets
namespace Sorting_Compile {

  public partial class __default {
    public static bool LexicographicByteSeqBelow(Dafny.ISequence<byte> x, Dafny.ISequence<byte> y)
    {
      return Sorting_Compile.__default.LexicographicByteSeqBelowAux(x, y, BigInteger.Zero);
    }
    public static bool LexicographicByteSeqBelowAux(Dafny.ISequence<byte> x, Dafny.ISequence<byte> y, BigInteger n)
    {
      return (((n) == (new BigInteger((x).Count))) || (((n) != (new BigInteger((y).Count))) && (((x).Select(n)) < ((y).Select(n))))) || ((((n) != (new BigInteger((y).Count))) && (((x).Select(n)) == ((y).Select(n)))) && (Sorting_Compile.__default.LexicographicByteSeqBelowAux(x, y, (n) + (BigInteger.One))));
    }
    public static void SelectionSort<__Data>(__Data[] a, Func<__Data, __Data, bool> below)
    {
      BigInteger _191_m;
      _191_m = BigInteger.Zero;
      while ((_191_m) < (new BigInteger((a).Length))) {
        BigInteger _192_mindex;
        BigInteger _193_n;
        BigInteger _rhs2 = _191_m;
        BigInteger _rhs3 = (_191_m) + (BigInteger.One);
        _192_mindex = _rhs2;
        _193_n = _rhs3;
        while ((_193_n) < (new BigInteger((a).Length))) {
          if (!(Dafny.Helpers.Id<Func<__Data, __Data, bool>>(below)((a)[(int)(_192_mindex)], (a)[(int)(_193_n)]))) {
            _192_mindex = _193_n;
          }
          _193_n = (_193_n) + (BigInteger.One);
        }
        __Data _rhs4 = (a)[(int)(_192_mindex)];
        __Data _rhs5 = (a)[(int)(_191_m)];
        __Data[] _lhs0 = a;
        BigInteger _lhs1 = _191_m;
        __Data[] _lhs2 = a;
        BigInteger _lhs3 = _192_mindex;
        _lhs0[(int)(_lhs1)] = _rhs4;
        _lhs2[(int)(_lhs3)] = _rhs5;
        _191_m = (_191_m) + (BigInteger.One);
      }
    }
  }
} // end of namespace Sorting_Compile
namespace Streams_Compile {

  public partial class SeqReader<T> {
    public SeqReader() {
      this.pos = BigInteger.Zero;
      this._data = Dafny.Sequence<T>.Empty;
    }
    public BigInteger pos {get; set;}
    public void __ctor(Dafny.ISequence<T> s)
    {
      (this)._data = s;
      (this).pos = BigInteger.Zero;
    }
    public Dafny.ISequence<T> ReadElements(BigInteger n)
    {
      Dafny.ISequence<T> elems = Dafny.Sequence<T>.Empty;
      elems = (((this).data).Drop(this.pos)).Take(n);
      (this).pos = (this.pos) + (n);
      elems = elems;
      return elems;
      return elems;
    }
    public Wrappers_Compile._IResult<Dafny.ISequence<T>, Dafny.ISequence<char>> ReadExact(BigInteger n)
    {
      Wrappers_Compile._IResult<Dafny.ISequence<T>, Dafny.ISequence<char>> res = Wrappers_Compile.Result<Dafny.ISequence<T>, Dafny.ISequence<char>>.Default(Dafny.Sequence<T>.Empty);
      if ((n) > ((new BigInteger(((this).data).Count)) - (this.pos))) {
        res = Wrappers_Compile.Result<Dafny.ISequence<T>, Dafny.ISequence<char>>.create_Failure(Dafny.Sequence<char>.FromString("IO Error: Not enough elements left on stream."));
        return res;
      } else {
        Dafny.ISequence<T> _194_elements;
        Dafny.ISequence<T> _out8;
        _out8 = (this).ReadElements(n);
        _194_elements = _out8;
        res = Wrappers_Compile.Result<Dafny.ISequence<T>, Dafny.ISequence<char>>.create_Success(_194_elements);
        return res;
      }
      return res;
    }
    public Dafny.ISequence<T> _data {get; set;}
    public Dafny.ISequence<T> data { get {
      return this._data;
    } }
  }

  public partial class ByteReader {
    public ByteReader() {
      this._reader = default(Streams_Compile.SeqReader<byte>);
    }
    public void __ctor(Dafny.ISequence<byte> s)
    {
      Streams_Compile.SeqReader<byte> _195_mr;
      Streams_Compile.SeqReader<byte> _nw2 = new Streams_Compile.SeqReader<byte>();
      _nw2.__ctor(s);
      _195_mr = _nw2;
      (this)._reader = _195_mr;
    }
    public Wrappers_Compile._IResult<byte, Dafny.ISequence<char>> ReadByte()
    {
      Wrappers_Compile._IResult<byte, Dafny.ISequence<char>> res = Wrappers_Compile.Result<byte, Dafny.ISequence<char>>.Default(0);
      Dafny.ISequence<byte> _196_bytes;
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, Dafny.ISequence<char>> _197_valueOrError0 = Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>>.Default(Dafny.Sequence<byte>.Empty);
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, Dafny.ISequence<char>> _out9;
      _out9 = ((this).reader).ReadExact(BigInteger.One);
      _197_valueOrError0 = _out9;
      if ((_197_valueOrError0).IsFailure()) {
        res = (_197_valueOrError0).PropagateFailure<byte>();
        return res;
      }
      _196_bytes = (_197_valueOrError0).Extract();
      res = Wrappers_Compile.Result<byte, Dafny.ISequence<char>>.create_Success((_196_bytes).Select(BigInteger.Zero));
      return res;
      return res;
    }
    public Wrappers_Compile._IResult<Dafny.ISequence<byte>, Dafny.ISequence<char>> ReadBytes(BigInteger n)
    {
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, Dafny.ISequence<char>> res = Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>>.Default(Dafny.Sequence<byte>.Empty);
      Dafny.ISequence<byte> _198_bytes;
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, Dafny.ISequence<char>> _199_valueOrError0 = Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>>.Default(Dafny.Sequence<byte>.Empty);
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, Dafny.ISequence<char>> _out10;
      _out10 = ((this).reader).ReadExact(n);
      _199_valueOrError0 = _out10;
      if ((_199_valueOrError0).IsFailure()) {
        res = (_199_valueOrError0).PropagateFailure<Dafny.ISequence<byte>>();
        return res;
      }
      _198_bytes = (_199_valueOrError0).Extract();
      res = Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>>.create_Success(_198_bytes);
      return res;
      return res;
    }
    public Wrappers_Compile._IResult<ushort, Dafny.ISequence<char>> ReadUInt16()
    {
      Wrappers_Compile._IResult<ushort, Dafny.ISequence<char>> res = Wrappers_Compile.Result<ushort, Dafny.ISequence<char>>.Default(0);
      Dafny.ISequence<byte> _200_bytes;
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, Dafny.ISequence<char>> _201_valueOrError0 = Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>>.Default(Dafny.Sequence<byte>.Empty);
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, Dafny.ISequence<char>> _out11;
      _out11 = ((this).reader).ReadExact(new BigInteger(2));
      _201_valueOrError0 = _out11;
      if ((_201_valueOrError0).IsFailure()) {
        res = (_201_valueOrError0).PropagateFailure<ushort>();
        return res;
      }
      _200_bytes = (_201_valueOrError0).Extract();
      ushort _202_n;
      _202_n = StandardLibrary_mUInt_Compile.__default.SeqToUInt16(_200_bytes);
      res = Wrappers_Compile.Result<ushort, Dafny.ISequence<char>>.create_Success(_202_n);
      return res;
      return res;
    }
    public Wrappers_Compile._IResult<uint, Dafny.ISequence<char>> ReadUInt32()
    {
      Wrappers_Compile._IResult<uint, Dafny.ISequence<char>> res = Wrappers_Compile.Result<uint, Dafny.ISequence<char>>.Default(0);
      Dafny.ISequence<byte> _203_bytes;
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, Dafny.ISequence<char>> _204_valueOrError0 = Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>>.Default(Dafny.Sequence<byte>.Empty);
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, Dafny.ISequence<char>> _out12;
      _out12 = ((this).reader).ReadExact(new BigInteger(4));
      _204_valueOrError0 = _out12;
      if ((_204_valueOrError0).IsFailure()) {
        res = (_204_valueOrError0).PropagateFailure<uint>();
        return res;
      }
      _203_bytes = (_204_valueOrError0).Extract();
      uint _205_n;
      _205_n = StandardLibrary_mUInt_Compile.__default.SeqToUInt32(_203_bytes);
      res = Wrappers_Compile.Result<uint, Dafny.ISequence<char>>.create_Success(_205_n);
      return res;
      return res;
    }
    public Wrappers_Compile._IResult<ulong, Dafny.ISequence<char>> ReadUInt64()
    {
      Wrappers_Compile._IResult<ulong, Dafny.ISequence<char>> res = Wrappers_Compile.Result<ulong, Dafny.ISequence<char>>.Default(0);
      Dafny.ISequence<byte> _206_bytes;
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, Dafny.ISequence<char>> _207_valueOrError0 = Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>>.Default(Dafny.Sequence<byte>.Empty);
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, Dafny.ISequence<char>> _out13;
      _out13 = ((this).reader).ReadExact(new BigInteger(8));
      _207_valueOrError0 = _out13;
      if ((_207_valueOrError0).IsFailure()) {
        res = (_207_valueOrError0).PropagateFailure<ulong>();
        return res;
      }
      _206_bytes = (_207_valueOrError0).Extract();
      ulong _208_n;
      _208_n = StandardLibrary_mUInt_Compile.__default.SeqToUInt64(_206_bytes);
      res = Wrappers_Compile.Result<ulong, Dafny.ISequence<char>>.create_Success(_208_n);
      return res;
      return res;
    }
    public bool IsDoneReading()
    {
      bool b = false;
      b = (new BigInteger((((this).reader).data).Count)) == ((this).reader.pos);
      return b;
      return b;
    }
    public BigInteger GetSizeRead()
    {
      BigInteger n = BigInteger.Zero;
      n = (this).reader.pos;
      return n;
      return n;
    }
    public Streams_Compile.SeqReader<byte> _reader {get; set;}
    public Streams_Compile.SeqReader<byte> reader { get {
      return this._reader;
    } }
  }

  public partial class SeqWriter<T> {
    public SeqWriter() {
      this.data = Dafny.Sequence<T>.Empty;
    }
    public Dafny.ISequence<T> data {get; set;}
    public void __ctor()
    {
      (this).data = Dafny.Sequence<T>.FromElements();
    }
    public BigInteger WriteElements(Dafny.ISequence<T> elems)
    {
      BigInteger n = BigInteger.Zero;
      (this).data = Dafny.Sequence<T>.Concat(this.data, elems);
      n = new BigInteger((elems).Count);
      return n;
      return n;
    }
  }

  public partial class ByteWriter {
    public ByteWriter() {
      this._writer = default(Streams_Compile.SeqWriter<byte>);
    }
    public void __ctor()
    {
      Streams_Compile.SeqWriter<byte> _209_mw;
      Streams_Compile.SeqWriter<byte> _nw3 = new Streams_Compile.SeqWriter<byte>();
      _nw3.__ctor();
      _209_mw = _nw3;
      (this)._writer = _209_mw;
    }
    public BigInteger WriteByte(byte n)
    {
      BigInteger r = BigInteger.Zero;
      BigInteger _out14;
      _out14 = ((this).writer).WriteElements(Dafny.Sequence<byte>.FromElements(n));
      r = _out14;
      return r;
    }
    public BigInteger WriteBytes(Dafny.ISequence<byte> s)
    {
      BigInteger r = BigInteger.Zero;
      BigInteger _out15;
      _out15 = ((this).writer).WriteElements(s);
      r = _out15;
      return r;
    }
    public BigInteger WriteUInt16(ushort n)
    {
      BigInteger r = BigInteger.Zero;
      BigInteger _out16;
      _out16 = ((this).writer).WriteElements(StandardLibrary_mUInt_Compile.__default.UInt16ToSeq(n));
      r = _out16;
      return r;
    }
    public BigInteger WriteUInt32(uint n)
    {
      BigInteger r = BigInteger.Zero;
      BigInteger _out17;
      _out17 = ((this).writer).WriteElements(StandardLibrary_mUInt_Compile.__default.UInt32ToSeq(n));
      r = _out17;
      return r;
    }
    public Dafny.ISequence<byte> GetDataWritten() {
      return (this).writer.data;
    }
    public BigInteger GetSizeWritten() {
      return new BigInteger(((this).writer.data).Count);
    }
    public Streams_Compile.SeqWriter<byte> _writer {get; set;}
    public Streams_Compile.SeqWriter<byte> writer { get {
      return this._writer;
    } }
  }

} // end of namespace Streams_Compile
namespace Time {

} // end of namespace Time
namespace UTF8 {

  public partial class ValidUTF8Bytes {
    private static readonly Dafny.ISequence<byte> Witness = Dafny.Sequence<byte>.FromElements();
    public static Dafny.ISequence<byte> Default() {
      return Witness;
    }
    private static readonly Dafny.TypeDescriptor<Dafny.ISequence<byte>> _TYPE = new Dafny.TypeDescriptor<Dafny.ISequence<byte>>(UTF8.ValidUTF8Bytes.Default());
    public static Dafny.TypeDescriptor<Dafny.ISequence<byte>> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class __default {
    public static bool IsASCIIString(Dafny.ISequence<char> s) {
      return Dafny.Helpers.Id<Func<Dafny.ISequence<char>, bool>>((_210_s) => Dafny.Helpers.Quantifier<BigInteger>(Dafny.Helpers.IntegerRange(BigInteger.Zero, new BigInteger((_210_s).Count)), true, (((_forall_var_5) => {
        BigInteger _211_i = (BigInteger)_forall_var_5;
        return !(((_211_i).Sign != -1) && ((_211_i) < (new BigInteger((_210_s).Count)))) || ((new BigInteger((_210_s).Select(_211_i))) < (new BigInteger(128)));
      }))))(s);
    }
    public static Dafny.ISequence<byte> EncodeAscii(Dafny.ISequence<char> s) {
      Dafny.ISequence<byte> _212___accumulator = Dafny.Sequence<byte>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((s).Count)).Sign == 0) {
        return Dafny.Sequence<byte>.Concat(_212___accumulator, Dafny.Sequence<byte>.FromElements());
      } else {
        Dafny.ISequence<byte> _213_x = Dafny.Sequence<byte>.FromElements((byte)((s).Select(BigInteger.Zero)));
        _212___accumulator = Dafny.Sequence<byte>.Concat(_212___accumulator, _213_x);
        Dafny.ISequence<char> _in54 = (s).Drop(BigInteger.One);
        s = _in54;
        goto TAIL_CALL_START;
      }
    }
    public static bool Uses1Byte(Dafny.ISequence<byte> s) {
      return (((byte)(0)) <= ((s).Select(BigInteger.Zero))) && (((s).Select(BigInteger.Zero)) <= ((byte)(127)));
    }
    public static bool Uses2Bytes(Dafny.ISequence<byte> s) {
      return ((((byte)(194)) <= ((s).Select(BigInteger.Zero))) && (((s).Select(BigInteger.Zero)) <= ((byte)(223)))) && ((((byte)(128)) <= ((s).Select(BigInteger.One))) && (((s).Select(BigInteger.One)) <= ((byte)(191))));
    }
    public static bool Uses3Bytes(Dafny.ISequence<byte> s) {
      return (((((((s).Select(BigInteger.Zero)) == ((byte)(224))) && ((((byte)(160)) <= ((s).Select(BigInteger.One))) && (((s).Select(BigInteger.One)) <= ((byte)(191))))) && ((((byte)(128)) <= ((s).Select(new BigInteger(2)))) && (((s).Select(new BigInteger(2))) <= ((byte)(191))))) || ((((((byte)(225)) <= ((s).Select(BigInteger.Zero))) && (((s).Select(BigInteger.Zero)) <= ((byte)(236)))) && ((((byte)(128)) <= ((s).Select(BigInteger.One))) && (((s).Select(BigInteger.One)) <= ((byte)(191))))) && ((((byte)(128)) <= ((s).Select(new BigInteger(2)))) && (((s).Select(new BigInteger(2))) <= ((byte)(191)))))) || (((((s).Select(BigInteger.Zero)) == ((byte)(237))) && ((((byte)(128)) <= ((s).Select(BigInteger.One))) && (((s).Select(BigInteger.One)) <= ((byte)(159))))) && ((((byte)(128)) <= ((s).Select(new BigInteger(2)))) && (((s).Select(new BigInteger(2))) <= ((byte)(191)))))) || ((((((byte)(238)) <= ((s).Select(BigInteger.Zero))) && (((s).Select(BigInteger.Zero)) <= ((byte)(239)))) && ((((byte)(128)) <= ((s).Select(BigInteger.One))) && (((s).Select(BigInteger.One)) <= ((byte)(191))))) && ((((byte)(128)) <= ((s).Select(new BigInteger(2)))) && (((s).Select(new BigInteger(2))) <= ((byte)(191)))));
    }
    public static bool Uses4Bytes(Dafny.ISequence<byte> s) {
      return (((((((s).Select(BigInteger.Zero)) == ((byte)(240))) && ((((byte)(144)) <= ((s).Select(BigInteger.One))) && (((s).Select(BigInteger.One)) <= ((byte)(191))))) && ((((byte)(128)) <= ((s).Select(new BigInteger(2)))) && (((s).Select(new BigInteger(2))) <= ((byte)(191))))) && ((((byte)(128)) <= ((s).Select(new BigInteger(3)))) && (((s).Select(new BigInteger(3))) <= ((byte)(191))))) || (((((((byte)(241)) <= ((s).Select(BigInteger.Zero))) && (((s).Select(BigInteger.Zero)) <= ((byte)(243)))) && ((((byte)(128)) <= ((s).Select(BigInteger.One))) && (((s).Select(BigInteger.One)) <= ((byte)(191))))) && ((((byte)(128)) <= ((s).Select(new BigInteger(2)))) && (((s).Select(new BigInteger(2))) <= ((byte)(191))))) && ((((byte)(128)) <= ((s).Select(new BigInteger(3)))) && (((s).Select(new BigInteger(3))) <= ((byte)(191)))))) || ((((((s).Select(BigInteger.Zero)) == ((byte)(244))) && ((((byte)(128)) <= ((s).Select(BigInteger.One))) && (((s).Select(BigInteger.One)) <= ((byte)(143))))) && ((((byte)(128)) <= ((s).Select(new BigInteger(2)))) && (((s).Select(new BigInteger(2))) <= ((byte)(191))))) && ((((byte)(128)) <= ((s).Select(new BigInteger(3)))) && (((s).Select(new BigInteger(3))) <= ((byte)(191)))));
    }
    public static bool ValidUTF8Range(Dafny.ISequence<byte> a, BigInteger lo, BigInteger hi)
    {
    TAIL_CALL_START: ;
      if ((lo) == (hi)) {
        return true;
      } else {
        Dafny.ISequence<byte> _214_r = (a).Subsequence(lo, hi);
        if (UTF8.__default.Uses1Byte(_214_r)) {
          Dafny.ISequence<byte> _in55 = a;
          BigInteger _in56 = (lo) + (BigInteger.One);
          BigInteger _in57 = hi;
          a = _in55;
          lo = _in56;
          hi = _in57;
          goto TAIL_CALL_START;
        } else if (((new BigInteger(2)) <= (new BigInteger((_214_r).Count))) && (UTF8.__default.Uses2Bytes(_214_r))) {
          Dafny.ISequence<byte> _in58 = a;
          BigInteger _in59 = (lo) + (new BigInteger(2));
          BigInteger _in60 = hi;
          a = _in58;
          lo = _in59;
          hi = _in60;
          goto TAIL_CALL_START;
        } else if (((new BigInteger(3)) <= (new BigInteger((_214_r).Count))) && (UTF8.__default.Uses3Bytes(_214_r))) {
          Dafny.ISequence<byte> _in61 = a;
          BigInteger _in62 = (lo) + (new BigInteger(3));
          BigInteger _in63 = hi;
          a = _in61;
          lo = _in62;
          hi = _in63;
          goto TAIL_CALL_START;
        } else if (((new BigInteger(4)) <= (new BigInteger((_214_r).Count))) && (UTF8.__default.Uses4Bytes(_214_r))) {
          Dafny.ISequence<byte> _in64 = a;
          BigInteger _in65 = (lo) + (new BigInteger(4));
          BigInteger _in66 = hi;
          a = _in64;
          lo = _in65;
          hi = _in66;
          goto TAIL_CALL_START;
        } else {
          return false;
        }
      }
    }
    public static bool ValidUTF8Seq(Dafny.ISequence<byte> s) {
      return UTF8.__default.ValidUTF8Range(s, BigInteger.Zero, new BigInteger((s).Count));
    }
  }
} // end of namespace UTF8
namespace UUID {

} // end of namespace UUID
namespace MulInternalsNonlinear_Compile {

} // end of namespace MulInternalsNonlinear_Compile
namespace GeneralInternals_Compile {

} // end of namespace GeneralInternals_Compile
namespace MulInternals_Compile {

  public partial class __default {
    public static BigInteger MulPos(BigInteger x, BigInteger y)
    {
      BigInteger _215___accumulator = BigInteger.Zero;
    TAIL_CALL_START: ;
      if ((x).Sign == 0) {
        return (BigInteger.Zero) + (_215___accumulator);
      } else {
        _215___accumulator = (_215___accumulator) + (y);
        BigInteger _in67 = (x) - (BigInteger.One);
        BigInteger _in68 = y;
        x = _in67;
        y = _in68;
        goto TAIL_CALL_START;
      }
    }
    public static BigInteger MulRecursive(BigInteger x, BigInteger y)
    {
      if ((x).Sign != -1) {
        return MulInternals_Compile.__default.MulPos(x, y);
      } else {
        return (new BigInteger(-1)) * (MulInternals_Compile.__default.MulPos((new BigInteger(-1)) * (x), y));
      }
    }
  }
} // end of namespace MulInternals_Compile
namespace Mul_Compile {

} // end of namespace Mul_Compile
namespace ModInternalsNonlinear_Compile {

} // end of namespace ModInternalsNonlinear_Compile
namespace DivInternalsNonlinear_Compile {

} // end of namespace DivInternalsNonlinear_Compile
namespace ModInternals_Compile {

  public partial class __default {
    public static BigInteger ModRecursive(BigInteger x, BigInteger d)
    {
    TAIL_CALL_START: ;
      if ((x).Sign == -1) {
        BigInteger _in69 = (d) + (x);
        BigInteger _in70 = d;
        x = _in69;
        d = _in70;
        goto TAIL_CALL_START;
      } else if ((x) < (d)) {
        return x;
      } else {
        BigInteger _in71 = (x) - (d);
        BigInteger _in72 = d;
        x = _in71;
        d = _in72;
        goto TAIL_CALL_START;
      }
    }
  }
} // end of namespace ModInternals_Compile
namespace DivInternals_Compile {

  public partial class __default {
    public static BigInteger DivPos(BigInteger x, BigInteger d)
    {
      BigInteger _216___accumulator = BigInteger.Zero;
    TAIL_CALL_START: ;
      if ((x).Sign == -1) {
        _216___accumulator = (_216___accumulator) + (new BigInteger(-1));
        BigInteger _in73 = (x) + (d);
        BigInteger _in74 = d;
        x = _in73;
        d = _in74;
        goto TAIL_CALL_START;
      } else if ((x) < (d)) {
        return (BigInteger.Zero) + (_216___accumulator);
      } else {
        _216___accumulator = (_216___accumulator) + (BigInteger.One);
        BigInteger _in75 = (x) - (d);
        BigInteger _in76 = d;
        x = _in75;
        d = _in76;
        goto TAIL_CALL_START;
      }
    }
    public static BigInteger DivRecursive(BigInteger x, BigInteger d)
    {
      if ((d).Sign == 1) {
        return DivInternals_Compile.__default.DivPos(x, d);
      } else {
        return (new BigInteger(-1)) * (DivInternals_Compile.__default.DivPos(x, (new BigInteger(-1)) * (d)));
      }
    }
  }
} // end of namespace DivInternals_Compile
namespace DivMod_Compile {

} // end of namespace DivMod_Compile
namespace Power_Compile {

  public partial class __default {
    public static BigInteger Pow(BigInteger b, BigInteger e)
    {
      BigInteger _217___accumulator = BigInteger.One;
    TAIL_CALL_START: ;
      if ((e).Sign == 0) {
        return (BigInteger.One) * (_217___accumulator);
      } else {
        _217___accumulator = (_217___accumulator) * (b);
        BigInteger _in77 = b;
        BigInteger _in78 = (e) - (BigInteger.One);
        b = _in77;
        e = _in78;
        goto TAIL_CALL_START;
      }
    }
  }
} // end of namespace Power_Compile
namespace Logarithm_Compile {

  public partial class __default {
    public static BigInteger Log(BigInteger @base, BigInteger pow)
    {
      BigInteger _218___accumulator = BigInteger.Zero;
    TAIL_CALL_START: ;
      if ((pow) < (@base)) {
        return (BigInteger.Zero) + (_218___accumulator);
      } else {
        _218___accumulator = (_218___accumulator) + (BigInteger.One);
        BigInteger _in79 = @base;
        BigInteger _in80 = Dafny.Helpers.EuclideanDivision(pow, @base);
        @base = _in79;
        pow = _in80;
        goto TAIL_CALL_START;
      }
    }
  }
} // end of namespace Logarithm_Compile
namespace FileIO_Compile {

  public partial class __default {
    public static Wrappers_Compile._IResult<Dafny.ISequence<byte>, Dafny.ISequence<char>> ReadBytesFromFile(Dafny.ISequence<char> path)
    {
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, Dafny.ISequence<char>> res = Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>>.Default(Dafny.Sequence<byte>.Empty);
      bool _219_isError;
      Dafny.ISequence<byte> _220_bytesRead;
      Dafny.ISequence<char> _221_errorMsg;
      bool _out18;
      Dafny.ISequence<byte> _out19;
      Dafny.ISequence<char> _out20;
      DafnyLibraries.FileIO.INTERNAL_ReadBytesFromFile(path, out _out18, out _out19, out _out20);
      _219_isError = _out18;
      _220_bytesRead = _out19;
      _221_errorMsg = _out20;
      res = ((_219_isError) ? (Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>>.create_Failure(_221_errorMsg)) : (Wrappers_Compile.Result<Dafny.ISequence<byte>, Dafny.ISequence<char>>.create_Success(_220_bytesRead)));
      return res;
      return res;
    }
    public static Wrappers_Compile._IResult<_System._ITuple0, Dafny.ISequence<char>> WriteBytesToFile(Dafny.ISequence<char> path, Dafny.ISequence<byte> bytes)
    {
      Wrappers_Compile._IResult<_System._ITuple0, Dafny.ISequence<char>> res = Wrappers_Compile.Result<_System._ITuple0, Dafny.ISequence<char>>.Default(_System.Tuple0.Default());
      bool _222_isError;
      Dafny.ISequence<char> _223_errorMsg;
      bool _out21;
      Dafny.ISequence<char> _out22;
      DafnyLibraries.FileIO.INTERNAL_WriteBytesToFile(path, bytes, out _out21, out _out22);
      _222_isError = _out21;
      _223_errorMsg = _out22;
      res = ((_222_isError) ? (Wrappers_Compile.Result<_System._ITuple0, Dafny.ISequence<char>>.create_Failure(_223_errorMsg)) : (Wrappers_Compile.Result<_System._ITuple0, Dafny.ISequence<char>>.create_Success(_System.Tuple0.create())));
      return res;
      return res;
    }
  }
} // end of namespace FileIO_Compile
namespace Unicode_Compile {

  public partial class CodePoint {
    private static readonly Dafny.TypeDescriptor<uint> _TYPE = new Dafny.TypeDescriptor<uint>(0);
    public static Dafny.TypeDescriptor<uint> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class HighSurrogateCodePoint {
    private static readonly uint Witness = Unicode_Compile.__default.HIGH__SURROGATE__MIN;
    public static uint Default() {
      return Witness;
    }
    private static readonly Dafny.TypeDescriptor<uint> _TYPE = new Dafny.TypeDescriptor<uint>(Unicode_Compile.HighSurrogateCodePoint.Default());
    public static Dafny.TypeDescriptor<uint> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class LowSurrogateCodePoint {
    private static readonly uint Witness = Unicode_Compile.__default.LOW__SURROGATE__MIN;
    public static uint Default() {
      return Witness;
    }
    private static readonly Dafny.TypeDescriptor<uint> _TYPE = new Dafny.TypeDescriptor<uint>(Unicode_Compile.LowSurrogateCodePoint.Default());
    public static Dafny.TypeDescriptor<uint> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class ScalarValue {
    private static readonly Dafny.TypeDescriptor<uint> _TYPE = new Dafny.TypeDescriptor<uint>(0);
    public static Dafny.TypeDescriptor<uint> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class AssignedCodePoint {
    private static readonly Dafny.TypeDescriptor<uint> _TYPE = new Dafny.TypeDescriptor<uint>(0);
    public static Dafny.TypeDescriptor<uint> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class __default {
    public static uint HIGH__SURROGATE__MIN { get {
      return 55296U;
    } }
    public static uint HIGH__SURROGATE__MAX { get {
      return 56319U;
    } }
    public static uint LOW__SURROGATE__MIN { get {
      return 56320U;
    } }
    public static uint LOW__SURROGATE__MAX { get {
      return 57343U;
    } }
    public static Dafny.ISet<byte> ASSIGNED__PLANES { get {
      return Dafny.Set<byte>.FromElements((byte)(0), (byte)(1), (byte)(2), (byte)(3), (byte)(14), (byte)(15), (byte)(16));
    } }
  }
} // end of namespace Unicode_Compile
namespace Functions_Compile {

} // end of namespace Functions_Compile
namespace Utf8EncodingForm_Compile {

  public partial class __default {
    public static bool IsMinimalWellFormedCodeUnitSubsequence(Dafny.ISequence<byte> s) {
      if ((new BigInteger((s).Count)) == (BigInteger.One)) {
        bool _224_b = Utf8EncodingForm_Compile.__default.IsWellFormedSingleCodeUnitSequence(s);
        return _224_b;
      } else if ((new BigInteger((s).Count)) == (new BigInteger(2))) {
        bool _225_b = Utf8EncodingForm_Compile.__default.IsWellFormedDoubleCodeUnitSequence(s);
        return _225_b;
      } else if ((new BigInteger((s).Count)) == (new BigInteger(3))) {
        bool _226_b = Utf8EncodingForm_Compile.__default.IsWellFormedTripleCodeUnitSequence(s);
        return _226_b;
      } else if ((new BigInteger((s).Count)) == (new BigInteger(4))) {
        bool _227_b = Utf8EncodingForm_Compile.__default.IsWellFormedQuadrupleCodeUnitSequence(s);
        return _227_b;
      } else {
        return false;
      }
    }
    public static bool IsWellFormedSingleCodeUnitSequence(Dafny.ISequence<byte> s) {
      byte _228_firstByte = (s).Select(BigInteger.Zero);
      return (true) && ((((byte)(0)) <= (_228_firstByte)) && ((_228_firstByte) <= ((byte)(127))));
    }
    public static bool IsWellFormedDoubleCodeUnitSequence(Dafny.ISequence<byte> s) {
      byte _229_firstByte = (s).Select(BigInteger.Zero);
      byte _230_secondByte = (s).Select(BigInteger.One);
      return ((((byte)(194)) <= (_229_firstByte)) && ((_229_firstByte) <= ((byte)(223)))) && ((((byte)(128)) <= (_230_secondByte)) && ((_230_secondByte) <= ((byte)(191))));
    }
    public static bool IsWellFormedTripleCodeUnitSequence(Dafny.ISequence<byte> s) {
      byte _231_firstByte = (s).Select(BigInteger.Zero);
      byte _232_secondByte = (s).Select(BigInteger.One);
      byte _233_thirdByte = (s).Select(new BigInteger(2));
      return ((((((_231_firstByte) == ((byte)(224))) && ((((byte)(160)) <= (_232_secondByte)) && ((_232_secondByte) <= ((byte)(191))))) || (((((byte)(225)) <= (_231_firstByte)) && ((_231_firstByte) <= ((byte)(236)))) && ((((byte)(128)) <= (_232_secondByte)) && ((_232_secondByte) <= ((byte)(191)))))) || (((_231_firstByte) == ((byte)(237))) && ((((byte)(128)) <= (_232_secondByte)) && ((_232_secondByte) <= ((byte)(159)))))) || (((((byte)(238)) <= (_231_firstByte)) && ((_231_firstByte) <= ((byte)(239)))) && ((((byte)(128)) <= (_232_secondByte)) && ((_232_secondByte) <= ((byte)(191)))))) && ((((byte)(128)) <= (_233_thirdByte)) && ((_233_thirdByte) <= ((byte)(191))));
    }
    public static bool IsWellFormedQuadrupleCodeUnitSequence(Dafny.ISequence<byte> s) {
      byte _234_firstByte = (s).Select(BigInteger.Zero);
      byte _235_secondByte = (s).Select(BigInteger.One);
      byte _236_thirdByte = (s).Select(new BigInteger(2));
      byte _237_fourthByte = (s).Select(new BigInteger(3));
      return ((((((_234_firstByte) == ((byte)(240))) && ((((byte)(144)) <= (_235_secondByte)) && ((_235_secondByte) <= ((byte)(191))))) || (((((byte)(241)) <= (_234_firstByte)) && ((_234_firstByte) <= ((byte)(243)))) && ((((byte)(128)) <= (_235_secondByte)) && ((_235_secondByte) <= ((byte)(191)))))) || (((_234_firstByte) == ((byte)(244))) && ((((byte)(128)) <= (_235_secondByte)) && ((_235_secondByte) <= ((byte)(143)))))) && ((((byte)(128)) <= (_236_thirdByte)) && ((_236_thirdByte) <= ((byte)(191))))) && ((((byte)(128)) <= (_237_fourthByte)) && ((_237_fourthByte) <= ((byte)(191))));
    }
    public static Wrappers_Compile._IOption<Dafny.ISequence<byte>> SplitPrefixMinimalWellFormedCodeUnitSubsequence(Dafny.ISequence<byte> s) {
      if (((new BigInteger((s).Count)) >= (BigInteger.One)) && (Utf8EncodingForm_Compile.__default.IsWellFormedSingleCodeUnitSequence((s).Take(BigInteger.One)))) {
        return Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_Some((s).Take(BigInteger.One));
      } else if (((new BigInteger((s).Count)) >= (new BigInteger(2))) && (Utf8EncodingForm_Compile.__default.IsWellFormedDoubleCodeUnitSequence((s).Take(new BigInteger(2))))) {
        return Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_Some((s).Take(new BigInteger(2)));
      } else if (((new BigInteger((s).Count)) >= (new BigInteger(3))) && (Utf8EncodingForm_Compile.__default.IsWellFormedTripleCodeUnitSequence((s).Take(new BigInteger(3))))) {
        return Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_Some((s).Take(new BigInteger(3)));
      } else if (((new BigInteger((s).Count)) >= (new BigInteger(4))) && (Utf8EncodingForm_Compile.__default.IsWellFormedQuadrupleCodeUnitSequence((s).Take(new BigInteger(4))))) {
        return Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_Some((s).Take(new BigInteger(4)));
      } else {
        return Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_None();
      }
    }
    public static Dafny.ISequence<byte> EncodeScalarValue(uint v) {
      if ((v) <= (127U)) {
        return Utf8EncodingForm_Compile.__default.EncodeScalarValueSingleByte(v);
      } else if ((v) <= (2047U)) {
        return Utf8EncodingForm_Compile.__default.EncodeScalarValueDoubleByte(v);
      } else if ((v) <= (65535U)) {
        return Utf8EncodingForm_Compile.__default.EncodeScalarValueTripleByte(v);
      } else {
        return Utf8EncodingForm_Compile.__default.EncodeScalarValueQuadrupleByte(v);
      }
    }
    public static Dafny.ISequence<byte> EncodeScalarValueSingleByte(uint v) {
      byte _238_x = (byte)((v) & (127U));
      byte _239_firstByte = (byte)(_238_x);
      return Dafny.Sequence<byte>.FromElements(_239_firstByte);
    }
    public static Dafny.ISequence<byte> EncodeScalarValueDoubleByte(uint v) {
      byte _240_x = (byte)((v) & (63U));
      byte _241_y = (byte)(((v) & (1984U)) >> ((int)((byte)(6))));
      byte _242_firstByte = (byte)(((byte)(192)) | ((byte)(_241_y)));
      byte _243_secondByte = (byte)(((byte)(128)) | ((byte)(_240_x)));
      return Dafny.Sequence<byte>.FromElements(_242_firstByte, _243_secondByte);
    }
    public static Dafny.ISequence<byte> EncodeScalarValueTripleByte(uint v) {
      byte _244_x = (byte)((v) & (63U));
      byte _245_y = (byte)(((v) & (4032U)) >> ((int)((byte)(6))));
      byte _246_z = (byte)(((v) & (61440U)) >> ((int)((byte)(12))));
      byte _247_firstByte = (byte)(((byte)(224)) | ((byte)(_246_z)));
      byte _248_secondByte = (byte)(((byte)(128)) | ((byte)(_245_y)));
      byte _249_thirdByte = (byte)(((byte)(128)) | ((byte)(_244_x)));
      return Dafny.Sequence<byte>.FromElements(_247_firstByte, _248_secondByte, _249_thirdByte);
    }
    public static Dafny.ISequence<byte> EncodeScalarValueQuadrupleByte(uint v) {
      byte _250_x = (byte)((v) & (63U));
      byte _251_y = (byte)(((v) & (4032U)) >> ((int)((byte)(6))));
      byte _252_z = (byte)(((v) & (61440U)) >> ((int)((byte)(12))));
      byte _253_u2 = (byte)(((v) & (196608U)) >> ((int)((byte)(16))));
      byte _254_u1 = (byte)(((v) & (1835008U)) >> ((int)((byte)(18))));
      byte _255_firstByte = (byte)(((byte)(240)) | ((byte)(_254_u1)));
      byte _256_secondByte = (byte)(((byte)(((byte)(128)) | (unchecked((byte)(((byte)(((byte)(_253_u2)) << ((int)((byte)(4)))))))))) | ((byte)(_252_z)));
      byte _257_thirdByte = (byte)(((byte)(128)) | ((byte)(_251_y)));
      byte _258_fourthByte = (byte)(((byte)(128)) | ((byte)(_250_x)));
      return Dafny.Sequence<byte>.FromElements(_255_firstByte, _256_secondByte, _257_thirdByte, _258_fourthByte);
    }
    public static uint DecodeMinimalWellFormedCodeUnitSubsequence(Dafny.ISequence<byte> m) {
      if ((new BigInteger((m).Count)) == (BigInteger.One)) {
        return Utf8EncodingForm_Compile.__default.DecodeMinimalWellFormedCodeUnitSubsequenceSingleByte(m);
      } else if ((new BigInteger((m).Count)) == (new BigInteger(2))) {
        return Utf8EncodingForm_Compile.__default.DecodeMinimalWellFormedCodeUnitSubsequenceDoubleByte(m);
      } else if ((new BigInteger((m).Count)) == (new BigInteger(3))) {
        return Utf8EncodingForm_Compile.__default.DecodeMinimalWellFormedCodeUnitSubsequenceTripleByte(m);
      } else {
        return Utf8EncodingForm_Compile.__default.DecodeMinimalWellFormedCodeUnitSubsequenceQuadrupleByte(m);
      }
    }
    public static uint DecodeMinimalWellFormedCodeUnitSubsequenceSingleByte(Dafny.ISequence<byte> m) {
      byte _259_firstByte = (m).Select(BigInteger.Zero);
      byte _260_x = (byte)(_259_firstByte);
      return (uint)(_260_x);
    }
    public static uint DecodeMinimalWellFormedCodeUnitSubsequenceDoubleByte(Dafny.ISequence<byte> m) {
      byte _261_firstByte = (m).Select(BigInteger.Zero);
      byte _262_secondByte = (m).Select(BigInteger.One);
      uint _263_y = (uint)((byte)((_261_firstByte) & ((byte)(31))));
      uint _264_x = (uint)((byte)((_262_secondByte) & ((byte)(63))));
      return (unchecked((uint)(((_263_y) << ((int)((byte)(6)))) & (uint)0xFFFFFFU))) | ((uint)(_264_x));
    }
    public static uint DecodeMinimalWellFormedCodeUnitSubsequenceTripleByte(Dafny.ISequence<byte> m) {
      byte _265_firstByte = (m).Select(BigInteger.Zero);
      byte _266_secondByte = (m).Select(BigInteger.One);
      byte _267_thirdByte = (m).Select(new BigInteger(2));
      uint _268_z = (uint)((byte)((_265_firstByte) & ((byte)(15))));
      uint _269_y = (uint)((byte)((_266_secondByte) & ((byte)(63))));
      uint _270_x = (uint)((byte)((_267_thirdByte) & ((byte)(63))));
      return ((unchecked((uint)(((_268_z) << ((int)((byte)(12)))) & (uint)0xFFFFFFU))) | (unchecked((uint)(((_269_y) << ((int)((byte)(6)))) & (uint)0xFFFFFFU)))) | ((uint)(_270_x));
    }
    public static uint DecodeMinimalWellFormedCodeUnitSubsequenceQuadrupleByte(Dafny.ISequence<byte> m) {
      byte _271_firstByte = (m).Select(BigInteger.Zero);
      byte _272_secondByte = (m).Select(BigInteger.One);
      byte _273_thirdByte = (m).Select(new BigInteger(2));
      byte _274_fourthByte = (m).Select(new BigInteger(3));
      uint _275_u1 = (uint)((byte)((_271_firstByte) & ((byte)(7))));
      uint _276_u2 = (uint)((byte)(((byte)((_272_secondByte) & ((byte)(48)))) >> ((int)((byte)(4)))));
      uint _277_z = (uint)((byte)((_272_secondByte) & ((byte)(15))));
      uint _278_y = (uint)((byte)((_273_thirdByte) & ((byte)(63))));
      uint _279_x = (uint)((byte)((_274_fourthByte) & ((byte)(63))));
      return ((((unchecked((uint)(((_275_u1) << ((int)((byte)(18)))) & (uint)0xFFFFFFU))) | (unchecked((uint)(((_276_u2) << ((int)((byte)(16)))) & (uint)0xFFFFFFU)))) | (unchecked((uint)(((_277_z) << ((int)((byte)(12)))) & (uint)0xFFFFFFU)))) | (unchecked((uint)(((_278_y) << ((int)((byte)(6)))) & (uint)0xFFFFFFU)))) | ((uint)(_279_x));
    }
    public static Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<byte>>> PartitionCodeUnitSequenceChecked(Dafny.ISequence<byte> s)
    {
      Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<byte>>> maybeParts = Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<byte>>>.Default();
      if ((s).Equals(Dafny.Sequence<byte>.FromElements())) {
        maybeParts = Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<byte>>>.create_Some(Dafny.Sequence<Dafny.ISequence<byte>>.FromElements());
        return maybeParts;
      }
      Dafny.ISequence<Dafny.ISequence<byte>> _280_result;
      _280_result = Dafny.Sequence<Dafny.ISequence<byte>>.FromElements();
      Dafny.ISequence<byte> _281_rest;
      _281_rest = s;
      while ((new BigInteger((_281_rest).Count)).Sign == 1) {
        Dafny.ISequence<byte> _282_prefix;
        Wrappers_Compile._IOption<Dafny.ISequence<byte>> _283_valueOrError0 = Wrappers_Compile.Option<Dafny.ISequence<byte>>.Default();
        _283_valueOrError0 = Utf8EncodingForm_Compile.__default.SplitPrefixMinimalWellFormedCodeUnitSubsequence(_281_rest);
        if ((_283_valueOrError0).IsFailure()) {
          maybeParts = (_283_valueOrError0).PropagateFailure<Dafny.ISequence<Dafny.ISequence<byte>>>();
          return maybeParts;
        }
        _282_prefix = (_283_valueOrError0).Extract();
        _280_result = Dafny.Sequence<Dafny.ISequence<byte>>.Concat(_280_result, Dafny.Sequence<Dafny.ISequence<byte>>.FromElements(_282_prefix));
        _281_rest = (_281_rest).Drop(new BigInteger((_282_prefix).Count));
      }
      maybeParts = Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<byte>>>.create_Some(_280_result);
      return maybeParts;
      return maybeParts;
    }
    public static Dafny.ISequence<Dafny.ISequence<byte>> PartitionCodeUnitSequence(Dafny.ISequence<byte> s) {
      return (Utf8EncodingForm_Compile.__default.PartitionCodeUnitSequenceChecked(s)).Extract();
    }
    public static bool IsWellFormedCodeUnitSequence(Dafny.ISequence<byte> s) {
      return (Utf8EncodingForm_Compile.__default.PartitionCodeUnitSequenceChecked(s)).is_Some;
    }
    public static Dafny.ISequence<byte> EncodeScalarSequence(Dafny.ISequence<uint> vs)
    {
      Dafny.ISequence<byte> s = Utf8EncodingForm_Compile.WellFormedCodeUnitSeq.Default();
      s = Dafny.Sequence<byte>.FromElements();
      BigInteger _lo1 = BigInteger.Zero;
      for (BigInteger _284_i = new BigInteger((vs).Count); _lo1 < _284_i; ) {
        _284_i--;
        Dafny.ISequence<byte> _285_next;
        _285_next = Utf8EncodingForm_Compile.__default.EncodeScalarValue((vs).Select(_284_i));
        s = Dafny.Sequence<byte>.Concat(_285_next, s);
      }
      return s;
    }
    public static Dafny.ISequence<uint> DecodeCodeUnitSequence(Dafny.ISequence<byte> s) {
      Dafny.ISequence<Dafny.ISequence<byte>> _286_parts = Utf8EncodingForm_Compile.__default.PartitionCodeUnitSequence(s);
      Dafny.ISequence<uint> _287_vs = Seq_Compile.__default.Map<Dafny.ISequence<byte>, uint>(Utf8EncodingForm_Compile.__default.DecodeMinimalWellFormedCodeUnitSubsequence, _286_parts);
      return _287_vs;
    }
    public static Wrappers_Compile._IOption<Dafny.ISequence<uint>> DecodeCodeUnitSequenceChecked(Dafny.ISequence<byte> s)
    {
      Wrappers_Compile._IOption<Dafny.ISequence<uint>> maybeVs = Wrappers_Compile.Option<Dafny.ISequence<uint>>.Default();
      Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<byte>>> _288_maybeParts;
      _288_maybeParts = Utf8EncodingForm_Compile.__default.PartitionCodeUnitSequenceChecked(s);
      if ((_288_maybeParts).is_None) {
        maybeVs = Wrappers_Compile.Option<Dafny.ISequence<uint>>.create_None();
        return maybeVs;
      }
      Dafny.ISequence<Dafny.ISequence<byte>> _289_parts;
      _289_parts = (_288_maybeParts).dtor_value;
      Dafny.ISequence<uint> _290_vs;
      _290_vs = Seq_Compile.__default.Map<Dafny.ISequence<byte>, uint>(Utf8EncodingForm_Compile.__default.DecodeMinimalWellFormedCodeUnitSubsequence, _289_parts);
      maybeVs = Wrappers_Compile.Option<Dafny.ISequence<uint>>.create_Some(_290_vs);
      return maybeVs;
      return maybeVs;
    }
  }

  public partial class WellFormedCodeUnitSeq {
    private static readonly Dafny.ISequence<byte> Witness = Dafny.Sequence<byte>.FromElements();
    public static Dafny.ISequence<byte> Default() {
      return Witness;
    }
    private static readonly Dafny.TypeDescriptor<Dafny.ISequence<byte>> _TYPE = new Dafny.TypeDescriptor<Dafny.ISequence<byte>>(Utf8EncodingForm_Compile.WellFormedCodeUnitSeq.Default());
    public static Dafny.TypeDescriptor<Dafny.ISequence<byte>> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class MinimalWellFormedCodeUnitSeq {
    private static readonly Dafny.TypeDescriptor<Dafny.ISequence<byte>> _TYPE = new Dafny.TypeDescriptor<Dafny.ISequence<byte>>(Dafny.Sequence<byte>.Empty);
    public static Dafny.TypeDescriptor<Dafny.ISequence<byte>> _TypeDescriptor() {
      return _TYPE;
    }
  }
} // end of namespace Utf8EncodingForm_Compile
namespace Utf16EncodingForm_Compile {

  public partial class __default {
    public static bool IsMinimalWellFormedCodeUnitSubsequence(Dafny.ISequence<ushort> s) {
      if ((new BigInteger((s).Count)) == (BigInteger.One)) {
        return Utf16EncodingForm_Compile.__default.IsWellFormedSingleCodeUnitSequence(s);
      } else if ((new BigInteger((s).Count)) == (new BigInteger(2))) {
        bool _291_b = Utf16EncodingForm_Compile.__default.IsWellFormedDoubleCodeUnitSequence(s);
        return _291_b;
      } else {
        return false;
      }
    }
    public static bool IsWellFormedSingleCodeUnitSequence(Dafny.ISequence<ushort> s) {
      ushort _292_firstWord = (s).Select(BigInteger.Zero);
      return ((((ushort)(0)) <= (_292_firstWord)) && ((_292_firstWord) <= ((ushort)(55295)))) || ((((ushort)(57344)) <= (_292_firstWord)) && ((_292_firstWord) <= ((ushort)(65535))));
    }
    public static bool IsWellFormedDoubleCodeUnitSequence(Dafny.ISequence<ushort> s) {
      ushort _293_firstWord = (s).Select(BigInteger.Zero);
      ushort _294_secondWord = (s).Select(BigInteger.One);
      return ((((ushort)(55296)) <= (_293_firstWord)) && ((_293_firstWord) <= ((ushort)(56319)))) && ((((ushort)(56320)) <= (_294_secondWord)) && ((_294_secondWord) <= ((ushort)(57343))));
    }
    public static Wrappers_Compile._IOption<Dafny.ISequence<ushort>> SplitPrefixMinimalWellFormedCodeUnitSubsequence(Dafny.ISequence<ushort> s) {
      if (((new BigInteger((s).Count)) >= (BigInteger.One)) && (Utf16EncodingForm_Compile.__default.IsWellFormedSingleCodeUnitSequence((s).Take(BigInteger.One)))) {
        return Wrappers_Compile.Option<Dafny.ISequence<ushort>>.create_Some((s).Take(BigInteger.One));
      } else if (((new BigInteger((s).Count)) >= (new BigInteger(2))) && (Utf16EncodingForm_Compile.__default.IsWellFormedDoubleCodeUnitSequence((s).Take(new BigInteger(2))))) {
        return Wrappers_Compile.Option<Dafny.ISequence<ushort>>.create_Some((s).Take(new BigInteger(2)));
      } else {
        return Wrappers_Compile.Option<Dafny.ISequence<ushort>>.create_None();
      }
    }
    public static Dafny.ISequence<ushort> EncodeScalarValue(uint v) {
      if ((((0U) <= (v)) && ((v) <= (55295U))) || (((57344U) <= (v)) && ((v) <= (65535U)))) {
        return Utf16EncodingForm_Compile.__default.EncodeScalarValueSingleWord(v);
      } else {
        return Utf16EncodingForm_Compile.__default.EncodeScalarValueDoubleWord(v);
      }
    }
    public static Dafny.ISequence<ushort> EncodeScalarValueSingleWord(uint v) {
      ushort _295_firstWord = (ushort)(v);
      return Dafny.Sequence<ushort>.FromElements(_295_firstWord);
    }
    public static Dafny.ISequence<ushort> EncodeScalarValueDoubleWord(uint v) {
      ushort _296_x2 = (ushort)((v) & (1023U));
      byte _297_x1 = (byte)(((v) & (64512U)) >> ((int)((byte)(10))));
      byte _298_u = (byte)(((v) & (2031616U)) >> ((int)((byte)(16))));
      byte _299_w = (byte)(unchecked((byte)(((byte)((_298_u) - ((byte)(1)))) & (byte)0x1F)));
      ushort _300_firstWord = (ushort)(((ushort)(((ushort)(55296)) | (unchecked((ushort)(((ushort)(((ushort)(_299_w)) << ((int)((byte)(6)))))))))) | ((ushort)(_297_x1)));
      ushort _301_secondWord = (ushort)(((ushort)(56320)) | ((ushort)(_296_x2)));
      return Dafny.Sequence<ushort>.FromElements(_300_firstWord, _301_secondWord);
    }
    public static uint DecodeMinimalWellFormedCodeUnitSubsequence(Dafny.ISequence<ushort> m) {
      if ((new BigInteger((m).Count)) == (BigInteger.One)) {
        return Utf16EncodingForm_Compile.__default.DecodeMinimalWellFormedCodeUnitSubsequenceSingleWord(m);
      } else {
        return Utf16EncodingForm_Compile.__default.DecodeMinimalWellFormedCodeUnitSubsequenceDoubleWord(m);
      }
    }
    public static uint DecodeMinimalWellFormedCodeUnitSubsequenceSingleWord(Dafny.ISequence<ushort> m) {
      ushort _302_firstWord = (m).Select(BigInteger.Zero);
      ushort _303_x = (ushort)(_302_firstWord);
      return (uint)(_303_x);
    }
    public static uint DecodeMinimalWellFormedCodeUnitSubsequenceDoubleWord(Dafny.ISequence<ushort> m) {
      ushort _304_firstWord = (m).Select(BigInteger.Zero);
      ushort _305_secondWord = (m).Select(BigInteger.One);
      uint _306_x2 = (uint)((ushort)((_305_secondWord) & ((ushort)(1023))));
      uint _307_x1 = (uint)((ushort)((_304_firstWord) & ((ushort)(63))));
      uint _308_w = (uint)((ushort)(((ushort)((_304_firstWord) & ((ushort)(960)))) >> ((int)((byte)(6)))));
      uint _309_u = (uint)(unchecked((uint)(((_308_w) + (1U)) & (uint)0xFFFFFFU)));
      uint _310_v = ((unchecked((uint)(((_309_u) << ((int)((byte)(16)))) & (uint)0xFFFFFFU))) | (unchecked((uint)(((_307_x1) << ((int)((byte)(10)))) & (uint)0xFFFFFFU)))) | ((uint)(_306_x2));
      return _310_v;
    }
    public static Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<ushort>>> PartitionCodeUnitSequenceChecked(Dafny.ISequence<ushort> s)
    {
      Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<ushort>>> maybeParts = Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<ushort>>>.Default();
      if ((s).Equals(Dafny.Sequence<ushort>.FromElements())) {
        maybeParts = Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<ushort>>>.create_Some(Dafny.Sequence<Dafny.ISequence<ushort>>.FromElements());
        return maybeParts;
      }
      Dafny.ISequence<Dafny.ISequence<ushort>> _311_result;
      _311_result = Dafny.Sequence<Dafny.ISequence<ushort>>.FromElements();
      Dafny.ISequence<ushort> _312_rest;
      _312_rest = s;
      while ((new BigInteger((_312_rest).Count)).Sign == 1) {
        Dafny.ISequence<ushort> _313_prefix;
        Wrappers_Compile._IOption<Dafny.ISequence<ushort>> _314_valueOrError0 = Wrappers_Compile.Option<Dafny.ISequence<ushort>>.Default();
        _314_valueOrError0 = Utf16EncodingForm_Compile.__default.SplitPrefixMinimalWellFormedCodeUnitSubsequence(_312_rest);
        if ((_314_valueOrError0).IsFailure()) {
          maybeParts = (_314_valueOrError0).PropagateFailure<Dafny.ISequence<Dafny.ISequence<ushort>>>();
          return maybeParts;
        }
        _313_prefix = (_314_valueOrError0).Extract();
        _311_result = Dafny.Sequence<Dafny.ISequence<ushort>>.Concat(_311_result, Dafny.Sequence<Dafny.ISequence<ushort>>.FromElements(_313_prefix));
        _312_rest = (_312_rest).Drop(new BigInteger((_313_prefix).Count));
      }
      maybeParts = Wrappers_Compile.Option<Dafny.ISequence<Dafny.ISequence<ushort>>>.create_Some(_311_result);
      return maybeParts;
      return maybeParts;
    }
    public static Dafny.ISequence<Dafny.ISequence<ushort>> PartitionCodeUnitSequence(Dafny.ISequence<ushort> s) {
      return (Utf16EncodingForm_Compile.__default.PartitionCodeUnitSequenceChecked(s)).Extract();
    }
    public static bool IsWellFormedCodeUnitSequence(Dafny.ISequence<ushort> s) {
      return (Utf16EncodingForm_Compile.__default.PartitionCodeUnitSequenceChecked(s)).is_Some;
    }
    public static Dafny.ISequence<ushort> EncodeScalarSequence(Dafny.ISequence<uint> vs)
    {
      Dafny.ISequence<ushort> s = Utf16EncodingForm_Compile.WellFormedCodeUnitSeq.Default();
      s = Dafny.Sequence<ushort>.FromElements();
      BigInteger _lo2 = BigInteger.Zero;
      for (BigInteger _315_i = new BigInteger((vs).Count); _lo2 < _315_i; ) {
        _315_i--;
        Dafny.ISequence<ushort> _316_next;
        _316_next = Utf16EncodingForm_Compile.__default.EncodeScalarValue((vs).Select(_315_i));
        s = Dafny.Sequence<ushort>.Concat(_316_next, s);
      }
      return s;
    }
    public static Dafny.ISequence<uint> DecodeCodeUnitSequence(Dafny.ISequence<ushort> s) {
      Dafny.ISequence<Dafny.ISequence<ushort>> _317_parts = Utf16EncodingForm_Compile.__default.PartitionCodeUnitSequence(s);
      Dafny.ISequence<uint> _318_vs = Seq_Compile.__default.Map<Dafny.ISequence<ushort>, uint>(Utf16EncodingForm_Compile.__default.DecodeMinimalWellFormedCodeUnitSubsequence, _317_parts);
      return _318_vs;
    }
    public static Wrappers_Compile._IOption<Dafny.ISequence<uint>> DecodeCodeUnitSequenceChecked(Dafny.ISequence<ushort> s)
    {
      Wrappers_Compile._IOption<Dafny.ISequence<uint>> maybeVs = Wrappers_Compile.Option<Dafny.ISequence<uint>>.Default();
      Wrappers_Compile._IOption<Dafny.ISequence<Dafny.ISequence<ushort>>> _319_maybeParts;
      _319_maybeParts = Utf16EncodingForm_Compile.__default.PartitionCodeUnitSequenceChecked(s);
      if ((_319_maybeParts).is_None) {
        maybeVs = Wrappers_Compile.Option<Dafny.ISequence<uint>>.create_None();
        return maybeVs;
      }
      Dafny.ISequence<Dafny.ISequence<ushort>> _320_parts;
      _320_parts = (_319_maybeParts).dtor_value;
      Dafny.ISequence<uint> _321_vs;
      _321_vs = Seq_Compile.__default.Map<Dafny.ISequence<ushort>, uint>(Utf16EncodingForm_Compile.__default.DecodeMinimalWellFormedCodeUnitSubsequence, _320_parts);
      maybeVs = Wrappers_Compile.Option<Dafny.ISequence<uint>>.create_Some(_321_vs);
      return maybeVs;
      return maybeVs;
    }
  }

  public partial class WellFormedCodeUnitSeq {
    private static readonly Dafny.ISequence<ushort> Witness = Dafny.Sequence<ushort>.FromElements();
    public static Dafny.ISequence<ushort> Default() {
      return Witness;
    }
    private static readonly Dafny.TypeDescriptor<Dafny.ISequence<ushort>> _TYPE = new Dafny.TypeDescriptor<Dafny.ISequence<ushort>>(Utf16EncodingForm_Compile.WellFormedCodeUnitSeq.Default());
    public static Dafny.TypeDescriptor<Dafny.ISequence<ushort>> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class MinimalWellFormedCodeUnitSeq {
    private static readonly Dafny.TypeDescriptor<Dafny.ISequence<ushort>> _TYPE = new Dafny.TypeDescriptor<Dafny.ISequence<ushort>>(Dafny.Sequence<ushort>.Empty);
    public static Dafny.TypeDescriptor<Dafny.ISequence<ushort>> _TypeDescriptor() {
      return _TYPE;
    }
  }
} // end of namespace Utf16EncodingForm_Compile
namespace UnicodeStrings_Compile {

  public partial class __default {
    public static bool IsWellFormedString(Dafny.ISequence<char> s) {
      return Utf16EncodingForm_Compile.__default.IsWellFormedCodeUnitSequence(Seq_Compile.__default.Map<char, ushort>(((System.Func<char, ushort>)((_322_c) => {
        return (ushort)(_322_c);
      })), s));
    }
    public static Wrappers_Compile._IOption<Dafny.ISequence<byte>> ToUTF8Checked(Dafny.ISequence<char> s) {
      Dafny.ISequence<ushort> _323_asCodeUnits = Seq_Compile.__default.Map<char, ushort>(((System.Func<char, ushort>)((_324_c) => {
        return (ushort)(_324_c);
      })), s);
      Wrappers_Compile._IOption<Dafny.ISequence<uint>> _325_valueOrError0 = Utf16EncodingForm_Compile.__default.DecodeCodeUnitSequenceChecked(_323_asCodeUnits);
      if ((_325_valueOrError0).IsFailure()) {
        return (_325_valueOrError0).PropagateFailure<Dafny.ISequence<byte>>();
      } else {
        Dafny.ISequence<uint> _326_utf32 = (_325_valueOrError0).Extract();
        Dafny.ISequence<byte> _327_asUtf8CodeUnits = Utf8EncodingForm_Compile.__default.EncodeScalarSequence(_326_utf32);
        return Wrappers_Compile.Option<Dafny.ISequence<byte>>.create_Some(Seq_Compile.__default.Map<byte, byte>(((System.Func<byte, byte>)((_328_c) => {
  return (byte)(_328_c);
})), _327_asUtf8CodeUnits));
      }
    }
    public static Wrappers_Compile._IOption<Dafny.ISequence<char>> FromUTF8Checked(Dafny.ISequence<byte> bs) {
      Dafny.ISequence<byte> _329_asCodeUnits = Seq_Compile.__default.Map<byte, byte>(((System.Func<byte, byte>)((_330_c) => {
        return (byte)(_330_c);
      })), bs);
      Wrappers_Compile._IOption<Dafny.ISequence<uint>> _331_valueOrError0 = Utf8EncodingForm_Compile.__default.DecodeCodeUnitSequenceChecked(_329_asCodeUnits);
      if ((_331_valueOrError0).IsFailure()) {
        return (_331_valueOrError0).PropagateFailure<Dafny.ISequence<char>>();
      } else {
        Dafny.ISequence<uint> _332_utf32 = (_331_valueOrError0).Extract();
        Dafny.ISequence<ushort> _333_asUtf16CodeUnits = Utf16EncodingForm_Compile.__default.EncodeScalarSequence(_332_utf32);
        return Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(Seq_Compile.__default.Map<ushort, char>(((System.Func<ushort, char>)((_334_cu) => {
  return (char)(_334_cu);
})), _333_asUtf16CodeUnits));
      }
    }
    public static Wrappers_Compile._IOption<Dafny.ISequence<ushort>> ToUTF16Checked(Dafny.ISequence<char> s) {
      if (Utf16EncodingForm_Compile.__default.IsWellFormedCodeUnitSequence(Seq_Compile.__default.Map<char, ushort>(((System.Func<char, ushort>)((_335_c) => {
        return (ushort)(_335_c);
      })), s))) {
        return Wrappers_Compile.Option<Dafny.ISequence<ushort>>.create_Some(Seq_Compile.__default.Map<char, ushort>(((System.Func<char, ushort>)((_336_c) => {
  return (ushort)(_336_c);
})), s));
      } else {
        return Wrappers_Compile.Option<Dafny.ISequence<ushort>>.create_None();
      }
    }
    public static Wrappers_Compile._IOption<Dafny.ISequence<char>> FromUTF16Checked(Dafny.ISequence<ushort> bs) {
      if (Utf16EncodingForm_Compile.__default.IsWellFormedCodeUnitSequence(Seq_Compile.__default.Map<ushort, ushort>(((System.Func<ushort, ushort>)((_337_c) => {
        return (ushort)(_337_c);
      })), bs))) {
        return Wrappers_Compile.Option<Dafny.ISequence<char>>.create_Some(Seq_Compile.__default.Map<ushort, char>(((System.Func<ushort, char>)((_338_c) => {
  return (char)(_338_c);
})), bs));
      } else {
        return Wrappers_Compile.Option<Dafny.ISequence<char>>.create_None();
      }
    }
    public static Dafny.ISequence<byte> ASCIIToUTF8(Dafny.ISequence<char> s) {
      return Seq_Compile.__default.Map<char, byte>(((System.Func<char, byte>)((_339_c) => {
        return (byte)(_339_c);
      })), s);
    }
    public static Dafny.ISequence<ushort> ASCIIToUTF16(Dafny.ISequence<char> s) {
      return Seq_Compile.__default.Map<char, ushort>(((System.Func<char, ushort>)((_340_c) => {
        return (ushort)(_340_c);
      })), s);
    }
  }
} // end of namespace UnicodeStrings_Compile
namespace JSON_mUtils_mVectors_Compile {

  public interface _IVectorError {
    bool is_OutOfMemory { get; }
    _IVectorError DowncastClone();
  }
  public class VectorError : _IVectorError {
    public VectorError() {
    }
    public _IVectorError DowncastClone() {
      if (this is _IVectorError dt) { return dt; }
      return new VectorError();
    }
    public override bool Equals(object other) {
      var oth = other as JSON_mUtils_mVectors_Compile.VectorError;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "JSON_mUtils_mVectors_Compile.VectorError.OutOfMemory";
      return s;
    }
    private static readonly JSON_mUtils_mVectors_Compile._IVectorError theDefault = create();
    public static JSON_mUtils_mVectors_Compile._IVectorError Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<JSON_mUtils_mVectors_Compile._IVectorError> _TYPE = new Dafny.TypeDescriptor<JSON_mUtils_mVectors_Compile._IVectorError>(JSON_mUtils_mVectors_Compile.VectorError.Default());
    public static Dafny.TypeDescriptor<JSON_mUtils_mVectors_Compile._IVectorError> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IVectorError create() {
      return new VectorError();
    }
    public static _IVectorError create_OutOfMemory() {
      return create();
    }
    public bool is_OutOfMemory { get { return true; } }
    public static System.Collections.Generic.IEnumerable<_IVectorError> AllSingletonConstructors {
      get {
        yield return VectorError.create();
      }
    }
  }

  public partial class Vector<A> {
    public Vector() {
      this.size = 0;
      this.capacity = 0;
      this.data = new A[0];
      this._a = default(A);
    }
    public uint size {get; set;}
    public uint capacity {get; set;}
    public A[] data {get; set;}
    public void __ctor(A a0, uint initial__capacity)
    {
      (this)._a = a0;
      (this).size = 0U;
      (this).capacity = initial__capacity;
      Func<BigInteger, A> _init2 = Dafny.Helpers.Id<Func<A, Func<BigInteger, A>>>((_341_a0) => ((System.Func<BigInteger, A>)((_342___v0) => {
        return _341_a0;
      })))(a0);
      A[] _nw4 = new A[Dafny.Helpers.ToIntChecked(initial__capacity, "array size exceeds memory limit")];
      for (var _i0_2 = 0; _i0_2 < new BigInteger(_nw4.Length); _i0_2++) {
        _nw4[(int)(_i0_2)] = _init2(_i0_2);
      }
      (this).data = _nw4;
    }
    public A At(uint idx) {
      return (this.data)[(int)(idx)];
    }
    public A Top() {
      return (this.data)[(int)((this.size) - (1U))];
    }
    public void Put(uint idx, A a)
    {
      var _arr0 = this.data;
      _arr0[(int)((idx))] = a;
    }
    public void CopyFrom(A[] new__data, uint count)
    {
      uint _hi7 = count;
      for (uint _343_idx = 0U; _343_idx < _hi7; _343_idx++) {
        var _arr1 = this.data;
        _arr1[(int)((_343_idx))] = (new__data)[(int)(_343_idx)];
      }
    }
    public void Realloc(uint new__capacity)
    {
      A[] _344_old__data;
      uint _345_old__capacity;
      A[] _rhs6 = this.data;
      uint _rhs7 = this.capacity;
      _344_old__data = _rhs6;
      _345_old__capacity = _rhs7;
      Func<BigInteger, A> _init3 = ((System.Func<BigInteger, A>)((_346___v1) => {
        return (this).a;
      }));
      A[] _nw5 = new A[Dafny.Helpers.ToIntChecked(new__capacity, "array size exceeds memory limit")];
      for (var _i0_3 = 0; _i0_3 < new BigInteger(_nw5.Length); _i0_3++) {
        _nw5[(int)(_i0_3)] = _init3(_i0_3);
      }
      A[] _rhs8 = _nw5;
      uint _rhs9 = new__capacity;
      JSON_mUtils_mVectors_Compile.Vector<A> _lhs4 = this;
      JSON_mUtils_mVectors_Compile.Vector<A> _lhs5 = this;
      _lhs4.data = _rhs8;
      _lhs5.capacity = _rhs9;
      (this).CopyFrom(_344_old__data, _345_old__capacity);
    }
    public uint DefaultNewCapacity(uint capacity) {
      if ((capacity) < ((this).MAX__CAPACITY__BEFORE__DOUBLING)) {
        return (2U) * (capacity);
      } else {
        return (this).MAX__CAPACITY;
      }
    }
    public Wrappers_Compile._IOutcome<JSON_mUtils_mVectors_Compile._IVectorError> ReallocDefault()
    {
      Wrappers_Compile._IOutcome<JSON_mUtils_mVectors_Compile._IVectorError> o = Wrappers_Compile.Outcome<JSON_mUtils_mVectors_Compile._IVectorError>.Default();
      if ((this.capacity) == ((this).MAX__CAPACITY)) {
        o = Wrappers_Compile.Outcome<JSON_mUtils_mVectors_Compile._IVectorError>.create_Fail(JSON_mUtils_mVectors_Compile.VectorError.create());
        return o;
      }
      (this).Realloc((this).DefaultNewCapacity(this.capacity));
      o = Wrappers_Compile.Outcome<JSON_mUtils_mVectors_Compile._IVectorError>.create_Pass();
      return o;
      return o;
    }
    public Wrappers_Compile._IOutcome<JSON_mUtils_mVectors_Compile._IVectorError> Ensure(uint reserved)
    {
      Wrappers_Compile._IOutcome<JSON_mUtils_mVectors_Compile._IVectorError> o = Wrappers_Compile.Outcome<JSON_mUtils_mVectors_Compile._IVectorError>.Default();
      if ((reserved) > (((this).MAX__CAPACITY) - (this.size))) {
        o = Wrappers_Compile.Outcome<JSON_mUtils_mVectors_Compile._IVectorError>.create_Fail(JSON_mUtils_mVectors_Compile.VectorError.create());
        return o;
      }
      if ((reserved) <= ((this.capacity) - (this.size))) {
        o = Wrappers_Compile.Outcome<JSON_mUtils_mVectors_Compile._IVectorError>.create_Pass();
        return o;
      }
      uint _347_new__capacity;
      _347_new__capacity = this.capacity;
      while ((reserved) > ((_347_new__capacity) - (this.size))) {
        _347_new__capacity = (this).DefaultNewCapacity(_347_new__capacity);
      }
      (this).Realloc(_347_new__capacity);
      o = Wrappers_Compile.Outcome<JSON_mUtils_mVectors_Compile._IVectorError>.create_Pass();
      return o;
      return o;
    }
    public void PopFast()
    {
      (this).size = (this.size) - (1U);
    }
    public void PushFast(A a)
    {
      var _arr2 = this.data;
      var _index0 = this.size;
      _arr2[(int)(_index0)] = a;
      (this).size = (this.size) + (1U);
    }
    public Wrappers_Compile._IOutcome<JSON_mUtils_mVectors_Compile._IVectorError> Push(A a)
    {
      Wrappers_Compile._IOutcome<JSON_mUtils_mVectors_Compile._IVectorError> o = Wrappers_Compile.Outcome<JSON_mUtils_mVectors_Compile._IVectorError>.Default();
      if ((this.size) == (this.capacity)) {
        Wrappers_Compile._IOutcome<JSON_mUtils_mVectors_Compile._IVectorError> _348_d;
        Wrappers_Compile._IOutcome<JSON_mUtils_mVectors_Compile._IVectorError> _out23;
        _out23 = (this).ReallocDefault();
        _348_d = _out23;
        if ((_348_d).is_Fail) {
          o = _348_d;
          return o;
        }
      }
      (this).PushFast(a);
      o = Wrappers_Compile.Outcome<JSON_mUtils_mVectors_Compile._IVectorError>.create_Pass();
      return o;
      return o;
    }
    public A _a {get; set;}
    public A a { get {
      return this._a;
    } }
    public uint MAX__CAPACITY__BEFORE__DOUBLING { get {
      return (BoundedInts_Compile.__default.UINT32__MAX) / (2U);
    } }
    public uint MAX__CAPACITY { get {
      return BoundedInts_Compile.__default.UINT32__MAX;
    } }
  }

  public partial class __default {
    public static Wrappers_Compile._IOutcome<JSON_mUtils_mVectors_Compile._IVectorError> OOM__FAILURE { get {
      return Wrappers_Compile.Outcome<JSON_mUtils_mVectors_Compile._IVectorError>.create_Fail(JSON_mUtils_mVectors_Compile.VectorError.create());
    } }
  }
} // end of namespace JSON_mUtils_mVectors_Compile
namespace JSON_mUtils_mStr_mCharStrConversion_Compile {

  public partial class __default {
    public static Dafny.ISequence<BigInteger> Digits(BigInteger n, BigInteger @base)
    {
      if ((n).Sign == 0) {
        return Dafny.Sequence<BigInteger>.FromElements();
      } else {
        Dafny.ISequence<BigInteger> _349_digits_k = JSON_mUtils_mStr_mCharStrConversion_Compile.__default.Digits(Dafny.Helpers.EuclideanDivision(n, @base), @base);
        Dafny.ISequence<BigInteger> _350_digits = Dafny.Sequence<BigInteger>.Concat(_349_digits_k, Dafny.Sequence<BigInteger>.FromElements(Dafny.Helpers.EuclideanModulus(n, @base)));
        return _350_digits;
      }
    }
    public static Dafny.ISequence<char> OfDigits(Dafny.ISequence<BigInteger> digits, Dafny.ISequence<char> chars)
    {
      Dafny.ISequence<char> _351___accumulator = Dafny.Sequence<char>.FromElements();
    TAIL_CALL_START: ;
      if ((digits).Equals(Dafny.Sequence<BigInteger>.FromElements())) {
        return Dafny.Sequence<char>.Concat(_351___accumulator, Dafny.Sequence<char>.FromElements());
      } else {
        _351___accumulator = Dafny.Sequence<char>.Concat(_351___accumulator, Dafny.Sequence<char>.FromElements((chars).Select((digits).Select(BigInteger.Zero))));
        Dafny.ISequence<BigInteger> _in81 = (digits).Drop(BigInteger.One);
        Dafny.ISequence<char> _in82 = chars;
        digits = _in81;
        chars = _in82;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<char> OfNat__any(BigInteger n, Dafny.ISequence<char> chars)
    {
      BigInteger _352_base = new BigInteger((chars).Count);
      if ((n).Sign == 0) {
        return Dafny.Sequence<char>.FromElements((chars).Select(BigInteger.Zero));
      } else {
        return JSON_mUtils_mStr_mCharStrConversion_Compile.__default.OfDigits(JSON_mUtils_mStr_mCharStrConversion_Compile.__default.Digits(n, _352_base), chars);
      }
    }
    public static bool NumberStr(Dafny.ISequence<char> str, char minus, Func<char, bool> is__digit)
    {
      return !(!(str).Equals(Dafny.Sequence<char>.FromElements())) || (((((str).Select(BigInteger.Zero)) == (minus)) || (Dafny.Helpers.Id<Func<char, bool>>(is__digit)((str).Select(BigInteger.Zero)))) && (Dafny.Helpers.Id<Func<Dafny.ISequence<char>, Func<char, bool>, bool>>((_353_str, _354_is__digit) => Dafny.Helpers.Quantifier<char>(((_353_str).Drop(BigInteger.One)).UniqueElements, true, (((_forall_var_6) => {
        char _355_c = (char)_forall_var_6;
        return !(((_353_str).Drop(BigInteger.One)).Contains(_355_c)) || (Dafny.Helpers.Id<Func<char, bool>>(_354_is__digit)(_355_c));
      }))))(str, is__digit)));
    }
    public static Dafny.ISequence<char> OfInt__any(BigInteger n, Dafny.ISequence<char> chars, char minus)
    {
      if ((n).Sign != -1) {
        return JSON_mUtils_mStr_mCharStrConversion_Compile.__default.OfNat__any(n, chars);
      } else {
        return Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.FromElements(minus), JSON_mUtils_mStr_mCharStrConversion_Compile.__default.OfNat__any((BigInteger.Zero) - (n), chars));
      }
    }
    public static BigInteger ToNat__any(Dafny.ISequence<char> str, BigInteger @base, Dafny.IMap<char,BigInteger> digits)
    {
      if ((str).Equals(Dafny.Sequence<char>.FromElements())) {
        return BigInteger.Zero;
      } else {
        return ((JSON_mUtils_mStr_mCharStrConversion_Compile.__default.ToNat__any((str).Take((new BigInteger((str).Count)) - (BigInteger.One)), @base, digits)) * (@base)) + (Dafny.Map<char, BigInteger>.Select(digits,(str).Select((new BigInteger((str).Count)) - (BigInteger.One))));
      }
    }
    public static BigInteger ToInt__any(Dafny.ISequence<char> str, char minus, BigInteger @base, Dafny.IMap<char,BigInteger> digits)
    {
      if (Dafny.Sequence<char>.IsPrefixOf(Dafny.Sequence<char>.FromElements(minus), str)) {
        return (BigInteger.Zero) - (JSON_mUtils_mStr_mCharStrConversion_Compile.__default.ToNat__any((str).Drop(BigInteger.One), @base, digits));
      } else {
        return JSON_mUtils_mStr_mCharStrConversion_Compile.__default.ToNat__any(str, @base, digits);
      }
    }
  }
} // end of namespace JSON_mUtils_mStr_mCharStrConversion_Compile
namespace JSON_mUtils_mStr_mCharStrEscaping_Compile {

  public partial class __default {
    public static Dafny.ISequence<char> Escape(Dafny.ISequence<char> str, Dafny.ISet<char> special, char escape)
    {
      Dafny.ISequence<char> _356___accumulator = Dafny.Sequence<char>.FromElements();
    TAIL_CALL_START: ;
      if ((str).Equals(Dafny.Sequence<char>.FromElements())) {
        return Dafny.Sequence<char>.Concat(_356___accumulator, str);
      } else if ((special).Contains((str).Select(BigInteger.Zero))) {
        _356___accumulator = Dafny.Sequence<char>.Concat(_356___accumulator, Dafny.Sequence<char>.FromElements(escape, (str).Select(BigInteger.Zero)));
        Dafny.ISequence<char> _in83 = (str).Drop(BigInteger.One);
        Dafny.ISet<char> _in84 = special;
        char _in85 = escape;
        str = _in83;
        special = _in84;
        escape = _in85;
        goto TAIL_CALL_START;
      } else {
        _356___accumulator = Dafny.Sequence<char>.Concat(_356___accumulator, Dafny.Sequence<char>.FromElements((str).Select(BigInteger.Zero)));
        Dafny.ISequence<char> _in86 = (str).Drop(BigInteger.One);
        Dafny.ISet<char> _in87 = special;
        char _in88 = escape;
        str = _in86;
        special = _in87;
        escape = _in88;
        goto TAIL_CALL_START;
      }
    }
    public static Wrappers_Compile._IResult<Dafny.ISequence<char>, JSON_mUtils_mStr_mCharStrEscaping_Compile._IUnescapeError> Unescape(Dafny.ISequence<char> str, char escape)
    {
      if ((str).Equals(Dafny.Sequence<char>.FromElements())) {
        return Wrappers_Compile.Result<Dafny.ISequence<char>, JSON_mUtils_mStr_mCharStrEscaping_Compile._IUnescapeError>.create_Success(str);
      } else if (((str).Select(BigInteger.Zero)) == (escape)) {
        if ((new BigInteger((str).Count)) > (BigInteger.One)) {
          Wrappers_Compile._IResult<Dafny.ISequence<char>, JSON_mUtils_mStr_mCharStrEscaping_Compile._IUnescapeError> _357_valueOrError0 = JSON_mUtils_mStr_mCharStrEscaping_Compile.__default.Unescape((str).Drop(new BigInteger(2)), escape);
          if ((_357_valueOrError0).IsFailure()) {
            return (_357_valueOrError0).PropagateFailure<Dafny.ISequence<char>>();
          } else {
            Dafny.ISequence<char> _358_tl = (_357_valueOrError0).Extract();
            return Wrappers_Compile.Result<Dafny.ISequence<char>, JSON_mUtils_mStr_mCharStrEscaping_Compile._IUnescapeError>.create_Success(Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.FromElements((str).Select(BigInteger.One)), _358_tl));
          }
        } else {
          return Wrappers_Compile.Result<Dafny.ISequence<char>, JSON_mUtils_mStr_mCharStrEscaping_Compile._IUnescapeError>.create_Failure(JSON_mUtils_mStr_mCharStrEscaping_Compile.UnescapeError.create());
        }
      } else {
        Wrappers_Compile._IResult<Dafny.ISequence<char>, JSON_mUtils_mStr_mCharStrEscaping_Compile._IUnescapeError> _359_valueOrError1 = JSON_mUtils_mStr_mCharStrEscaping_Compile.__default.Unescape((str).Drop(BigInteger.One), escape);
        if ((_359_valueOrError1).IsFailure()) {
          return (_359_valueOrError1).PropagateFailure<Dafny.ISequence<char>>();
        } else {
          Dafny.ISequence<char> _360_tl = (_359_valueOrError1).Extract();
          return Wrappers_Compile.Result<Dafny.ISequence<char>, JSON_mUtils_mStr_mCharStrEscaping_Compile._IUnescapeError>.create_Success(Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.FromElements((str).Select(BigInteger.Zero)), _360_tl));
        }
      }
    }
  }

  public interface _IUnescapeError {
    bool is_EscapeAtEOS { get; }
    _IUnescapeError DowncastClone();
  }
  public class UnescapeError : _IUnescapeError {
    public UnescapeError() {
    }
    public _IUnescapeError DowncastClone() {
      if (this is _IUnescapeError dt) { return dt; }
      return new UnescapeError();
    }
    public override bool Equals(object other) {
      var oth = other as JSON_mUtils_mStr_mCharStrEscaping_Compile.UnescapeError;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "JSON_mUtils_mStr_mCharStrEscaping_Compile.UnescapeError.EscapeAtEOS";
      return s;
    }
    private static readonly JSON_mUtils_mStr_mCharStrEscaping_Compile._IUnescapeError theDefault = create();
    public static JSON_mUtils_mStr_mCharStrEscaping_Compile._IUnescapeError Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<JSON_mUtils_mStr_mCharStrEscaping_Compile._IUnescapeError> _TYPE = new Dafny.TypeDescriptor<JSON_mUtils_mStr_mCharStrEscaping_Compile._IUnescapeError>(JSON_mUtils_mStr_mCharStrEscaping_Compile.UnescapeError.Default());
    public static Dafny.TypeDescriptor<JSON_mUtils_mStr_mCharStrEscaping_Compile._IUnescapeError> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IUnescapeError create() {
      return new UnescapeError();
    }
    public static _IUnescapeError create_EscapeAtEOS() {
      return create();
    }
    public bool is_EscapeAtEOS { get { return true; } }
    public static System.Collections.Generic.IEnumerable<_IUnescapeError> AllSingletonConstructors {
      get {
        yield return UnescapeError.create();
      }
    }
  }
} // end of namespace JSON_mUtils_mStr_mCharStrEscaping_Compile
namespace JSON_mUtils_mStr_Compile {

  public partial class __default {
    public static Dafny.ISequence<char> OfNat(BigInteger n, BigInteger @base)
    {
      return JSON_mUtils_mStr_mCharStrConversion_Compile.__default.OfNat__any(n, (JSON_mUtils_mStr_Compile.__default.HEX__DIGITS).Take(@base));
    }
    public static Dafny.ISequence<char> OfInt(BigInteger n, BigInteger @base)
    {
      return JSON_mUtils_mStr_mCharStrConversion_Compile.__default.OfInt__any(n, (JSON_mUtils_mStr_Compile.__default.HEX__DIGITS).Take(@base), '-');
    }
    public static BigInteger ToNat(Dafny.ISequence<char> str, BigInteger @base)
    {
      return JSON_mUtils_mStr_mCharStrConversion_Compile.__default.ToNat__any(str, @base, JSON_mUtils_mStr_Compile.__default.HEX__TABLE);
    }
    public static BigInteger ToInt(Dafny.ISequence<char> str, BigInteger @base)
    {
      return JSON_mUtils_mStr_mCharStrConversion_Compile.__default.ToInt__any(str, '-', @base, JSON_mUtils_mStr_Compile.__default.HEX__TABLE);
    }
    public static Dafny.ISequence<char> EscapeQuotes(Dafny.ISequence<char> str) {
      return JSON_mUtils_mStr_mCharStrEscaping_Compile.__default.Escape(str, Dafny.Set<char>.FromElements('\"', '\''), '\\');
    }
    public static Wrappers_Compile._IResult<Dafny.ISequence<char>, JSON_mUtils_mStr_mCharStrEscaping_Compile._IUnescapeError> UnescapeQuotes(Dafny.ISequence<char> str) {
      return JSON_mUtils_mStr_mCharStrEscaping_Compile.__default.Unescape(str, '\\');
    }
    public static void Test()
    {
      if (!((JSON_mUtils_mStr_Compile.__default.OfInt(BigInteger.Zero, new BigInteger(10))).Equals(Dafny.Sequence<char>.FromString("0")))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-net/libraries/src/JSON/Utils/Str.dfy(229,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      if (!((JSON_mUtils_mStr_Compile.__default.OfInt(new BigInteger(3), new BigInteger(10))).Equals(Dafny.Sequence<char>.FromString("3")))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-net/libraries/src/JSON/Utils/Str.dfy(230,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      if (!((JSON_mUtils_mStr_Compile.__default.OfInt(new BigInteger(302), new BigInteger(10))).Equals(Dafny.Sequence<char>.FromString("302")))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-net/libraries/src/JSON/Utils/Str.dfy(231,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      if (!((JSON_mUtils_mStr_Compile.__default.OfInt(new BigInteger(-3), new BigInteger(10))).Equals(Dafny.Sequence<char>.FromString("-3")))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-net/libraries/src/JSON/Utils/Str.dfy(232,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
      if (!((JSON_mUtils_mStr_Compile.__default.OfInt(new BigInteger(-302), new BigInteger(10))).Equals(Dafny.Sequence<char>.FromString("-302")))) {
        throw new Dafny.HaltException("/Users/jocorell/crypto-tools/mpl/aws-cryptographic-material-providers-library-net/libraries/src/JSON/Utils/Str.dfy(233,4): " + Dafny.Sequence<char>.FromString("expectation violation"));}
    }
    public static Dafny.ISequence<char> OfBool(bool b) {
      if (b) {
        return Dafny.Sequence<char>.FromString("true");
      } else {
        return Dafny.Sequence<char>.FromString("false");
      }
    }
    public static Dafny.ISequence<char> OfChar(char c) {
      return Dafny.Sequence<char>.FromElements(c);
    }
    public static Dafny.ISequence<char> Join(Dafny.ISequence<char> sep, Dafny.ISequence<Dafny.ISequence<char>> strs)
    {
      Dafny.ISequence<char> _361___accumulator = Dafny.Sequence<char>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((strs).Count)).Sign == 0) {
        return Dafny.Sequence<char>.Concat(_361___accumulator, Dafny.Sequence<char>.FromString(""));
      } else if ((new BigInteger((strs).Count)) == (BigInteger.One)) {
        return Dafny.Sequence<char>.Concat(_361___accumulator, (strs).Select(BigInteger.Zero));
      } else {
        _361___accumulator = Dafny.Sequence<char>.Concat(_361___accumulator, Dafny.Sequence<char>.Concat((strs).Select(BigInteger.Zero), sep));
        Dafny.ISequence<char> _in89 = sep;
        Dafny.ISequence<Dafny.ISequence<char>> _in90 = (strs).Drop(BigInteger.One);
        sep = _in89;
        strs = _in90;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<char> Concat(Dafny.ISequence<Dafny.ISequence<char>> strs) {
      Dafny.ISequence<char> _362___accumulator = Dafny.Sequence<char>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((strs).Count)).Sign == 0) {
        return Dafny.Sequence<char>.Concat(_362___accumulator, Dafny.Sequence<char>.FromString(""));
      } else {
        _362___accumulator = Dafny.Sequence<char>.Concat(_362___accumulator, (strs).Select(BigInteger.Zero));
        Dafny.ISequence<Dafny.ISequence<char>> _in91 = (strs).Drop(BigInteger.One);
        strs = _in91;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<char> HEX__DIGITS { get {
      return Dafny.Sequence<char>.FromString("0123456789ABCDEF");
    } }
    public static Dafny.IMap<char,BigInteger> HEX__TABLE { get {
      return Dafny.Map<char, BigInteger>.FromElements(new Dafny.Pair<char, BigInteger>('0', BigInteger.Zero), new Dafny.Pair<char, BigInteger>('1', BigInteger.One), new Dafny.Pair<char, BigInteger>('2', new BigInteger(2)), new Dafny.Pair<char, BigInteger>('3', new BigInteger(3)), new Dafny.Pair<char, BigInteger>('4', new BigInteger(4)), new Dafny.Pair<char, BigInteger>('5', new BigInteger(5)), new Dafny.Pair<char, BigInteger>('6', new BigInteger(6)), new Dafny.Pair<char, BigInteger>('7', new BigInteger(7)), new Dafny.Pair<char, BigInteger>('8', new BigInteger(8)), new Dafny.Pair<char, BigInteger>('9', new BigInteger(9)), new Dafny.Pair<char, BigInteger>('a', new BigInteger(10)), new Dafny.Pair<char, BigInteger>('b', new BigInteger(11)), new Dafny.Pair<char, BigInteger>('c', new BigInteger(12)), new Dafny.Pair<char, BigInteger>('d', new BigInteger(13)), new Dafny.Pair<char, BigInteger>('e', new BigInteger(14)), new Dafny.Pair<char, BigInteger>('f', new BigInteger(15)), new Dafny.Pair<char, BigInteger>('A', new BigInteger(10)), new Dafny.Pair<char, BigInteger>('B', new BigInteger(11)), new Dafny.Pair<char, BigInteger>('C', new BigInteger(12)), new Dafny.Pair<char, BigInteger>('D', new BigInteger(13)), new Dafny.Pair<char, BigInteger>('E', new BigInteger(14)), new Dafny.Pair<char, BigInteger>('F', new BigInteger(15)));
    } }
  }
} // end of namespace JSON_mUtils_mStr_Compile
namespace JSON_mUtils_mSeq_Compile {

} // end of namespace JSON_mUtils_mSeq_Compile
namespace JSON_mUtils_mViews_mCore_Compile {

  public partial class View {
    private static readonly JSON_mUtils_mViews_mCore_Compile._IView__ Witness = JSON_mUtils_mViews_mCore_Compile.View__.create(Dafny.Sequence<byte>.FromElements(), 0U, 0U);
    public static JSON_mUtils_mViews_mCore_Compile._IView__ Default() {
      return Witness;
    }
    private static readonly Dafny.TypeDescriptor<JSON_mUtils_mViews_mCore_Compile._IView__> _TYPE = new Dafny.TypeDescriptor<JSON_mUtils_mViews_mCore_Compile._IView__>(JSON_mUtils_mViews_mCore_Compile.View.Default());
    public static Dafny.TypeDescriptor<JSON_mUtils_mViews_mCore_Compile._IView__> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public interface _IView__ {
    bool is_View { get; }
    Dafny.ISequence<byte> dtor_s { get; }
    uint dtor_beg { get; }
    uint dtor_end { get; }
    _IView__ DowncastClone();
    bool Empty_q { get; }
    uint Length();
    Dafny.ISequence<byte> Bytes();
    bool Byte_q(byte c);
    bool Char_q(char c);
    byte At(uint idx);
    short Peek();
    void CopyTo(byte[] dest, uint start);
  }
  public class View__ : _IView__ {
    public readonly Dafny.ISequence<byte> _s;
    public readonly uint _beg;
    public readonly uint _end;
    public View__(Dafny.ISequence<byte> s, uint beg, uint end) {
      this._s = s;
      this._beg = beg;
      this._end = end;
    }
    public _IView__ DowncastClone() {
      if (this is _IView__ dt) { return dt; }
      return new View__(_s, _beg, _end);
    }
    public override bool Equals(object other) {
      var oth = other as JSON_mUtils_mViews_mCore_Compile.View__;
      return oth != null && object.Equals(this._s, oth._s) && this._beg == oth._beg && this._end == oth._end;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._s));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._beg));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._end));
      return (int) hash;
    }
    public override string ToString() {
      string ss = "JSON_mUtils_mViews_mCore_Compile.View_.View";
      ss += "(";
      ss += Dafny.Helpers.ToString(this._s);
      ss += ", ";
      ss += Dafny.Helpers.ToString(this._beg);
      ss += ", ";
      ss += Dafny.Helpers.ToString(this._end);
      ss += ")";
      return ss;
    }
    private static readonly JSON_mUtils_mViews_mCore_Compile._IView__ theDefault = create(Dafny.Sequence<byte>.Empty, 0, 0);
    public static JSON_mUtils_mViews_mCore_Compile._IView__ Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<JSON_mUtils_mViews_mCore_Compile._IView__> _TYPE = new Dafny.TypeDescriptor<JSON_mUtils_mViews_mCore_Compile._IView__>(JSON_mUtils_mViews_mCore_Compile.View__.Default());
    public static Dafny.TypeDescriptor<JSON_mUtils_mViews_mCore_Compile._IView__> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IView__ create(Dafny.ISequence<byte> s, uint beg, uint end) {
      return new View__(s, beg, end);
    }
    public static _IView__ create_View(Dafny.ISequence<byte> s, uint beg, uint end) {
      return create(s, beg, end);
    }
    public bool is_View { get { return true; } }
    public Dafny.ISequence<byte> dtor_s {
      get {
        return this._s;
      }
    }
    public uint dtor_beg {
      get {
        return this._beg;
      }
    }
    public uint dtor_end {
      get {
        return this._end;
      }
    }
    public uint Length() {
      return ((this).dtor_end) - ((this).dtor_beg);
    }
    public Dafny.ISequence<byte> Bytes() {
      return ((this).dtor_s).Subsequence((this).dtor_beg, (this).dtor_end);
    }
    public static JSON_mUtils_mViews_mCore_Compile._IView__ OfBytes(Dafny.ISequence<byte> bs) {
      return JSON_mUtils_mViews_mCore_Compile.View__.create(bs, (uint)(0U), (uint)(bs).LongCount);
    }
    public static Dafny.ISequence<byte> OfString(Dafny.ISequence<char> s) {
      return ((System.Func<Dafny.ISequence<byte>>) (() => {
        BigInteger dim5 = new BigInteger((s).Count);
        var arr5 = new byte[Dafny.Helpers.ToIntChecked(dim5, "array size exceeds memory limit")];
        for (int i5 = 0; i5 < dim5; i5++) {
          var _363_i = (BigInteger) i5;
          arr5[(int)(_363_i)] = (byte)((s).Select(_363_i));
        }
        return Dafny.Sequence<byte>.FromArray(arr5);
      }))();
    }
    public bool Byte_q(byte c)
    {
      bool _hresult = false;
      _hresult = (((this).Length()) == (1U)) && (((this).At(0U)) == (c));
      return _hresult;
      return _hresult;
    }
    public bool Char_q(char c) {
      return (this).Byte_q((byte)(c));
    }
    public byte At(uint idx) {
      return ((this).dtor_s).Select(((this).dtor_beg) + (idx));
    }
    public short Peek() {
      if ((this).Empty_q) {
        return (short)(-1);
      } else {
        return (short)((this).At(0U));
      }
    }
    public void CopyTo(byte[] dest, uint start)
    {
      uint _hi8 = (this).Length();
      for (uint _364_idx = 0U; _364_idx < _hi8; _364_idx++) {
        var _index1 = (start) + (_364_idx);
        (dest)[(int)(_index1)] = ((this).dtor_s).Select(((this).dtor_beg) + (_364_idx));
      }
    }
    public static JSON_mUtils_mViews_mCore_Compile._IView__ Empty { get {
      return JSON_mUtils_mViews_mCore_Compile.View__.create(Dafny.Sequence<byte>.FromElements(), 0U, 0U);
    } }
    public bool Empty_q { get {
      return ((this).dtor_beg) == ((this).dtor_end);
    } }
  }

  public partial class __default {
    public static bool Adjacent(JSON_mUtils_mViews_mCore_Compile._IView__ lv, JSON_mUtils_mViews_mCore_Compile._IView__ rv)
    {
      return (((lv).dtor_end) == ((rv).dtor_beg)) && (((lv).dtor_s).Equals((rv).dtor_s));
    }
    public static JSON_mUtils_mViews_mCore_Compile._IView__ Merge(JSON_mUtils_mViews_mCore_Compile._IView__ lv, JSON_mUtils_mViews_mCore_Compile._IView__ rv)
    {
      JSON_mUtils_mViews_mCore_Compile._IView__ _365_dt__update__tmp_h0 = lv;
      uint _366_dt__update_hend_h0 = (rv).dtor_end;
      return JSON_mUtils_mViews_mCore_Compile.View__.create((_365_dt__update__tmp_h0).dtor_s, (_365_dt__update__tmp_h0).dtor_beg, _366_dt__update_hend_h0);
    }
  }
} // end of namespace JSON_mUtils_mViews_mCore_Compile
namespace JSON_mUtils_mViews_mWriters_Compile {

  public interface _IChain {
    bool is_Empty { get; }
    bool is_Chain { get; }
    JSON_mUtils_mViews_mWriters_Compile._IChain dtor_previous { get; }
    JSON_mUtils_mViews_mCore_Compile._IView__ dtor_v { get; }
    _IChain DowncastClone();
    BigInteger Length();
    BigInteger Count();
    Dafny.ISequence<byte> Bytes();
    JSON_mUtils_mViews_mWriters_Compile._IChain Append(JSON_mUtils_mViews_mCore_Compile._IView__ v_k);
    void CopyTo(byte[] dest, uint end);
  }
  public abstract class Chain : _IChain {
    public Chain() { }
    private static readonly JSON_mUtils_mViews_mWriters_Compile._IChain theDefault = create_Empty();
    public static JSON_mUtils_mViews_mWriters_Compile._IChain Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<JSON_mUtils_mViews_mWriters_Compile._IChain> _TYPE = new Dafny.TypeDescriptor<JSON_mUtils_mViews_mWriters_Compile._IChain>(JSON_mUtils_mViews_mWriters_Compile.Chain.Default());
    public static Dafny.TypeDescriptor<JSON_mUtils_mViews_mWriters_Compile._IChain> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IChain create_Empty() {
      return new Chain_Empty();
    }
    public static _IChain create_Chain(JSON_mUtils_mViews_mWriters_Compile._IChain previous, JSON_mUtils_mViews_mCore_Compile._IView__ v) {
      return new Chain_Chain(previous, v);
    }
    public bool is_Empty { get { return this is Chain_Empty; } }
    public bool is_Chain { get { return this is Chain_Chain; } }
    public JSON_mUtils_mViews_mWriters_Compile._IChain dtor_previous {
      get {
        var d = this;
        return ((Chain_Chain)d)._previous;
      }
    }
    public JSON_mUtils_mViews_mCore_Compile._IView__ dtor_v {
      get {
        var d = this;
        return ((Chain_Chain)d)._v;
      }
    }
    public abstract _IChain DowncastClone();
    public BigInteger Length() {
      BigInteger _367___accumulator = BigInteger.Zero;
      _IChain _this = this;
    TAIL_CALL_START: ;
      if ((_this).is_Empty) {
        return (BigInteger.Zero) + (_367___accumulator);
      } else {
        _367___accumulator = (new BigInteger(((_this).dtor_v).Length())) + (_367___accumulator);
        var _in92 = (_this).dtor_previous;
        _this = _in92;
        goto TAIL_CALL_START;
      }
    }
    public BigInteger Count() {
      BigInteger _368___accumulator = BigInteger.Zero;
      _IChain _this = this;
    TAIL_CALL_START: ;
      if ((_this).is_Empty) {
        return (BigInteger.Zero) + (_368___accumulator);
      } else {
        _368___accumulator = (BigInteger.One) + (_368___accumulator);
        var _in93 = (_this).dtor_previous;
        _this = _in93;
        goto TAIL_CALL_START;
      }
    }
    public Dafny.ISequence<byte> Bytes() {
      Dafny.ISequence<byte> _369___accumulator = Dafny.Sequence<byte>.FromElements();
      _IChain _this = this;
    TAIL_CALL_START: ;
      if ((_this).is_Empty) {
        return Dafny.Sequence<byte>.Concat(Dafny.Sequence<byte>.FromElements(), _369___accumulator);
      } else {
        _369___accumulator = Dafny.Sequence<byte>.Concat(((_this).dtor_v).Bytes(), _369___accumulator);
        var _in94 = (_this).dtor_previous;
        _this = _in94;
        goto TAIL_CALL_START;
      }
    }
    public JSON_mUtils_mViews_mWriters_Compile._IChain Append(JSON_mUtils_mViews_mCore_Compile._IView__ v_k) {
      if (((this).is_Chain) && (JSON_mUtils_mViews_mCore_Compile.__default.Adjacent((this).dtor_v, v_k))) {
        return JSON_mUtils_mViews_mWriters_Compile.Chain.create_Chain((this).dtor_previous, JSON_mUtils_mViews_mCore_Compile.__default.Merge((this).dtor_v, v_k));
      } else {
        return JSON_mUtils_mViews_mWriters_Compile.Chain.create_Chain(this, v_k);
      }
    }
    public void CopyTo(byte[] dest, uint end)
    {
      _IChain _this = this;
    TAIL_CALL_START: ;
      if ((_this).is_Chain) {
        uint _370_end;
        _370_end = (end) - (((_this).dtor_v).Length());
        ((_this).dtor_v).CopyTo(dest, _370_end);
        var _in95 = (_this).dtor_previous;
        byte[] _in96 = dest;
        uint _in97 = _370_end;
        _this = _in95;
        dest = _in96;
        end = _in97;
        goto TAIL_CALL_START;
      }
    }
  }
  public class Chain_Empty : Chain {
    public Chain_Empty() {
    }
    public override _IChain DowncastClone() {
      if (this is _IChain dt) { return dt; }
      return new Chain_Empty();
    }
    public override bool Equals(object other) {
      var oth = other as JSON_mUtils_mViews_mWriters_Compile.Chain_Empty;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "JSON_mUtils_mViews_mWriters_Compile.Chain.Empty";
      return s;
    }
  }
  public class Chain_Chain : Chain {
    public readonly JSON_mUtils_mViews_mWriters_Compile._IChain _previous;
    public readonly JSON_mUtils_mViews_mCore_Compile._IView__ _v;
    public Chain_Chain(JSON_mUtils_mViews_mWriters_Compile._IChain previous, JSON_mUtils_mViews_mCore_Compile._IView__ v) {
      this._previous = previous;
      this._v = v;
    }
    public override _IChain DowncastClone() {
      if (this is _IChain dt) { return dt; }
      return new Chain_Chain(_previous, _v);
    }
    public override bool Equals(object other) {
      var oth = other as JSON_mUtils_mViews_mWriters_Compile.Chain_Chain;
      return oth != null && object.Equals(this._previous, oth._previous) && object.Equals(this._v, oth._v);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._previous));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._v));
      return (int) hash;
    }
    public override string ToString() {
      string s = "JSON_mUtils_mViews_mWriters_Compile.Chain.Chain";
      s += "(";
      s += Dafny.Helpers.ToString(this._previous);
      s += ", ";
      s += Dafny.Helpers.ToString(this._v);
      s += ")";
      return s;
    }
  }

  public partial class Writer {
    private static readonly JSON_mUtils_mViews_mWriters_Compile._IWriter__ Witness = JSON_mUtils_mViews_mWriters_Compile.Writer__.create(0U, JSON_mUtils_mViews_mWriters_Compile.Chain.create_Empty());
    public static JSON_mUtils_mViews_mWriters_Compile._IWriter__ Default() {
      return Witness;
    }
    private static readonly Dafny.TypeDescriptor<JSON_mUtils_mViews_mWriters_Compile._IWriter__> _TYPE = new Dafny.TypeDescriptor<JSON_mUtils_mViews_mWriters_Compile._IWriter__>(JSON_mUtils_mViews_mWriters_Compile.Writer.Default());
    public static Dafny.TypeDescriptor<JSON_mUtils_mViews_mWriters_Compile._IWriter__> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public interface _IWriter__ {
    bool is_Writer { get; }
    uint dtor_length { get; }
    JSON_mUtils_mViews_mWriters_Compile._IChain dtor_chain { get; }
    _IWriter__ DowncastClone();
    bool Empty_q { get; }
    bool Unsaturated_q { get; }
    Dafny.ISequence<byte> Bytes();
    JSON_mUtils_mViews_mWriters_Compile._IWriter__ Append(JSON_mUtils_mViews_mCore_Compile._IView__ v_k);
    JSON_mUtils_mViews_mWriters_Compile._IWriter__ Then(Func<JSON_mUtils_mViews_mWriters_Compile._IWriter__, JSON_mUtils_mViews_mWriters_Compile._IWriter__> fn);
    void CopyTo(byte[] dest);
    byte[] ToArray();
  }
  public class Writer__ : _IWriter__ {
    public readonly uint _length;
    public readonly JSON_mUtils_mViews_mWriters_Compile._IChain _chain;
    public Writer__(uint length, JSON_mUtils_mViews_mWriters_Compile._IChain chain) {
      this._length = length;
      this._chain = chain;
    }
    public _IWriter__ DowncastClone() {
      if (this is _IWriter__ dt) { return dt; }
      return new Writer__(_length, _chain);
    }
    public override bool Equals(object other) {
      var oth = other as JSON_mUtils_mViews_mWriters_Compile.Writer__;
      return oth != null && this._length == oth._length && object.Equals(this._chain, oth._chain);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._length));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._chain));
      return (int) hash;
    }
    public override string ToString() {
      string s = "JSON_mUtils_mViews_mWriters_Compile.Writer_.Writer";
      s += "(";
      s += Dafny.Helpers.ToString(this._length);
      s += ", ";
      s += Dafny.Helpers.ToString(this._chain);
      s += ")";
      return s;
    }
    private static readonly JSON_mUtils_mViews_mWriters_Compile._IWriter__ theDefault = create(0, JSON_mUtils_mViews_mWriters_Compile.Chain.Default());
    public static JSON_mUtils_mViews_mWriters_Compile._IWriter__ Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<JSON_mUtils_mViews_mWriters_Compile._IWriter__> _TYPE = new Dafny.TypeDescriptor<JSON_mUtils_mViews_mWriters_Compile._IWriter__>(JSON_mUtils_mViews_mWriters_Compile.Writer__.Default());
    public static Dafny.TypeDescriptor<JSON_mUtils_mViews_mWriters_Compile._IWriter__> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IWriter__ create(uint length, JSON_mUtils_mViews_mWriters_Compile._IChain chain) {
      return new Writer__(length, chain);
    }
    public static _IWriter__ create_Writer(uint length, JSON_mUtils_mViews_mWriters_Compile._IChain chain) {
      return create(length, chain);
    }
    public bool is_Writer { get { return true; } }
    public uint dtor_length {
      get {
        return this._length;
      }
    }
    public JSON_mUtils_mViews_mWriters_Compile._IChain dtor_chain {
      get {
        return this._chain;
      }
    }
    public Dafny.ISequence<byte> Bytes() {
      return ((this).dtor_chain).Bytes();
    }
    public static uint SaturatedAddU32(uint a, uint b)
    {
      if ((a) <= ((BoundedInts_Compile.__default.UINT32__MAX) - (b))) {
        return (a) + (b);
      } else {
        return BoundedInts_Compile.__default.UINT32__MAX;
      }
    }
    public JSON_mUtils_mViews_mWriters_Compile._IWriter__ Append(JSON_mUtils_mViews_mCore_Compile._IView__ v_k) {
      return JSON_mUtils_mViews_mWriters_Compile.Writer__.create(JSON_mUtils_mViews_mWriters_Compile.Writer__.SaturatedAddU32((this).dtor_length, (v_k).Length()), ((this).dtor_chain).Append(v_k));
    }
    public JSON_mUtils_mViews_mWriters_Compile._IWriter__ Then(Func<JSON_mUtils_mViews_mWriters_Compile._IWriter__, JSON_mUtils_mViews_mWriters_Compile._IWriter__> fn) {
      return Dafny.Helpers.Id<Func<JSON_mUtils_mViews_mWriters_Compile._IWriter__, JSON_mUtils_mViews_mWriters_Compile._IWriter__>>(fn)(this);
    }
    public void CopyTo(byte[] dest)
    {
      ((this).dtor_chain).CopyTo(dest, (this).dtor_length);
    }
    public byte[] ToArray()
    {
      byte[] bs = new byte[0];
      byte[] _nw6 = new byte[Dafny.Helpers.ToIntChecked((this).dtor_length, "array size exceeds memory limit")];
      bs = _nw6;
      (this).CopyTo(bs);
      return bs;
    }
    public static JSON_mUtils_mViews_mWriters_Compile._IWriter__ Empty { get {
      return JSON_mUtils_mViews_mWriters_Compile.Writer__.create(0U, JSON_mUtils_mViews_mWriters_Compile.Chain.create_Empty());
    } }
    public bool Unsaturated_q { get {
      return ((this).dtor_length) != (BoundedInts_Compile.__default.UINT32__MAX);
    } }
    public bool Empty_q { get {
      return ((this).dtor_chain).is_Empty;
    } }
  }

} // end of namespace JSON_mUtils_mViews_mWriters_Compile
namespace JSON_mUtils_mViews_Compile {

} // end of namespace JSON_mUtils_mViews_Compile
namespace JSON_mUtils_mLexers_mCore_Compile {

  public interface _ILexerResult<out T, out R> {
    bool is_Accept { get; }
    bool is_Reject { get; }
    bool is_Partial { get; }
    R dtor_err { get; }
    T dtor_st { get; }
    _ILexerResult<__T, __R> DowncastClone<__T, __R>(Func<T, __T> converter0, Func<R, __R> converter1);
  }
  public abstract class LexerResult<T, R> : _ILexerResult<T, R> {
    public LexerResult() { }
    public static JSON_mUtils_mLexers_mCore_Compile._ILexerResult<T, R> Default() {
      return create_Accept();
    }
    public static Dafny.TypeDescriptor<JSON_mUtils_mLexers_mCore_Compile._ILexerResult<T, R>> _TypeDescriptor() {
      return new Dafny.TypeDescriptor<JSON_mUtils_mLexers_mCore_Compile._ILexerResult<T, R>>(JSON_mUtils_mLexers_mCore_Compile.LexerResult<T, R>.Default());
    }
    public static _ILexerResult<T, R> create_Accept() {
      return new LexerResult_Accept<T, R>();
    }
    public static _ILexerResult<T, R> create_Reject(R err) {
      return new LexerResult_Reject<T, R>(err);
    }
    public static _ILexerResult<T, R> create_Partial(T st) {
      return new LexerResult_Partial<T, R>(st);
    }
    public bool is_Accept { get { return this is LexerResult_Accept<T, R>; } }
    public bool is_Reject { get { return this is LexerResult_Reject<T, R>; } }
    public bool is_Partial { get { return this is LexerResult_Partial<T, R>; } }
    public R dtor_err {
      get {
        var d = this;
        return ((LexerResult_Reject<T, R>)d)._err;
      }
    }
    public T dtor_st {
      get {
        var d = this;
        return ((LexerResult_Partial<T, R>)d)._st;
      }
    }
    public abstract _ILexerResult<__T, __R> DowncastClone<__T, __R>(Func<T, __T> converter0, Func<R, __R> converter1);
  }
  public class LexerResult_Accept<T, R> : LexerResult<T, R> {
    public LexerResult_Accept() {
    }
    public override _ILexerResult<__T, __R> DowncastClone<__T, __R>(Func<T, __T> converter0, Func<R, __R> converter1) {
      if (this is _ILexerResult<__T, __R> dt) { return dt; }
      return new LexerResult_Accept<__T, __R>();
    }
    public override bool Equals(object other) {
      var oth = other as JSON_mUtils_mLexers_mCore_Compile.LexerResult_Accept<T, R>;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "JSON_mUtils_mLexers_mCore_Compile.LexerResult.Accept";
      return s;
    }
  }
  public class LexerResult_Reject<T, R> : LexerResult<T, R> {
    public readonly R _err;
    public LexerResult_Reject(R err) {
      this._err = err;
    }
    public override _ILexerResult<__T, __R> DowncastClone<__T, __R>(Func<T, __T> converter0, Func<R, __R> converter1) {
      if (this is _ILexerResult<__T, __R> dt) { return dt; }
      return new LexerResult_Reject<__T, __R>(converter1(_err));
    }
    public override bool Equals(object other) {
      var oth = other as JSON_mUtils_mLexers_mCore_Compile.LexerResult_Reject<T, R>;
      return oth != null && object.Equals(this._err, oth._err);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._err));
      return (int) hash;
    }
    public override string ToString() {
      string s = "JSON_mUtils_mLexers_mCore_Compile.LexerResult.Reject";
      s += "(";
      s += Dafny.Helpers.ToString(this._err);
      s += ")";
      return s;
    }
  }
  public class LexerResult_Partial<T, R> : LexerResult<T, R> {
    public readonly T _st;
    public LexerResult_Partial(T st) {
      this._st = st;
    }
    public override _ILexerResult<__T, __R> DowncastClone<__T, __R>(Func<T, __T> converter0, Func<R, __R> converter1) {
      if (this is _ILexerResult<__T, __R> dt) { return dt; }
      return new LexerResult_Partial<__T, __R>(converter0(_st));
    }
    public override bool Equals(object other) {
      var oth = other as JSON_mUtils_mLexers_mCore_Compile.LexerResult_Partial<T, R>;
      return oth != null && object.Equals(this._st, oth._st);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 2;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._st));
      return (int) hash;
    }
    public override string ToString() {
      string s = "JSON_mUtils_mLexers_mCore_Compile.LexerResult.Partial";
      s += "(";
      s += Dafny.Helpers.ToString(this._st);
      s += ")";
      return s;
    }
  }

} // end of namespace JSON_mUtils_mLexers_mCore_Compile
namespace JSON_mUtils_mLexers_mStrings_Compile {

  public interface _IStringLexerState {
    bool is_Start { get; }
    bool is_Body { get; }
    bool is_End { get; }
    bool dtor_escaped { get; }
    _IStringLexerState DowncastClone();
  }
  public abstract class StringLexerState : _IStringLexerState {
    public StringLexerState() { }
    private static readonly JSON_mUtils_mLexers_mStrings_Compile._IStringLexerState theDefault = create_Start();
    public static JSON_mUtils_mLexers_mStrings_Compile._IStringLexerState Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<JSON_mUtils_mLexers_mStrings_Compile._IStringLexerState> _TYPE = new Dafny.TypeDescriptor<JSON_mUtils_mLexers_mStrings_Compile._IStringLexerState>(JSON_mUtils_mLexers_mStrings_Compile.StringLexerState.Default());
    public static Dafny.TypeDescriptor<JSON_mUtils_mLexers_mStrings_Compile._IStringLexerState> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IStringLexerState create_Start() {
      return new StringLexerState_Start();
    }
    public static _IStringLexerState create_Body(bool escaped) {
      return new StringLexerState_Body(escaped);
    }
    public static _IStringLexerState create_End() {
      return new StringLexerState_End();
    }
    public bool is_Start { get { return this is StringLexerState_Start; } }
    public bool is_Body { get { return this is StringLexerState_Body; } }
    public bool is_End { get { return this is StringLexerState_End; } }
    public bool dtor_escaped {
      get {
        var d = this;
        return ((StringLexerState_Body)d)._escaped;
      }
    }
    public abstract _IStringLexerState DowncastClone();
  }
  public class StringLexerState_Start : StringLexerState {
    public StringLexerState_Start() {
    }
    public override _IStringLexerState DowncastClone() {
      if (this is _IStringLexerState dt) { return dt; }
      return new StringLexerState_Start();
    }
    public override bool Equals(object other) {
      var oth = other as JSON_mUtils_mLexers_mStrings_Compile.StringLexerState_Start;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "JSON_mUtils_mLexers_mStrings_Compile.StringLexerState.Start";
      return s;
    }
  }
  public class StringLexerState_Body : StringLexerState {
    public readonly bool _escaped;
    public StringLexerState_Body(bool escaped) {
      this._escaped = escaped;
    }
    public override _IStringLexerState DowncastClone() {
      if (this is _IStringLexerState dt) { return dt; }
      return new StringLexerState_Body(_escaped);
    }
    public override bool Equals(object other) {
      var oth = other as JSON_mUtils_mLexers_mStrings_Compile.StringLexerState_Body;
      return oth != null && this._escaped == oth._escaped;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._escaped));
      return (int) hash;
    }
    public override string ToString() {
      string s = "JSON_mUtils_mLexers_mStrings_Compile.StringLexerState.Body";
      s += "(";
      s += Dafny.Helpers.ToString(this._escaped);
      s += ")";
      return s;
    }
  }
  public class StringLexerState_End : StringLexerState {
    public StringLexerState_End() {
    }
    public override _IStringLexerState DowncastClone() {
      if (this is _IStringLexerState dt) { return dt; }
      return new StringLexerState_End();
    }
    public override bool Equals(object other) {
      var oth = other as JSON_mUtils_mLexers_mStrings_Compile.StringLexerState_End;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 2;
      return (int) hash;
    }
    public override string ToString() {
      string s = "JSON_mUtils_mLexers_mStrings_Compile.StringLexerState.End";
      return s;
    }
  }

  public partial class __default {
    public static JSON_mUtils_mLexers_mCore_Compile._ILexerResult<bool, __R> StringBody<__R>(bool escaped, short @byte)
    {
      if ((@byte) == ((short)('\\'))) {
        return JSON_mUtils_mLexers_mCore_Compile.LexerResult<bool, __R>.create_Partial(!(escaped));
      } else if (((@byte) == ((short)('\"'))) && (!(escaped))) {
        return JSON_mUtils_mLexers_mCore_Compile.LexerResult<bool, __R>.create_Accept();
      } else {
        return JSON_mUtils_mLexers_mCore_Compile.LexerResult<bool, __R>.create_Partial(false);
      }
    }
    public static JSON_mUtils_mLexers_mCore_Compile._ILexerResult<JSON_mUtils_mLexers_mStrings_Compile._IStringLexerState, Dafny.ISequence<char>> String(JSON_mUtils_mLexers_mStrings_Compile._IStringLexerState st, short @byte)
    {
      JSON_mUtils_mLexers_mStrings_Compile._IStringLexerState _source6 = st;
      if (_source6.is_Start) {
        if ((@byte) == ((short)('\"'))) {
          return JSON_mUtils_mLexers_mCore_Compile.LexerResult<JSON_mUtils_mLexers_mStrings_Compile._IStringLexerState, Dafny.ISequence<char>>.create_Partial(JSON_mUtils_mLexers_mStrings_Compile.StringLexerState.create_Body(false));
        } else {
          return JSON_mUtils_mLexers_mCore_Compile.LexerResult<JSON_mUtils_mLexers_mStrings_Compile._IStringLexerState, Dafny.ISequence<char>>.create_Reject(Dafny.Sequence<char>.FromString("String must start with double quote"));
        }
      } else if (_source6.is_Body) {
        bool _371___mcc_h0 = _source6.dtor_escaped;
        bool _372_escaped = _371___mcc_h0;
        if ((@byte) == ((short)('\\'))) {
          return JSON_mUtils_mLexers_mCore_Compile.LexerResult<JSON_mUtils_mLexers_mStrings_Compile._IStringLexerState, Dafny.ISequence<char>>.create_Partial(JSON_mUtils_mLexers_mStrings_Compile.StringLexerState.create_Body(!(_372_escaped)));
        } else if (((@byte) == ((short)('\"'))) && (!(_372_escaped))) {
          return JSON_mUtils_mLexers_mCore_Compile.LexerResult<JSON_mUtils_mLexers_mStrings_Compile._IStringLexerState, Dafny.ISequence<char>>.create_Partial(JSON_mUtils_mLexers_mStrings_Compile.StringLexerState.create_End());
        } else {
          return JSON_mUtils_mLexers_mCore_Compile.LexerResult<JSON_mUtils_mLexers_mStrings_Compile._IStringLexerState, Dafny.ISequence<char>>.create_Partial(JSON_mUtils_mLexers_mStrings_Compile.StringLexerState.create_Body(false));
        }
      } else {
        return JSON_mUtils_mLexers_mCore_Compile.LexerResult<JSON_mUtils_mLexers_mStrings_Compile._IStringLexerState, Dafny.ISequence<char>>.create_Accept();
      }
    }
    public static bool StringBodyLexerStart { get {
      return false;
    } }
    public static JSON_mUtils_mLexers_mStrings_Compile._IStringLexerState StringLexerStart { get {
      return JSON_mUtils_mLexers_mStrings_Compile.StringLexerState.create_Start();
    } }
  }
} // end of namespace JSON_mUtils_mLexers_mStrings_Compile
namespace JSON_mUtils_mLexers_Compile {

} // end of namespace JSON_mUtils_mLexers_Compile
namespace JSON_mUtils_mCursors_Compile {

  public interface _ISplit<out T> {
    bool is_SP { get; }
    T dtor_t { get; }
    JSON_mUtils_mCursors_Compile._ICursor__ dtor_cs { get; }
    _ISplit<__T> DowncastClone<__T>(Func<T, __T> converter0);
  }
  public class Split<T> : _ISplit<T> {
    public readonly T _t;
    public readonly JSON_mUtils_mCursors_Compile._ICursor__ _cs;
    public Split(T t, JSON_mUtils_mCursors_Compile._ICursor__ cs) {
      this._t = t;
      this._cs = cs;
    }
    public _ISplit<__T> DowncastClone<__T>(Func<T, __T> converter0) {
      if (this is _ISplit<__T> dt) { return dt; }
      return new Split<__T>(converter0(_t), _cs);
    }
    public override bool Equals(object other) {
      var oth = other as JSON_mUtils_mCursors_Compile.Split<T>;
      return oth != null && object.Equals(this._t, oth._t) && object.Equals(this._cs, oth._cs);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._t));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._cs));
      return (int) hash;
    }
    public override string ToString() {
      string s = "JSON_mUtils_mCursors_Compile.Split.SP";
      s += "(";
      s += Dafny.Helpers.ToString(this._t);
      s += ", ";
      s += Dafny.Helpers.ToString(this._cs);
      s += ")";
      return s;
    }
    public static JSON_mUtils_mCursors_Compile._ISplit<T> Default(T _default_T) {
      return create(_default_T, JSON_mUtils_mCursors_Compile.FreshCursor.Default());
    }
    public static Dafny.TypeDescriptor<JSON_mUtils_mCursors_Compile._ISplit<T>> _TypeDescriptor(Dafny.TypeDescriptor<T> _td_T) {
      return new Dafny.TypeDescriptor<JSON_mUtils_mCursors_Compile._ISplit<T>>(JSON_mUtils_mCursors_Compile.Split<T>.Default(_td_T.Default()));
    }
    public static _ISplit<T> create(T t, JSON_mUtils_mCursors_Compile._ICursor__ cs) {
      return new Split<T>(t, cs);
    }
    public static _ISplit<T> create_SP(T t, JSON_mUtils_mCursors_Compile._ICursor__ cs) {
      return create(t, cs);
    }
    public bool is_SP { get { return true; } }
    public T dtor_t {
      get {
        return this._t;
      }
    }
    public JSON_mUtils_mCursors_Compile._ICursor__ dtor_cs {
      get {
        return this._cs;
      }
    }
  }

  public partial class Cursor {
    private static readonly JSON_mUtils_mCursors_Compile._ICursor__ Witness = JSON_mUtils_mCursors_Compile.Cursor__.create(Dafny.Sequence<byte>.FromElements(), 0U, 0U, 0U);
    public static JSON_mUtils_mCursors_Compile._ICursor__ Default() {
      return Witness;
    }
    private static readonly Dafny.TypeDescriptor<JSON_mUtils_mCursors_Compile._ICursor__> _TYPE = new Dafny.TypeDescriptor<JSON_mUtils_mCursors_Compile._ICursor__>(JSON_mUtils_mCursors_Compile.Cursor.Default());
    public static Dafny.TypeDescriptor<JSON_mUtils_mCursors_Compile._ICursor__> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class FreshCursor {
    private static readonly JSON_mUtils_mCursors_Compile._ICursor__ Witness = JSON_mUtils_mCursors_Compile.Cursor__.create(Dafny.Sequence<byte>.FromElements(), 0U, 0U, 0U);
    public static JSON_mUtils_mCursors_Compile._ICursor__ Default() {
      return Witness;
    }
    private static readonly Dafny.TypeDescriptor<JSON_mUtils_mCursors_Compile._ICursor__> _TYPE = new Dafny.TypeDescriptor<JSON_mUtils_mCursors_Compile._ICursor__>(JSON_mUtils_mCursors_Compile.FreshCursor.Default());
    public static Dafny.TypeDescriptor<JSON_mUtils_mCursors_Compile._ICursor__> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public interface _ICursorError<out R> {
    bool is_EOF { get; }
    bool is_ExpectingByte { get; }
    bool is_ExpectingAnyByte { get; }
    bool is_OtherError { get; }
    byte dtor_expected { get; }
    short dtor_b { get; }
    Dafny.ISequence<byte> dtor_expected__sq { get; }
    R dtor_err { get; }
    _ICursorError<__R> DowncastClone<__R>(Func<R, __R> converter0);
  }
  public abstract class CursorError<R> : _ICursorError<R> {
    public CursorError() { }
    public static JSON_mUtils_mCursors_Compile._ICursorError<R> Default() {
      return create_EOF();
    }
    public static Dafny.TypeDescriptor<JSON_mUtils_mCursors_Compile._ICursorError<R>> _TypeDescriptor() {
      return new Dafny.TypeDescriptor<JSON_mUtils_mCursors_Compile._ICursorError<R>>(JSON_mUtils_mCursors_Compile.CursorError<R>.Default());
    }
    public static _ICursorError<R> create_EOF() {
      return new CursorError_EOF<R>();
    }
    public static _ICursorError<R> create_ExpectingByte(byte expected, short b) {
      return new CursorError_ExpectingByte<R>(expected, b);
    }
    public static _ICursorError<R> create_ExpectingAnyByte(Dafny.ISequence<byte> expected__sq, short b) {
      return new CursorError_ExpectingAnyByte<R>(expected__sq, b);
    }
    public static _ICursorError<R> create_OtherError(R err) {
      return new CursorError_OtherError<R>(err);
    }
    public bool is_EOF { get { return this is CursorError_EOF<R>; } }
    public bool is_ExpectingByte { get { return this is CursorError_ExpectingByte<R>; } }
    public bool is_ExpectingAnyByte { get { return this is CursorError_ExpectingAnyByte<R>; } }
    public bool is_OtherError { get { return this is CursorError_OtherError<R>; } }
    public byte dtor_expected {
      get {
        var d = this;
        return ((CursorError_ExpectingByte<R>)d)._expected;
      }
    }
    public short dtor_b {
      get {
        var d = this;
        if (d is CursorError_ExpectingByte<R>) { return ((CursorError_ExpectingByte<R>)d)._b; }
        return ((CursorError_ExpectingAnyByte<R>)d)._b;
      }
    }
    public Dafny.ISequence<byte> dtor_expected__sq {
      get {
        var d = this;
        return ((CursorError_ExpectingAnyByte<R>)d)._expected__sq;
      }
    }
    public R dtor_err {
      get {
        var d = this;
        return ((CursorError_OtherError<R>)d)._err;
      }
    }
    public abstract _ICursorError<__R> DowncastClone<__R>(Func<R, __R> converter0);
    public static Dafny.ISequence<char> _ToString(JSON_mUtils_mCursors_Compile._ICursorError<R> _this, Func<R, Dafny.ISequence<char>> pr) {
      JSON_mUtils_mCursors_Compile._ICursorError<R> _source7 = _this;
      if (_source7.is_EOF) {
        return Dafny.Sequence<char>.FromString("Reached EOF");
      } else if (_source7.is_ExpectingByte) {
        byte _373___mcc_h0 = _source7.dtor_expected;
        short _374___mcc_h1 = _source7.dtor_b;
        short _375_b = _374___mcc_h1;
        byte _376_b0 = _373___mcc_h0;
        Dafny.ISequence<char> _377_c = (((_375_b) > ((short)(0))) ? (Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.FromString("'"), Dafny.Sequence<char>.FromElements((char)(_375_b))), Dafny.Sequence<char>.FromString("'"))) : (Dafny.Sequence<char>.FromString("EOF")));
        return Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.FromString("Expecting '"), Dafny.Sequence<char>.FromElements((char)(_376_b0))), Dafny.Sequence<char>.FromString("', read ")), _377_c);
      } else if (_source7.is_ExpectingAnyByte) {
        Dafny.ISequence<byte> _378___mcc_h2 = _source7.dtor_expected__sq;
        short _379___mcc_h3 = _source7.dtor_b;
        short _380_b = _379___mcc_h3;
        Dafny.ISequence<byte> _381_bs0 = _378___mcc_h2;
        Dafny.ISequence<char> _382_c = (((_380_b) > ((short)(0))) ? (Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.FromString("'"), Dafny.Sequence<char>.FromElements((char)(_380_b))), Dafny.Sequence<char>.FromString("'"))) : (Dafny.Sequence<char>.FromString("EOF")));
        Dafny.ISequence<char> _383_c0s = ((System.Func<Dafny.ISequence<char>>) (() => {
          BigInteger dim6 = new BigInteger((_381_bs0).Count);
          var arr6 = new char[Dafny.Helpers.ToIntChecked(dim6, "array size exceeds memory limit")];
          for (int i6 = 0; i6 < dim6; i6++) {
            var _384_idx = (BigInteger) i6;
            arr6[(int)(_384_idx)] = (char)((_381_bs0).Select(_384_idx));
          }
          return Dafny.Sequence<char>.FromArray(arr6);
        }))();
        return Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.FromString("Expecting one of '"), _383_c0s), Dafny.Sequence<char>.FromString("', read ")), _382_c);
      } else {
        R _385___mcc_h4 = _source7.dtor_err;
        R _386_err = _385___mcc_h4;
        return Dafny.Helpers.Id<Func<R, Dafny.ISequence<char>>>(pr)(_386_err);
      }
    }
  }
  public class CursorError_EOF<R> : CursorError<R> {
    public CursorError_EOF() {
    }
    public override _ICursorError<__R> DowncastClone<__R>(Func<R, __R> converter0) {
      if (this is _ICursorError<__R> dt) { return dt; }
      return new CursorError_EOF<__R>();
    }
    public override bool Equals(object other) {
      var oth = other as JSON_mUtils_mCursors_Compile.CursorError_EOF<R>;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "JSON_mUtils_mCursors_Compile.CursorError.EOF";
      return s;
    }
  }
  public class CursorError_ExpectingByte<R> : CursorError<R> {
    public readonly byte _expected;
    public readonly short _b;
    public CursorError_ExpectingByte(byte expected, short b) {
      this._expected = expected;
      this._b = b;
    }
    public override _ICursorError<__R> DowncastClone<__R>(Func<R, __R> converter0) {
      if (this is _ICursorError<__R> dt) { return dt; }
      return new CursorError_ExpectingByte<__R>(_expected, _b);
    }
    public override bool Equals(object other) {
      var oth = other as JSON_mUtils_mCursors_Compile.CursorError_ExpectingByte<R>;
      return oth != null && this._expected == oth._expected && this._b == oth._b;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._expected));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._b));
      return (int) hash;
    }
    public override string ToString() {
      string s = "JSON_mUtils_mCursors_Compile.CursorError.ExpectingByte";
      s += "(";
      s += Dafny.Helpers.ToString(this._expected);
      s += ", ";
      s += Dafny.Helpers.ToString(this._b);
      s += ")";
      return s;
    }
  }
  public class CursorError_ExpectingAnyByte<R> : CursorError<R> {
    public readonly Dafny.ISequence<byte> _expected__sq;
    public readonly short _b;
    public CursorError_ExpectingAnyByte(Dafny.ISequence<byte> expected__sq, short b) {
      this._expected__sq = expected__sq;
      this._b = b;
    }
    public override _ICursorError<__R> DowncastClone<__R>(Func<R, __R> converter0) {
      if (this is _ICursorError<__R> dt) { return dt; }
      return new CursorError_ExpectingAnyByte<__R>(_expected__sq, _b);
    }
    public override bool Equals(object other) {
      var oth = other as JSON_mUtils_mCursors_Compile.CursorError_ExpectingAnyByte<R>;
      return oth != null && object.Equals(this._expected__sq, oth._expected__sq) && this._b == oth._b;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 2;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._expected__sq));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._b));
      return (int) hash;
    }
    public override string ToString() {
      string s = "JSON_mUtils_mCursors_Compile.CursorError.ExpectingAnyByte";
      s += "(";
      s += Dafny.Helpers.ToString(this._expected__sq);
      s += ", ";
      s += Dafny.Helpers.ToString(this._b);
      s += ")";
      return s;
    }
  }
  public class CursorError_OtherError<R> : CursorError<R> {
    public readonly R _err;
    public CursorError_OtherError(R err) {
      this._err = err;
    }
    public override _ICursorError<__R> DowncastClone<__R>(Func<R, __R> converter0) {
      if (this is _ICursorError<__R> dt) { return dt; }
      return new CursorError_OtherError<__R>(converter0(_err));
    }
    public override bool Equals(object other) {
      var oth = other as JSON_mUtils_mCursors_Compile.CursorError_OtherError<R>;
      return oth != null && object.Equals(this._err, oth._err);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 3;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._err));
      return (int) hash;
    }
    public override string ToString() {
      string s = "JSON_mUtils_mCursors_Compile.CursorError.OtherError";
      s += "(";
      s += Dafny.Helpers.ToString(this._err);
      s += ")";
      return s;
    }
  }

  public interface _ICursor__ {
    bool is_Cursor { get; }
    Dafny.ISequence<byte> dtor_s { get; }
    uint dtor_beg { get; }
    uint dtor_point { get; }
    uint dtor_end { get; }
    _ICursor__ DowncastClone();
    bool BOF_q { get; }
    bool EOF_q { get; }
    Dafny.ISequence<byte> Bytes();
    JSON_mUtils_mViews_mCore_Compile._IView__ Prefix();
    JSON_mUtils_mCursors_Compile._ICursor__ Suffix();
    JSON_mUtils_mCursors_Compile._ISplit<JSON_mUtils_mViews_mCore_Compile._IView__> Split();
    uint PrefixLength();
    uint SuffixLength();
    uint Length();
    byte At(uint idx);
    byte SuffixAt(uint idx);
    short Peek();
    bool LookingAt(char c);
    JSON_mUtils_mCursors_Compile._ICursor__ Skip(uint n);
    JSON_mUtils_mCursors_Compile._ICursor__ Unskip(uint n);
    Wrappers_Compile._IResult<JSON_mUtils_mCursors_Compile._ICursor__, JSON_mUtils_mCursors_Compile._ICursorError<__R>> Get<__R>(__R err);
    Wrappers_Compile._IResult<JSON_mUtils_mCursors_Compile._ICursor__, JSON_mUtils_mCursors_Compile._ICursorError<__R>> AssertByte<__R>(byte b);
    Wrappers_Compile._IResult<JSON_mUtils_mCursors_Compile._ICursor__, JSON_mUtils_mCursors_Compile._ICursorError<__R>> AssertBytes<__R>(Dafny.ISequence<byte> bs, uint offset);
    Wrappers_Compile._IResult<JSON_mUtils_mCursors_Compile._ICursor__, JSON_mUtils_mCursors_Compile._ICursorError<__R>> AssertChar<__R>(char c0);
    JSON_mUtils_mCursors_Compile._ICursor__ SkipByte();
    JSON_mUtils_mCursors_Compile._ICursor__ SkipIf(Func<byte, bool> p);
    JSON_mUtils_mCursors_Compile._ICursor__ SkipWhile(Func<byte, bool> p);
    Wrappers_Compile._IResult<JSON_mUtils_mCursors_Compile._ICursor__, JSON_mUtils_mCursors_Compile._ICursorError<__R>> SkipWhileLexer<__A, __R>(Func<__A, short, JSON_mUtils_mLexers_mCore_Compile._ILexerResult<__A, __R>> step, __A st);
  }
  public class Cursor__ : _ICursor__ {
    public readonly Dafny.ISequence<byte> _s;
    public readonly uint _beg;
    public readonly uint _point;
    public readonly uint _end;
    public Cursor__(Dafny.ISequence<byte> s, uint beg, uint point, uint end) {
      this._s = s;
      this._beg = beg;
      this._point = point;
      this._end = end;
    }
    public _ICursor__ DowncastClone() {
      if (this is _ICursor__ dt) { return dt; }
      return new Cursor__(_s, _beg, _point, _end);
    }
    public override bool Equals(object other) {
      var oth = other as JSON_mUtils_mCursors_Compile.Cursor__;
      return oth != null && object.Equals(this._s, oth._s) && this._beg == oth._beg && this._point == oth._point && this._end == oth._end;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._s));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._beg));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._point));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._end));
      return (int) hash;
    }
    public override string ToString() {
      string ss = "JSON_mUtils_mCursors_Compile.Cursor_.Cursor";
      ss += "(";
      ss += Dafny.Helpers.ToString(this._s);
      ss += ", ";
      ss += Dafny.Helpers.ToString(this._beg);
      ss += ", ";
      ss += Dafny.Helpers.ToString(this._point);
      ss += ", ";
      ss += Dafny.Helpers.ToString(this._end);
      ss += ")";
      return ss;
    }
    private static readonly JSON_mUtils_mCursors_Compile._ICursor__ theDefault = create(Dafny.Sequence<byte>.Empty, 0, 0, 0);
    public static JSON_mUtils_mCursors_Compile._ICursor__ Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<JSON_mUtils_mCursors_Compile._ICursor__> _TYPE = new Dafny.TypeDescriptor<JSON_mUtils_mCursors_Compile._ICursor__>(JSON_mUtils_mCursors_Compile.Cursor__.Default());
    public static Dafny.TypeDescriptor<JSON_mUtils_mCursors_Compile._ICursor__> _TypeDescriptor() {
      return _TYPE;
    }
    public static _ICursor__ create(Dafny.ISequence<byte> s, uint beg, uint point, uint end) {
      return new Cursor__(s, beg, point, end);
    }
    public static _ICursor__ create_Cursor(Dafny.ISequence<byte> s, uint beg, uint point, uint end) {
      return create(s, beg, point, end);
    }
    public bool is_Cursor { get { return true; } }
    public Dafny.ISequence<byte> dtor_s {
      get {
        return this._s;
      }
    }
    public uint dtor_beg {
      get {
        return this._beg;
      }
    }
    public uint dtor_point {
      get {
        return this._point;
      }
    }
    public uint dtor_end {
      get {
        return this._end;
      }
    }
    public static JSON_mUtils_mCursors_Compile._ICursor__ OfView(JSON_mUtils_mViews_mCore_Compile._IView__ v) {
      return JSON_mUtils_mCursors_Compile.Cursor__.create((v).dtor_s, (v).dtor_beg, (v).dtor_beg, (v).dtor_end);
    }
    public static JSON_mUtils_mCursors_Compile._ICursor__ OfBytes(Dafny.ISequence<byte> bs) {
      return JSON_mUtils_mCursors_Compile.Cursor__.create(bs, 0U, 0U, (uint)(bs).LongCount);
    }
    public Dafny.ISequence<byte> Bytes() {
      return ((this).dtor_s).Subsequence((this).dtor_beg, (this).dtor_end);
    }
    public JSON_mUtils_mViews_mCore_Compile._IView__ Prefix() {
      return JSON_mUtils_mViews_mCore_Compile.View__.create((this).dtor_s, (this).dtor_beg, (this).dtor_point);
    }
    public JSON_mUtils_mCursors_Compile._ICursor__ Suffix() {
      JSON_mUtils_mCursors_Compile._ICursor__ _387_dt__update__tmp_h0 = this;
      uint _388_dt__update_hbeg_h0 = (this).dtor_point;
      return JSON_mUtils_mCursors_Compile.Cursor__.create((_387_dt__update__tmp_h0).dtor_s, _388_dt__update_hbeg_h0, (_387_dt__update__tmp_h0).dtor_point, (_387_dt__update__tmp_h0).dtor_end);
    }
    public JSON_mUtils_mCursors_Compile._ISplit<JSON_mUtils_mViews_mCore_Compile._IView__> Split() {
      return JSON_mUtils_mCursors_Compile.Split<JSON_mUtils_mViews_mCore_Compile._IView__>.create((this).Prefix(), (this).Suffix());
    }
    public uint PrefixLength() {
      return ((this).dtor_point) - ((this).dtor_beg);
    }
    public uint SuffixLength() {
      return ((this).dtor_end) - ((this).dtor_point);
    }
    public uint Length() {
      return ((this).dtor_end) - ((this).dtor_beg);
    }
    public byte At(uint idx) {
      return ((this).dtor_s).Select(((this).dtor_beg) + (idx));
    }
    public byte SuffixAt(uint idx) {
      return ((this).dtor_s).Select(((this).dtor_point) + (idx));
    }
    public short Peek() {
      if ((this).EOF_q) {
        return (short)(-1);
      } else {
        return (short)((this).SuffixAt(0U));
      }
    }
    public bool LookingAt(char c) {
      return ((this).Peek()) == ((short)(c));
    }
    public JSON_mUtils_mCursors_Compile._ICursor__ Skip(uint n) {
      JSON_mUtils_mCursors_Compile._ICursor__ _389_dt__update__tmp_h0 = this;
      uint _390_dt__update_hpoint_h0 = ((this).dtor_point) + (n);
      return JSON_mUtils_mCursors_Compile.Cursor__.create((_389_dt__update__tmp_h0).dtor_s, (_389_dt__update__tmp_h0).dtor_beg, _390_dt__update_hpoint_h0, (_389_dt__update__tmp_h0).dtor_end);
    }
    public JSON_mUtils_mCursors_Compile._ICursor__ Unskip(uint n) {
      JSON_mUtils_mCursors_Compile._ICursor__ _391_dt__update__tmp_h0 = this;
      uint _392_dt__update_hpoint_h0 = ((this).dtor_point) - (n);
      return JSON_mUtils_mCursors_Compile.Cursor__.create((_391_dt__update__tmp_h0).dtor_s, (_391_dt__update__tmp_h0).dtor_beg, _392_dt__update_hpoint_h0, (_391_dt__update__tmp_h0).dtor_end);
    }
    public Wrappers_Compile._IResult<JSON_mUtils_mCursors_Compile._ICursor__, JSON_mUtils_mCursors_Compile._ICursorError<__R>> Get<__R>(__R err) {
      if ((this).EOF_q) {
        return Wrappers_Compile.Result<JSON_mUtils_mCursors_Compile._ICursor__, JSON_mUtils_mCursors_Compile._ICursorError<__R>>.create_Failure(JSON_mUtils_mCursors_Compile.CursorError<__R>.create_OtherError(err));
      } else {
        return Wrappers_Compile.Result<JSON_mUtils_mCursors_Compile._ICursor__, JSON_mUtils_mCursors_Compile._ICursorError<__R>>.create_Success((this).Skip(1U));
      }
    }
    public Wrappers_Compile._IResult<JSON_mUtils_mCursors_Compile._ICursor__, JSON_mUtils_mCursors_Compile._ICursorError<__R>> AssertByte<__R>(byte b) {
      short _393_nxt = (this).Peek();
      if ((_393_nxt) == ((short)(b))) {
        return Wrappers_Compile.Result<JSON_mUtils_mCursors_Compile._ICursor__, JSON_mUtils_mCursors_Compile._ICursorError<__R>>.create_Success((this).Skip(1U));
      } else {
        return Wrappers_Compile.Result<JSON_mUtils_mCursors_Compile._ICursor__, JSON_mUtils_mCursors_Compile._ICursorError<__R>>.create_Failure(JSON_mUtils_mCursors_Compile.CursorError<__R>.create_ExpectingByte(b, _393_nxt));
      }
    }
    public Wrappers_Compile._IResult<JSON_mUtils_mCursors_Compile._ICursor__, JSON_mUtils_mCursors_Compile._ICursorError<__R>> AssertBytes<__R>(Dafny.ISequence<byte> bs, uint offset)
    {
      _ICursor__ _this = this;
    TAIL_CALL_START: ;
      if ((offset) == ((uint)(bs).LongCount)) {
        return Wrappers_Compile.Result<JSON_mUtils_mCursors_Compile._ICursor__, JSON_mUtils_mCursors_Compile._ICursorError<__R>>.create_Success(_this);
      } else {
        Wrappers_Compile._IResult<JSON_mUtils_mCursors_Compile._ICursor__, JSON_mUtils_mCursors_Compile._ICursorError<__R>> _394_valueOrError0 = (_this).AssertByte<__R>((byte)((bs).Select(offset)));
        if ((_394_valueOrError0).IsFailure()) {
          return (_394_valueOrError0).PropagateFailure<JSON_mUtils_mCursors_Compile._ICursor__>();
        } else {
          JSON_mUtils_mCursors_Compile._ICursor__ _395_ps = (_394_valueOrError0).Extract();
          var _in98 = _395_ps;
          Dafny.ISequence<byte> _in99 = bs;
          uint _in100 = (offset) + (1U);
          _this = _in98;
          bs = _in99;
          offset = _in100;
          goto TAIL_CALL_START;
        }
      }
    }
    public Wrappers_Compile._IResult<JSON_mUtils_mCursors_Compile._ICursor__, JSON_mUtils_mCursors_Compile._ICursorError<__R>> AssertChar<__R>(char c0) {
      return (this).AssertByte<__R>((byte)(c0));
    }
    public JSON_mUtils_mCursors_Compile._ICursor__ SkipByte() {
      if ((this).EOF_q) {
        return this;
      } else {
        return (this).Skip(1U);
      }
    }
    public JSON_mUtils_mCursors_Compile._ICursor__ SkipIf(Func<byte, bool> p) {
      if (((this).EOF_q) || (!(Dafny.Helpers.Id<Func<byte, bool>>(p)((this).SuffixAt(0U))))) {
        return this;
      } else {
        return (this).Skip(1U);
      }
    }
    public JSON_mUtils_mCursors_Compile._ICursor__ SkipWhile(Func<byte, bool> p)
    {
      JSON_mUtils_mCursors_Compile._ICursor__ ps = JSON_mUtils_mCursors_Compile.Cursor.Default();
      uint _396_point_k;
      _396_point_k = (this).dtor_point;
      uint _397_end;
      _397_end = (this).dtor_end;
      while (((_396_point_k) < (_397_end)) && (Dafny.Helpers.Id<Func<byte, bool>>(p)(((this).dtor_s).Select(_396_point_k)))) {
        _396_point_k = (_396_point_k) + (1U);
      }
      ps = JSON_mUtils_mCursors_Compile.Cursor__.create((this).dtor_s, (this).dtor_beg, _396_point_k, (this).dtor_end);
      return ps;
      return ps;
    }
    public Wrappers_Compile._IResult<JSON_mUtils_mCursors_Compile._ICursor__, JSON_mUtils_mCursors_Compile._ICursorError<__R>> SkipWhileLexer<__A, __R>(Func<__A, short, JSON_mUtils_mLexers_mCore_Compile._ILexerResult<__A, __R>> step, __A st)
    {
      Wrappers_Compile._IResult<JSON_mUtils_mCursors_Compile._ICursor__, JSON_mUtils_mCursors_Compile._ICursorError<__R>> pr = Wrappers_Compile.Result<JSON_mUtils_mCursors_Compile._ICursor__, JSON_mUtils_mCursors_Compile._ICursorError<__R>>.Default(JSON_mUtils_mCursors_Compile.Cursor.Default());
      uint _398_point_k;
      _398_point_k = (this).dtor_point;
      uint _399_end;
      _399_end = (this).dtor_end;
      __A _400_st_k;
      _400_st_k = st;
      while (true) {
        bool _401_eof;
        _401_eof = (_398_point_k) == (_399_end);
        short _402_minusone;
        _402_minusone = (short)(-1);
        short _403_c;
        _403_c = ((_401_eof) ? (_402_minusone) : ((short)(((this).dtor_s).Select(_398_point_k))));
        JSON_mUtils_mLexers_mCore_Compile._ILexerResult<__A, __R> _source8 = Dafny.Helpers.Id<Func<__A, short, JSON_mUtils_mLexers_mCore_Compile._ILexerResult<__A, __R>>>(step)(_400_st_k, _403_c);
        if (_source8.is_Accept) {
          pr = Wrappers_Compile.Result<JSON_mUtils_mCursors_Compile._ICursor__, JSON_mUtils_mCursors_Compile._ICursorError<__R>>.create_Success(JSON_mUtils_mCursors_Compile.Cursor__.create((this).dtor_s, (this).dtor_beg, _398_point_k, (this).dtor_end));
          return pr;
        } else if (_source8.is_Reject) {
          __R _404___mcc_h0 = _source8.dtor_err;
          __R _405_err = _404___mcc_h0;
          pr = Wrappers_Compile.Result<JSON_mUtils_mCursors_Compile._ICursor__, JSON_mUtils_mCursors_Compile._ICursorError<__R>>.create_Failure(JSON_mUtils_mCursors_Compile.CursorError<__R>.create_OtherError(_405_err));
          return pr;
        } else {
          __A _406___mcc_h1 = _source8.dtor_st;
          __A _407_st_k_k = _406___mcc_h1;
          if (_401_eof) {
            pr = Wrappers_Compile.Result<JSON_mUtils_mCursors_Compile._ICursor__, JSON_mUtils_mCursors_Compile._ICursorError<__R>>.create_Failure(JSON_mUtils_mCursors_Compile.CursorError<__R>.create_EOF());
            return pr;
          } else {
            _400_st_k = _407_st_k_k;
            _398_point_k = (_398_point_k) + (1U);
          }
        }
      }
      return pr;
    }
    public bool BOF_q { get {
      return ((this).dtor_point) == ((this).dtor_beg);
    } }
    public bool EOF_q { get {
      return ((this).dtor_point) == ((this).dtor_end);
    } }
  }

} // end of namespace JSON_mUtils_mCursors_Compile
namespace JSON_mUtils_mParsers_Compile {

  public partial class Parser<T, R> {
    public static JSON_mUtils_mParsers_Compile._IParser__<T, R> Default() {
      return JSON_mUtils_mParsers_Compile.__default.ParserWitness<T, R>();
    }
    public static Dafny.TypeDescriptor<JSON_mUtils_mParsers_Compile._IParser__<T, R>> _TypeDescriptor(Dafny.TypeDescriptor<T> _td_T, Dafny.TypeDescriptor<R> _td_R) {
      return new Dafny.TypeDescriptor<JSON_mUtils_mParsers_Compile._IParser__<T, R>>(JSON_mUtils_mParsers_Compile.Parser<T, R>.Default());
    }
  }

  public interface _IParser__<T, out R> {
    bool is_Parser { get; }
    Func<JSON_mUtils_mCursors_Compile._ICursor__, Wrappers_Compile._IResult<JSON_mUtils_mCursors_Compile._ISplit<T>, JSON_mUtils_mCursors_Compile._ICursorError<R>>> dtor_fn { get; }
    _IParser__<__T, __R> DowncastClone<__T, __R>(Func<T, __T> converter0, Func<R, __R> converter1);
  }
  public class Parser__<T, R> : _IParser__<T, R> {
    public readonly Func<JSON_mUtils_mCursors_Compile._ICursor__, Wrappers_Compile._IResult<JSON_mUtils_mCursors_Compile._ISplit<T>, JSON_mUtils_mCursors_Compile._ICursorError<R>>> _fn;
    public Parser__(Func<JSON_mUtils_mCursors_Compile._ICursor__, Wrappers_Compile._IResult<JSON_mUtils_mCursors_Compile._ISplit<T>, JSON_mUtils_mCursors_Compile._ICursorError<R>>> fn) {
      this._fn = fn;
    }
    public _IParser__<__T, __R> DowncastClone<__T, __R>(Func<T, __T> converter0, Func<R, __R> converter1) {
      if (this is _IParser__<__T, __R> dt) { return dt; }
      return new Parser__<__T, __R>((_fn).DowncastClone<JSON_mUtils_mCursors_Compile._ICursor__, Wrappers_Compile._IResult<JSON_mUtils_mCursors_Compile._ISplit<T>, JSON_mUtils_mCursors_Compile._ICursorError<R>>, JSON_mUtils_mCursors_Compile._ICursor__, Wrappers_Compile._IResult<JSON_mUtils_mCursors_Compile._ISplit<__T>, JSON_mUtils_mCursors_Compile._ICursorError<__R>>>(Dafny.Helpers.Id<JSON_mUtils_mCursors_Compile._ICursor__>, Dafny.Helpers.CastConverter<Wrappers_Compile._IResult<JSON_mUtils_mCursors_Compile._ISplit<T>, JSON_mUtils_mCursors_Compile._ICursorError<R>>, Wrappers_Compile._IResult<JSON_mUtils_mCursors_Compile._ISplit<__T>, JSON_mUtils_mCursors_Compile._ICursorError<__R>>>));
    }
    public override bool Equals(object other) {
      var oth = other as JSON_mUtils_mParsers_Compile.Parser__<T, R>;
      return oth != null && object.Equals(this._fn, oth._fn);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._fn));
      return (int) hash;
    }
    public override string ToString() {
      string s = "JSON_mUtils_mParsers_Compile.Parser_.Parser";
      s += "(";
      s += Dafny.Helpers.ToString(this._fn);
      s += ")";
      return s;
    }
    public static JSON_mUtils_mParsers_Compile._IParser__<T, R> Default(T _default_T) {
      return create(((JSON_mUtils_mCursors_Compile._ICursor__ x0) => Wrappers_Compile.Result<JSON_mUtils_mCursors_Compile._ISplit<T>, JSON_mUtils_mCursors_Compile._ICursorError<R>>.Default(JSON_mUtils_mCursors_Compile.Split<T>.Default(_default_T))));
    }
    public static Dafny.TypeDescriptor<JSON_mUtils_mParsers_Compile._IParser__<T, R>> _TypeDescriptor(Dafny.TypeDescriptor<T> _td_T) {
      return new Dafny.TypeDescriptor<JSON_mUtils_mParsers_Compile._IParser__<T, R>>(JSON_mUtils_mParsers_Compile.Parser__<T, R>.Default(_td_T.Default()));
    }
    public static _IParser__<T, R> create(Func<JSON_mUtils_mCursors_Compile._ICursor__, Wrappers_Compile._IResult<JSON_mUtils_mCursors_Compile._ISplit<T>, JSON_mUtils_mCursors_Compile._ICursorError<R>>> fn) {
      return new Parser__<T, R>(fn);
    }
    public static _IParser__<T, R> create_Parser(Func<JSON_mUtils_mCursors_Compile._ICursor__, Wrappers_Compile._IResult<JSON_mUtils_mCursors_Compile._ISplit<T>, JSON_mUtils_mCursors_Compile._ICursorError<R>>> fn) {
      return create(fn);
    }
    public bool is_Parser { get { return true; } }
    public Func<JSON_mUtils_mCursors_Compile._ICursor__, Wrappers_Compile._IResult<JSON_mUtils_mCursors_Compile._ISplit<T>, JSON_mUtils_mCursors_Compile._ICursorError<R>>> dtor_fn {
      get {
        return this._fn;
      }
    }
  }

  public interface _ISubParser__<T, out R> {
    bool is_SubParser { get; }
    Func<JSON_mUtils_mCursors_Compile._ICursor__, Wrappers_Compile._IResult<JSON_mUtils_mCursors_Compile._ISplit<T>, JSON_mUtils_mCursors_Compile._ICursorError<R>>> dtor_fn { get; }
    _ISubParser__<__T, __R> DowncastClone<__T, __R>(Func<T, __T> converter0, Func<R, __R> converter1);
  }
  public class SubParser__<T, R> : _ISubParser__<T, R> {
    public readonly Func<JSON_mUtils_mCursors_Compile._ICursor__, Wrappers_Compile._IResult<JSON_mUtils_mCursors_Compile._ISplit<T>, JSON_mUtils_mCursors_Compile._ICursorError<R>>> _fn;
    public SubParser__(Func<JSON_mUtils_mCursors_Compile._ICursor__, Wrappers_Compile._IResult<JSON_mUtils_mCursors_Compile._ISplit<T>, JSON_mUtils_mCursors_Compile._ICursorError<R>>> fn) {
      this._fn = fn;
    }
    public _ISubParser__<__T, __R> DowncastClone<__T, __R>(Func<T, __T> converter0, Func<R, __R> converter1) {
      if (this is _ISubParser__<__T, __R> dt) { return dt; }
      return new SubParser__<__T, __R>((_fn).DowncastClone<JSON_mUtils_mCursors_Compile._ICursor__, Wrappers_Compile._IResult<JSON_mUtils_mCursors_Compile._ISplit<T>, JSON_mUtils_mCursors_Compile._ICursorError<R>>, JSON_mUtils_mCursors_Compile._ICursor__, Wrappers_Compile._IResult<JSON_mUtils_mCursors_Compile._ISplit<__T>, JSON_mUtils_mCursors_Compile._ICursorError<__R>>>(Dafny.Helpers.Id<JSON_mUtils_mCursors_Compile._ICursor__>, Dafny.Helpers.CastConverter<Wrappers_Compile._IResult<JSON_mUtils_mCursors_Compile._ISplit<T>, JSON_mUtils_mCursors_Compile._ICursorError<R>>, Wrappers_Compile._IResult<JSON_mUtils_mCursors_Compile._ISplit<__T>, JSON_mUtils_mCursors_Compile._ICursorError<__R>>>));
    }
    public override bool Equals(object other) {
      var oth = other as JSON_mUtils_mParsers_Compile.SubParser__<T, R>;
      return oth != null && object.Equals(this._fn, oth._fn);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._fn));
      return (int) hash;
    }
    public override string ToString() {
      string s = "JSON_mUtils_mParsers_Compile.SubParser_.SubParser";
      s += "(";
      s += Dafny.Helpers.ToString(this._fn);
      s += ")";
      return s;
    }
    public static JSON_mUtils_mParsers_Compile._ISubParser__<T, R> Default() {
      return create(((Func<JSON_mUtils_mCursors_Compile._ICursor__, Wrappers_Compile._IResult<JSON_mUtils_mCursors_Compile._ISplit<T>, JSON_mUtils_mCursors_Compile._ICursorError<R>>>)null));
    }
    public static Dafny.TypeDescriptor<JSON_mUtils_mParsers_Compile._ISubParser__<T, R>> _TypeDescriptor() {
      return new Dafny.TypeDescriptor<JSON_mUtils_mParsers_Compile._ISubParser__<T, R>>(JSON_mUtils_mParsers_Compile.SubParser__<T, R>.Default());
    }
    public static _ISubParser__<T, R> create(Func<JSON_mUtils_mCursors_Compile._ICursor__, Wrappers_Compile._IResult<JSON_mUtils_mCursors_Compile._ISplit<T>, JSON_mUtils_mCursors_Compile._ICursorError<R>>> fn) {
      return new SubParser__<T, R>(fn);
    }
    public static _ISubParser__<T, R> create_SubParser(Func<JSON_mUtils_mCursors_Compile._ICursor__, Wrappers_Compile._IResult<JSON_mUtils_mCursors_Compile._ISplit<T>, JSON_mUtils_mCursors_Compile._ICursorError<R>>> fn) {
      return create(fn);
    }
    public bool is_SubParser { get { return true; } }
    public Func<JSON_mUtils_mCursors_Compile._ICursor__, Wrappers_Compile._IResult<JSON_mUtils_mCursors_Compile._ISplit<T>, JSON_mUtils_mCursors_Compile._ICursorError<R>>> dtor_fn {
      get {
        return this._fn;
      }
    }
  }

  public partial class SubParser<T, R> {
    public static JSON_mUtils_mParsers_Compile._ISubParser__<T, R> Default() {
      return JSON_mUtils_mParsers_Compile.__default.SubParserWitness<T, R>();
    }
    public static Dafny.TypeDescriptor<JSON_mUtils_mParsers_Compile._ISubParser__<T, R>> _TypeDescriptor(Dafny.TypeDescriptor<T> _td_T, Dafny.TypeDescriptor<R> _td_R) {
      return new Dafny.TypeDescriptor<JSON_mUtils_mParsers_Compile._ISubParser__<T, R>>(JSON_mUtils_mParsers_Compile.SubParser<T, R>.Default());
    }
  }

  public partial class __default {
    public static JSON_mUtils_mParsers_Compile._IParser__<__T, __R> ParserWitness<__T, __R>() {
      return JSON_mUtils_mParsers_Compile.Parser__<__T, __R>.create(((System.Func<JSON_mUtils_mCursors_Compile._ICursor__, Wrappers_Compile._IResult<JSON_mUtils_mCursors_Compile._ISplit<__T>, JSON_mUtils_mCursors_Compile._ICursorError<__R>>>)((_408___v0) => {
  return Wrappers_Compile.Result<JSON_mUtils_mCursors_Compile._ISplit<__T>, JSON_mUtils_mCursors_Compile._ICursorError<__R>>.create_Failure(JSON_mUtils_mCursors_Compile.CursorError<__R>.create_EOF());
})));
    }
    public static JSON_mUtils_mParsers_Compile._ISubParser__<__T, __R> SubParserWitness<__T, __R>() {
      return JSON_mUtils_mParsers_Compile.SubParser__<__T, __R>.create(((System.Func<JSON_mUtils_mCursors_Compile._ICursor__, Wrappers_Compile._IResult<JSON_mUtils_mCursors_Compile._ISplit<__T>, JSON_mUtils_mCursors_Compile._ICursorError<__R>>>)((_409_cs) => {
  return Wrappers_Compile.Result<JSON_mUtils_mCursors_Compile._ISplit<__T>, JSON_mUtils_mCursors_Compile._ICursorError<__R>>.create_Failure(JSON_mUtils_mCursors_Compile.CursorError<__R>.create_EOF());
})));
    }
  }
} // end of namespace JSON_mUtils_mParsers_Compile
namespace JSON_mUtils_Compile {

} // end of namespace JSON_mUtils_Compile
namespace JSON_mErrors_Compile {

  public interface _IDeserializationError {
    bool is_UnterminatedSequence { get; }
    bool is_UnsupportedEscape { get; }
    bool is_EscapeAtEOS { get; }
    bool is_EmptyNumber { get; }
    bool is_ExpectingEOF { get; }
    bool is_IntOverflow { get; }
    bool is_ReachedEOF { get; }
    bool is_ExpectingByte { get; }
    bool is_ExpectingAnyByte { get; }
    bool is_InvalidUnicode { get; }
    Dafny.ISequence<char> dtor_str { get; }
    byte dtor_expected { get; }
    short dtor_b { get; }
    Dafny.ISequence<byte> dtor_expected__sq { get; }
    _IDeserializationError DowncastClone();
    Dafny.ISequence<char> _ToString();
  }
  public abstract class DeserializationError : _IDeserializationError {
    public DeserializationError() { }
    private static readonly JSON_mErrors_Compile._IDeserializationError theDefault = create_UnterminatedSequence();
    public static JSON_mErrors_Compile._IDeserializationError Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<JSON_mErrors_Compile._IDeserializationError> _TYPE = new Dafny.TypeDescriptor<JSON_mErrors_Compile._IDeserializationError>(JSON_mErrors_Compile.DeserializationError.Default());
    public static Dafny.TypeDescriptor<JSON_mErrors_Compile._IDeserializationError> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IDeserializationError create_UnterminatedSequence() {
      return new DeserializationError_UnterminatedSequence();
    }
    public static _IDeserializationError create_UnsupportedEscape(Dafny.ISequence<char> str) {
      return new DeserializationError_UnsupportedEscape(str);
    }
    public static _IDeserializationError create_EscapeAtEOS() {
      return new DeserializationError_EscapeAtEOS();
    }
    public static _IDeserializationError create_EmptyNumber() {
      return new DeserializationError_EmptyNumber();
    }
    public static _IDeserializationError create_ExpectingEOF() {
      return new DeserializationError_ExpectingEOF();
    }
    public static _IDeserializationError create_IntOverflow() {
      return new DeserializationError_IntOverflow();
    }
    public static _IDeserializationError create_ReachedEOF() {
      return new DeserializationError_ReachedEOF();
    }
    public static _IDeserializationError create_ExpectingByte(byte expected, short b) {
      return new DeserializationError_ExpectingByte(expected, b);
    }
    public static _IDeserializationError create_ExpectingAnyByte(Dafny.ISequence<byte> expected__sq, short b) {
      return new DeserializationError_ExpectingAnyByte(expected__sq, b);
    }
    public static _IDeserializationError create_InvalidUnicode() {
      return new DeserializationError_InvalidUnicode();
    }
    public bool is_UnterminatedSequence { get { return this is DeserializationError_UnterminatedSequence; } }
    public bool is_UnsupportedEscape { get { return this is DeserializationError_UnsupportedEscape; } }
    public bool is_EscapeAtEOS { get { return this is DeserializationError_EscapeAtEOS; } }
    public bool is_EmptyNumber { get { return this is DeserializationError_EmptyNumber; } }
    public bool is_ExpectingEOF { get { return this is DeserializationError_ExpectingEOF; } }
    public bool is_IntOverflow { get { return this is DeserializationError_IntOverflow; } }
    public bool is_ReachedEOF { get { return this is DeserializationError_ReachedEOF; } }
    public bool is_ExpectingByte { get { return this is DeserializationError_ExpectingByte; } }
    public bool is_ExpectingAnyByte { get { return this is DeserializationError_ExpectingAnyByte; } }
    public bool is_InvalidUnicode { get { return this is DeserializationError_InvalidUnicode; } }
    public Dafny.ISequence<char> dtor_str {
      get {
        var d = this;
        return ((DeserializationError_UnsupportedEscape)d)._str;
      }
    }
    public byte dtor_expected {
      get {
        var d = this;
        return ((DeserializationError_ExpectingByte)d)._expected;
      }
    }
    public short dtor_b {
      get {
        var d = this;
        if (d is DeserializationError_ExpectingByte) { return ((DeserializationError_ExpectingByte)d)._b; }
        return ((DeserializationError_ExpectingAnyByte)d)._b;
      }
    }
    public Dafny.ISequence<byte> dtor_expected__sq {
      get {
        var d = this;
        return ((DeserializationError_ExpectingAnyByte)d)._expected__sq;
      }
    }
    public abstract _IDeserializationError DowncastClone();
    public Dafny.ISequence<char> _ToString() {
      JSON_mErrors_Compile._IDeserializationError _source9 = this;
      if (_source9.is_UnterminatedSequence) {
        return Dafny.Sequence<char>.FromString("Unterminated sequence");
      } else if (_source9.is_UnsupportedEscape) {
        Dafny.ISequence<char> _410___mcc_h0 = _source9.dtor_str;
        Dafny.ISequence<char> _411_str = _410___mcc_h0;
        return Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.FromString("Unsupported escape sequence: "), _411_str);
      } else if (_source9.is_EscapeAtEOS) {
        return Dafny.Sequence<char>.FromString("Escape character at end of string");
      } else if (_source9.is_EmptyNumber) {
        return Dafny.Sequence<char>.FromString("Number must contain at least one digit");
      } else if (_source9.is_ExpectingEOF) {
        return Dafny.Sequence<char>.FromString("Expecting EOF");
      } else if (_source9.is_IntOverflow) {
        return Dafny.Sequence<char>.FromString("Input length does not fit in a 32-bit counter");
      } else if (_source9.is_ReachedEOF) {
        return Dafny.Sequence<char>.FromString("Reached EOF");
      } else if (_source9.is_ExpectingByte) {
        byte _412___mcc_h1 = _source9.dtor_expected;
        short _413___mcc_h2 = _source9.dtor_b;
        short _414_b = _413___mcc_h2;
        byte _415_b0 = _412___mcc_h1;
        Dafny.ISequence<char> _416_c = (((_414_b) > ((short)(0))) ? (Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.FromString("'"), Dafny.Sequence<char>.FromElements((char)(_414_b))), Dafny.Sequence<char>.FromString("'"))) : (Dafny.Sequence<char>.FromString("EOF")));
        return Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.FromString("Expecting '"), Dafny.Sequence<char>.FromElements((char)(_415_b0))), Dafny.Sequence<char>.FromString("', read ")), _416_c);
      } else if (_source9.is_ExpectingAnyByte) {
        Dafny.ISequence<byte> _417___mcc_h3 = _source9.dtor_expected__sq;
        short _418___mcc_h4 = _source9.dtor_b;
        short _419_b = _418___mcc_h4;
        Dafny.ISequence<byte> _420_bs0 = _417___mcc_h3;
        Dafny.ISequence<char> _421_c = (((_419_b) > ((short)(0))) ? (Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.FromString("'"), Dafny.Sequence<char>.FromElements((char)(_419_b))), Dafny.Sequence<char>.FromString("'"))) : (Dafny.Sequence<char>.FromString("EOF")));
        Dafny.ISequence<char> _422_c0s = ((System.Func<Dafny.ISequence<char>>) (() => {
          BigInteger dim7 = new BigInteger((_420_bs0).Count);
          var arr7 = new char[Dafny.Helpers.ToIntChecked(dim7, "array size exceeds memory limit")];
          for (int i7 = 0; i7 < dim7; i7++) {
            var _423_idx = (BigInteger) i7;
            arr7[(int)(_423_idx)] = (char)((_420_bs0).Select(_423_idx));
          }
          return Dafny.Sequence<char>.FromArray(arr7);
        }))();
        return Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.FromString("Expecting one of '"), _422_c0s), Dafny.Sequence<char>.FromString("', read ")), _421_c);
      } else {
        return Dafny.Sequence<char>.FromString("Invalid Unicode sequence");
      }
    }
  }
  public class DeserializationError_UnterminatedSequence : DeserializationError {
    public DeserializationError_UnterminatedSequence() {
    }
    public override _IDeserializationError DowncastClone() {
      if (this is _IDeserializationError dt) { return dt; }
      return new DeserializationError_UnterminatedSequence();
    }
    public override bool Equals(object other) {
      var oth = other as JSON_mErrors_Compile.DeserializationError_UnterminatedSequence;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "JSON_mErrors_Compile.DeserializationError.UnterminatedSequence";
      return s;
    }
  }
  public class DeserializationError_UnsupportedEscape : DeserializationError {
    public readonly Dafny.ISequence<char> _str;
    public DeserializationError_UnsupportedEscape(Dafny.ISequence<char> str) {
      this._str = str;
    }
    public override _IDeserializationError DowncastClone() {
      if (this is _IDeserializationError dt) { return dt; }
      return new DeserializationError_UnsupportedEscape(_str);
    }
    public override bool Equals(object other) {
      var oth = other as JSON_mErrors_Compile.DeserializationError_UnsupportedEscape;
      return oth != null && object.Equals(this._str, oth._str);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._str));
      return (int) hash;
    }
    public override string ToString() {
      string s = "JSON_mErrors_Compile.DeserializationError.UnsupportedEscape";
      s += "(";
      s += Dafny.Helpers.ToString(this._str);
      s += ")";
      return s;
    }
  }
  public class DeserializationError_EscapeAtEOS : DeserializationError {
    public DeserializationError_EscapeAtEOS() {
    }
    public override _IDeserializationError DowncastClone() {
      if (this is _IDeserializationError dt) { return dt; }
      return new DeserializationError_EscapeAtEOS();
    }
    public override bool Equals(object other) {
      var oth = other as JSON_mErrors_Compile.DeserializationError_EscapeAtEOS;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 2;
      return (int) hash;
    }
    public override string ToString() {
      string s = "JSON_mErrors_Compile.DeserializationError.EscapeAtEOS";
      return s;
    }
  }
  public class DeserializationError_EmptyNumber : DeserializationError {
    public DeserializationError_EmptyNumber() {
    }
    public override _IDeserializationError DowncastClone() {
      if (this is _IDeserializationError dt) { return dt; }
      return new DeserializationError_EmptyNumber();
    }
    public override bool Equals(object other) {
      var oth = other as JSON_mErrors_Compile.DeserializationError_EmptyNumber;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 3;
      return (int) hash;
    }
    public override string ToString() {
      string s = "JSON_mErrors_Compile.DeserializationError.EmptyNumber";
      return s;
    }
  }
  public class DeserializationError_ExpectingEOF : DeserializationError {
    public DeserializationError_ExpectingEOF() {
    }
    public override _IDeserializationError DowncastClone() {
      if (this is _IDeserializationError dt) { return dt; }
      return new DeserializationError_ExpectingEOF();
    }
    public override bool Equals(object other) {
      var oth = other as JSON_mErrors_Compile.DeserializationError_ExpectingEOF;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 4;
      return (int) hash;
    }
    public override string ToString() {
      string s = "JSON_mErrors_Compile.DeserializationError.ExpectingEOF";
      return s;
    }
  }
  public class DeserializationError_IntOverflow : DeserializationError {
    public DeserializationError_IntOverflow() {
    }
    public override _IDeserializationError DowncastClone() {
      if (this is _IDeserializationError dt) { return dt; }
      return new DeserializationError_IntOverflow();
    }
    public override bool Equals(object other) {
      var oth = other as JSON_mErrors_Compile.DeserializationError_IntOverflow;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 5;
      return (int) hash;
    }
    public override string ToString() {
      string s = "JSON_mErrors_Compile.DeserializationError.IntOverflow";
      return s;
    }
  }
  public class DeserializationError_ReachedEOF : DeserializationError {
    public DeserializationError_ReachedEOF() {
    }
    public override _IDeserializationError DowncastClone() {
      if (this is _IDeserializationError dt) { return dt; }
      return new DeserializationError_ReachedEOF();
    }
    public override bool Equals(object other) {
      var oth = other as JSON_mErrors_Compile.DeserializationError_ReachedEOF;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 6;
      return (int) hash;
    }
    public override string ToString() {
      string s = "JSON_mErrors_Compile.DeserializationError.ReachedEOF";
      return s;
    }
  }
  public class DeserializationError_ExpectingByte : DeserializationError {
    public readonly byte _expected;
    public readonly short _b;
    public DeserializationError_ExpectingByte(byte expected, short b) {
      this._expected = expected;
      this._b = b;
    }
    public override _IDeserializationError DowncastClone() {
      if (this is _IDeserializationError dt) { return dt; }
      return new DeserializationError_ExpectingByte(_expected, _b);
    }
    public override bool Equals(object other) {
      var oth = other as JSON_mErrors_Compile.DeserializationError_ExpectingByte;
      return oth != null && this._expected == oth._expected && this._b == oth._b;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 7;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._expected));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._b));
      return (int) hash;
    }
    public override string ToString() {
      string s = "JSON_mErrors_Compile.DeserializationError.ExpectingByte";
      s += "(";
      s += Dafny.Helpers.ToString(this._expected);
      s += ", ";
      s += Dafny.Helpers.ToString(this._b);
      s += ")";
      return s;
    }
  }
  public class DeserializationError_ExpectingAnyByte : DeserializationError {
    public readonly Dafny.ISequence<byte> _expected__sq;
    public readonly short _b;
    public DeserializationError_ExpectingAnyByte(Dafny.ISequence<byte> expected__sq, short b) {
      this._expected__sq = expected__sq;
      this._b = b;
    }
    public override _IDeserializationError DowncastClone() {
      if (this is _IDeserializationError dt) { return dt; }
      return new DeserializationError_ExpectingAnyByte(_expected__sq, _b);
    }
    public override bool Equals(object other) {
      var oth = other as JSON_mErrors_Compile.DeserializationError_ExpectingAnyByte;
      return oth != null && object.Equals(this._expected__sq, oth._expected__sq) && this._b == oth._b;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 8;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._expected__sq));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._b));
      return (int) hash;
    }
    public override string ToString() {
      string s = "JSON_mErrors_Compile.DeserializationError.ExpectingAnyByte";
      s += "(";
      s += Dafny.Helpers.ToString(this._expected__sq);
      s += ", ";
      s += Dafny.Helpers.ToString(this._b);
      s += ")";
      return s;
    }
  }
  public class DeserializationError_InvalidUnicode : DeserializationError {
    public DeserializationError_InvalidUnicode() {
    }
    public override _IDeserializationError DowncastClone() {
      if (this is _IDeserializationError dt) { return dt; }
      return new DeserializationError_InvalidUnicode();
    }
    public override bool Equals(object other) {
      var oth = other as JSON_mErrors_Compile.DeserializationError_InvalidUnicode;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 9;
      return (int) hash;
    }
    public override string ToString() {
      string s = "JSON_mErrors_Compile.DeserializationError.InvalidUnicode";
      return s;
    }
  }

  public interface _ISerializationError {
    bool is_OutOfMemory { get; }
    bool is_IntTooLarge { get; }
    bool is_StringTooLong { get; }
    bool is_InvalidUnicode { get; }
    BigInteger dtor_i { get; }
    Dafny.ISequence<char> dtor_s { get; }
    _ISerializationError DowncastClone();
    Dafny.ISequence<char> _ToString();
  }
  public abstract class SerializationError : _ISerializationError {
    public SerializationError() { }
    private static readonly JSON_mErrors_Compile._ISerializationError theDefault = create_OutOfMemory();
    public static JSON_mErrors_Compile._ISerializationError Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<JSON_mErrors_Compile._ISerializationError> _TYPE = new Dafny.TypeDescriptor<JSON_mErrors_Compile._ISerializationError>(JSON_mErrors_Compile.SerializationError.Default());
    public static Dafny.TypeDescriptor<JSON_mErrors_Compile._ISerializationError> _TypeDescriptor() {
      return _TYPE;
    }
    public static _ISerializationError create_OutOfMemory() {
      return new SerializationError_OutOfMemory();
    }
    public static _ISerializationError create_IntTooLarge(BigInteger i) {
      return new SerializationError_IntTooLarge(i);
    }
    public static _ISerializationError create_StringTooLong(Dafny.ISequence<char> s) {
      return new SerializationError_StringTooLong(s);
    }
    public static _ISerializationError create_InvalidUnicode() {
      return new SerializationError_InvalidUnicode();
    }
    public bool is_OutOfMemory { get { return this is SerializationError_OutOfMemory; } }
    public bool is_IntTooLarge { get { return this is SerializationError_IntTooLarge; } }
    public bool is_StringTooLong { get { return this is SerializationError_StringTooLong; } }
    public bool is_InvalidUnicode { get { return this is SerializationError_InvalidUnicode; } }
    public BigInteger dtor_i {
      get {
        var d = this;
        return ((SerializationError_IntTooLarge)d)._i;
      }
    }
    public Dafny.ISequence<char> dtor_s {
      get {
        var d = this;
        return ((SerializationError_StringTooLong)d)._s;
      }
    }
    public abstract _ISerializationError DowncastClone();
    public Dafny.ISequence<char> _ToString() {
      JSON_mErrors_Compile._ISerializationError _source10 = this;
      if (_source10.is_OutOfMemory) {
        return Dafny.Sequence<char>.FromString("Out of memory");
      } else if (_source10.is_IntTooLarge) {
        BigInteger _424___mcc_h0 = _source10.dtor_i;
        BigInteger _425_i = _424___mcc_h0;
        return Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.FromString("Integer too large: "), JSON_mUtils_mStr_Compile.__default.OfInt(_425_i, new BigInteger(10)));
      } else if (_source10.is_StringTooLong) {
        Dafny.ISequence<char> _426___mcc_h1 = _source10.dtor_s;
        Dafny.ISequence<char> _427_s = _426___mcc_h1;
        return Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.FromString("String too long: "), _427_s);
      } else {
        return Dafny.Sequence<char>.FromString("Invalid Unicode sequence");
      }
    }
  }
  public class SerializationError_OutOfMemory : SerializationError {
    public SerializationError_OutOfMemory() {
    }
    public override _ISerializationError DowncastClone() {
      if (this is _ISerializationError dt) { return dt; }
      return new SerializationError_OutOfMemory();
    }
    public override bool Equals(object other) {
      var oth = other as JSON_mErrors_Compile.SerializationError_OutOfMemory;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "JSON_mErrors_Compile.SerializationError.OutOfMemory";
      return s;
    }
  }
  public class SerializationError_IntTooLarge : SerializationError {
    public readonly BigInteger _i;
    public SerializationError_IntTooLarge(BigInteger i) {
      this._i = i;
    }
    public override _ISerializationError DowncastClone() {
      if (this is _ISerializationError dt) { return dt; }
      return new SerializationError_IntTooLarge(_i);
    }
    public override bool Equals(object other) {
      var oth = other as JSON_mErrors_Compile.SerializationError_IntTooLarge;
      return oth != null && this._i == oth._i;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._i));
      return (int) hash;
    }
    public override string ToString() {
      string s = "JSON_mErrors_Compile.SerializationError.IntTooLarge";
      s += "(";
      s += Dafny.Helpers.ToString(this._i);
      s += ")";
      return s;
    }
  }
  public class SerializationError_StringTooLong : SerializationError {
    public readonly Dafny.ISequence<char> _s;
    public SerializationError_StringTooLong(Dafny.ISequence<char> s) {
      this._s = s;
    }
    public override _ISerializationError DowncastClone() {
      if (this is _ISerializationError dt) { return dt; }
      return new SerializationError_StringTooLong(_s);
    }
    public override bool Equals(object other) {
      var oth = other as JSON_mErrors_Compile.SerializationError_StringTooLong;
      return oth != null && object.Equals(this._s, oth._s);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 2;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._s));
      return (int) hash;
    }
    public override string ToString() {
      string ss = "JSON_mErrors_Compile.SerializationError.StringTooLong";
      ss += "(";
      ss += Dafny.Helpers.ToString(this._s);
      ss += ")";
      return ss;
    }
  }
  public class SerializationError_InvalidUnicode : SerializationError {
    public SerializationError_InvalidUnicode() {
    }
    public override _ISerializationError DowncastClone() {
      if (this is _ISerializationError dt) { return dt; }
      return new SerializationError_InvalidUnicode();
    }
    public override bool Equals(object other) {
      var oth = other as JSON_mErrors_Compile.SerializationError_InvalidUnicode;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 3;
      return (int) hash;
    }
    public override string ToString() {
      string s = "JSON_mErrors_Compile.SerializationError.InvalidUnicode";
      return s;
    }
  }

} // end of namespace JSON_mErrors_Compile
namespace JSON_mValues_Compile {

  public interface _IDecimal {
    bool is_Decimal { get; }
    BigInteger dtor_n { get; }
    BigInteger dtor_e10 { get; }
    _IDecimal DowncastClone();
  }
  public class Decimal : _IDecimal {
    public readonly BigInteger _n;
    public readonly BigInteger _e10;
    public Decimal(BigInteger n, BigInteger e10) {
      this._n = n;
      this._e10 = e10;
    }
    public _IDecimal DowncastClone() {
      if (this is _IDecimal dt) { return dt; }
      return new Decimal(_n, _e10);
    }
    public override bool Equals(object other) {
      var oth = other as JSON_mValues_Compile.Decimal;
      return oth != null && this._n == oth._n && this._e10 == oth._e10;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._n));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._e10));
      return (int) hash;
    }
    public override string ToString() {
      string s = "JSON_mValues_Compile.Decimal.Decimal";
      s += "(";
      s += Dafny.Helpers.ToString(this._n);
      s += ", ";
      s += Dafny.Helpers.ToString(this._e10);
      s += ")";
      return s;
    }
    private static readonly JSON_mValues_Compile._IDecimal theDefault = create(BigInteger.Zero, BigInteger.Zero);
    public static JSON_mValues_Compile._IDecimal Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<JSON_mValues_Compile._IDecimal> _TYPE = new Dafny.TypeDescriptor<JSON_mValues_Compile._IDecimal>(JSON_mValues_Compile.Decimal.Default());
    public static Dafny.TypeDescriptor<JSON_mValues_Compile._IDecimal> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IDecimal create(BigInteger n, BigInteger e10) {
      return new Decimal(n, e10);
    }
    public static _IDecimal create_Decimal(BigInteger n, BigInteger e10) {
      return create(n, e10);
    }
    public bool is_Decimal { get { return true; } }
    public BigInteger dtor_n {
      get {
        return this._n;
      }
    }
    public BigInteger dtor_e10 {
      get {
        return this._e10;
      }
    }
  }

  public interface _IJSON {
    bool is_Null { get; }
    bool is_Bool { get; }
    bool is_String { get; }
    bool is_Number { get; }
    bool is_Object { get; }
    bool is_Array { get; }
    bool dtor_b { get; }
    Dafny.ISequence<char> dtor_str { get; }
    JSON_mValues_Compile._IDecimal dtor_num { get; }
    Dafny.ISequence<_System._ITuple2<Dafny.ISequence<char>, JSON_mValues_Compile._IJSON>> dtor_obj { get; }
    Dafny.ISequence<JSON_mValues_Compile._IJSON> dtor_arr { get; }
    _IJSON DowncastClone();
  }
  public abstract class JSON : _IJSON {
    public JSON() { }
    private static readonly JSON_mValues_Compile._IJSON theDefault = create_Null();
    public static JSON_mValues_Compile._IJSON Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<JSON_mValues_Compile._IJSON> _TYPE = new Dafny.TypeDescriptor<JSON_mValues_Compile._IJSON>(JSON_mValues_Compile.JSON.Default());
    public static Dafny.TypeDescriptor<JSON_mValues_Compile._IJSON> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IJSON create_Null() {
      return new JSON_Null();
    }
    public static _IJSON create_Bool(bool b) {
      return new JSON_Bool(b);
    }
    public static _IJSON create_String(Dafny.ISequence<char> str) {
      return new JSON_String(str);
    }
    public static _IJSON create_Number(JSON_mValues_Compile._IDecimal num) {
      return new JSON_Number(num);
    }
    public static _IJSON create_Object(Dafny.ISequence<_System._ITuple2<Dafny.ISequence<char>, JSON_mValues_Compile._IJSON>> obj) {
      return new JSON_Object(obj);
    }
    public static _IJSON create_Array(Dafny.ISequence<JSON_mValues_Compile._IJSON> arr) {
      return new JSON_Array(arr);
    }
    public bool is_Null { get { return this is JSON_Null; } }
    public bool is_Bool { get { return this is JSON_Bool; } }
    public bool is_String { get { return this is JSON_String; } }
    public bool is_Number { get { return this is JSON_Number; } }
    public bool is_Object { get { return this is JSON_Object; } }
    public bool is_Array { get { return this is JSON_Array; } }
    public bool dtor_b {
      get {
        var d = this;
        return ((JSON_Bool)d)._b;
      }
    }
    public Dafny.ISequence<char> dtor_str {
      get {
        var d = this;
        return ((JSON_String)d)._str;
      }
    }
    public JSON_mValues_Compile._IDecimal dtor_num {
      get {
        var d = this;
        return ((JSON_Number)d)._num;
      }
    }
    public Dafny.ISequence<_System._ITuple2<Dafny.ISequence<char>, JSON_mValues_Compile._IJSON>> dtor_obj {
      get {
        var d = this;
        return ((JSON_Object)d)._obj;
      }
    }
    public Dafny.ISequence<JSON_mValues_Compile._IJSON> dtor_arr {
      get {
        var d = this;
        return ((JSON_Array)d)._arr;
      }
    }
    public abstract _IJSON DowncastClone();
  }
  public class JSON_Null : JSON {
    public JSON_Null() {
    }
    public override _IJSON DowncastClone() {
      if (this is _IJSON dt) { return dt; }
      return new JSON_Null();
    }
    public override bool Equals(object other) {
      var oth = other as JSON_mValues_Compile.JSON_Null;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "JSON_mValues_Compile.JSON.Null";
      return s;
    }
  }
  public class JSON_Bool : JSON {
    public readonly bool _b;
    public JSON_Bool(bool b) {
      this._b = b;
    }
    public override _IJSON DowncastClone() {
      if (this is _IJSON dt) { return dt; }
      return new JSON_Bool(_b);
    }
    public override bool Equals(object other) {
      var oth = other as JSON_mValues_Compile.JSON_Bool;
      return oth != null && this._b == oth._b;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._b));
      return (int) hash;
    }
    public override string ToString() {
      string s = "JSON_mValues_Compile.JSON.Bool";
      s += "(";
      s += Dafny.Helpers.ToString(this._b);
      s += ")";
      return s;
    }
  }
  public class JSON_String : JSON {
    public readonly Dafny.ISequence<char> _str;
    public JSON_String(Dafny.ISequence<char> str) {
      this._str = str;
    }
    public override _IJSON DowncastClone() {
      if (this is _IJSON dt) { return dt; }
      return new JSON_String(_str);
    }
    public override bool Equals(object other) {
      var oth = other as JSON_mValues_Compile.JSON_String;
      return oth != null && object.Equals(this._str, oth._str);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 2;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._str));
      return (int) hash;
    }
    public override string ToString() {
      string s = "JSON_mValues_Compile.JSON.String";
      s += "(";
      s += Dafny.Helpers.ToString(this._str);
      s += ")";
      return s;
    }
  }
  public class JSON_Number : JSON {
    public readonly JSON_mValues_Compile._IDecimal _num;
    public JSON_Number(JSON_mValues_Compile._IDecimal num) {
      this._num = num;
    }
    public override _IJSON DowncastClone() {
      if (this is _IJSON dt) { return dt; }
      return new JSON_Number(_num);
    }
    public override bool Equals(object other) {
      var oth = other as JSON_mValues_Compile.JSON_Number;
      return oth != null && object.Equals(this._num, oth._num);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 3;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._num));
      return (int) hash;
    }
    public override string ToString() {
      string s = "JSON_mValues_Compile.JSON.Number";
      s += "(";
      s += Dafny.Helpers.ToString(this._num);
      s += ")";
      return s;
    }
  }
  public class JSON_Object : JSON {
    public readonly Dafny.ISequence<_System._ITuple2<Dafny.ISequence<char>, JSON_mValues_Compile._IJSON>> _obj;
    public JSON_Object(Dafny.ISequence<_System._ITuple2<Dafny.ISequence<char>, JSON_mValues_Compile._IJSON>> obj) {
      this._obj = obj;
    }
    public override _IJSON DowncastClone() {
      if (this is _IJSON dt) { return dt; }
      return new JSON_Object(_obj);
    }
    public override bool Equals(object other) {
      var oth = other as JSON_mValues_Compile.JSON_Object;
      return oth != null && object.Equals(this._obj, oth._obj);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 4;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._obj));
      return (int) hash;
    }
    public override string ToString() {
      string s = "JSON_mValues_Compile.JSON.Object";
      s += "(";
      s += Dafny.Helpers.ToString(this._obj);
      s += ")";
      return s;
    }
  }
  public class JSON_Array : JSON {
    public readonly Dafny.ISequence<JSON_mValues_Compile._IJSON> _arr;
    public JSON_Array(Dafny.ISequence<JSON_mValues_Compile._IJSON> arr) {
      this._arr = arr;
    }
    public override _IJSON DowncastClone() {
      if (this is _IJSON dt) { return dt; }
      return new JSON_Array(_arr);
    }
    public override bool Equals(object other) {
      var oth = other as JSON_mValues_Compile.JSON_Array;
      return oth != null && object.Equals(this._arr, oth._arr);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 5;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._arr));
      return (int) hash;
    }
    public override string ToString() {
      string s = "JSON_mValues_Compile.JSON.Array";
      s += "(";
      s += Dafny.Helpers.ToString(this._arr);
      s += ")";
      return s;
    }
  }

  public partial class __default {
    public static JSON_mValues_Compile._IDecimal Int(BigInteger n) {
      return JSON_mValues_Compile.Decimal.create(n, BigInteger.Zero);
    }
  }
} // end of namespace JSON_mValues_Compile
namespace JSON_mSpec_Compile {

  public partial class __default {
    public static Dafny.ISequence<ushort> EscapeUnicode(ushort c) {
      Dafny.ISequence<char> _428_sStr = JSON_mUtils_mStr_Compile.__default.OfNat(new BigInteger(c), new BigInteger(16));
      Dafny.ISequence<ushort> _429_s = UnicodeStrings_Compile.__default.ASCIIToUTF16(_428_sStr);
      return Dafny.Sequence<ushort>.Concat(_429_s, ((System.Func<Dafny.ISequence<ushort>>) (() => {
        BigInteger dim8 = (new BigInteger(4)) - (new BigInteger((_429_s).Count));
        var arr8 = new ushort[Dafny.Helpers.ToIntChecked(dim8, "array size exceeds memory limit")];
        for (int i8 = 0; i8 < dim8; i8++) {
          var _430___v0 = (BigInteger) i8;
          arr8[(int)(_430___v0)] = (ushort)(' ');
        }
        return Dafny.Sequence<ushort>.FromArray(arr8);
      }))());
    }
    public static Dafny.ISequence<ushort> Escape(Dafny.ISequence<ushort> str, BigInteger start)
    {
      Dafny.ISequence<ushort> _431___accumulator = Dafny.Sequence<ushort>.FromElements();
    TAIL_CALL_START: ;
      var _pat_let_tv2 = str;
      var _pat_let_tv3 = start;
      if ((start) >= (new BigInteger((str).Count))) {
        return Dafny.Sequence<ushort>.Concat(_431___accumulator, Dafny.Sequence<ushort>.FromElements());
      } else {
        _431___accumulator = Dafny.Sequence<ushort>.Concat(_431___accumulator, ((((str).Select(start)) == ((ushort)(34))) ? (UnicodeStrings_Compile.__default.ASCIIToUTF16(Dafny.Sequence<char>.FromString("\\\""))) : (((((str).Select(start)) == ((ushort)(92))) ? (UnicodeStrings_Compile.__default.ASCIIToUTF16(Dafny.Sequence<char>.FromString("\\\\"))) : (((((str).Select(start)) == ((ushort)(8))) ? (UnicodeStrings_Compile.__default.ASCIIToUTF16(Dafny.Sequence<char>.FromString("\\b"))) : (((((str).Select(start)) == ((ushort)(12))) ? (UnicodeStrings_Compile.__default.ASCIIToUTF16(Dafny.Sequence<char>.FromString("\\f"))) : (((((str).Select(start)) == ((ushort)(10))) ? (UnicodeStrings_Compile.__default.ASCIIToUTF16(Dafny.Sequence<char>.FromString("\\n"))) : (((((str).Select(start)) == ((ushort)(13))) ? (UnicodeStrings_Compile.__default.ASCIIToUTF16(Dafny.Sequence<char>.FromString("\\r"))) : (((((str).Select(start)) == ((ushort)(9))) ? (UnicodeStrings_Compile.__default.ASCIIToUTF16(Dafny.Sequence<char>.FromString("\\t"))) : (Dafny.Helpers.Let<ushort, Dafny.ISequence<ushort>>((str).Select(start), _pat_let1_0 => Dafny.Helpers.Let<ushort, Dafny.ISequence<ushort>>(_pat_let1_0, _432_c => (((_432_c) < ((ushort)(31))) ? (Dafny.Sequence<ushort>.Concat(UnicodeStrings_Compile.__default.ASCIIToUTF16(Dafny.Sequence<char>.FromString("\\u")), JSON_mSpec_Compile.__default.EscapeUnicode(_432_c))) : (Dafny.Sequence<ushort>.FromElements((_pat_let_tv2).Select(_pat_let_tv3)))))))))))))))))))));
        Dafny.ISequence<ushort> _in101 = str;
        BigInteger _in102 = (start) + (BigInteger.One);
        str = _in101;
        start = _in102;
        goto TAIL_CALL_START;
      }
    }
    public static Wrappers_Compile._IResult<Dafny.ISequence<byte>, JSON_mErrors_Compile._ISerializationError> EscapeToUTF8(Dafny.ISequence<char> str, BigInteger start)
    {
      Wrappers_Compile._IResult<Dafny.ISequence<ushort>, JSON_mErrors_Compile._ISerializationError> _433_valueOrError0 = (UnicodeStrings_Compile.__default.ToUTF16Checked(str)).ToResult_k<JSON_mErrors_Compile._ISerializationError>(JSON_mErrors_Compile.SerializationError.create_InvalidUnicode());
      if ((_433_valueOrError0).IsFailure()) {
        return (_433_valueOrError0).PropagateFailure<Dafny.ISequence<byte>>();
      } else {
        Dafny.ISequence<ushort> _434_utf16 = (_433_valueOrError0).Extract();
        Dafny.ISequence<ushort> _435_escaped = JSON_mSpec_Compile.__default.Escape(_434_utf16, BigInteger.Zero);
        Wrappers_Compile._IResult<Dafny.ISequence<char>, JSON_mErrors_Compile._ISerializationError> _436_valueOrError1 = (UnicodeStrings_Compile.__default.FromUTF16Checked(_435_escaped)).ToResult_k<JSON_mErrors_Compile._ISerializationError>(JSON_mErrors_Compile.SerializationError.create_InvalidUnicode());
        if ((_436_valueOrError1).IsFailure()) {
          return (_436_valueOrError1).PropagateFailure<Dafny.ISequence<byte>>();
        } else {
          Dafny.ISequence<char> _437_utf32 = (_436_valueOrError1).Extract();
          return (UnicodeStrings_Compile.__default.ToUTF8Checked(_437_utf32)).ToResult_k<JSON_mErrors_Compile._ISerializationError>(JSON_mErrors_Compile.SerializationError.create_InvalidUnicode());
        }
      }
    }
    public static Wrappers_Compile._IResult<Dafny.ISequence<byte>, JSON_mErrors_Compile._ISerializationError> String(Dafny.ISequence<char> str) {
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, JSON_mErrors_Compile._ISerializationError> _438_valueOrError0 = JSON_mSpec_Compile.__default.EscapeToUTF8(str, BigInteger.Zero);
      if ((_438_valueOrError0).IsFailure()) {
        return (_438_valueOrError0).PropagateFailure<Dafny.ISequence<byte>>();
      } else {
        Dafny.ISequence<byte> _439_inBytes = (_438_valueOrError0).Extract();
        return Wrappers_Compile.Result<Dafny.ISequence<byte>, JSON_mErrors_Compile._ISerializationError>.create_Success(Dafny.Sequence<byte>.Concat(Dafny.Sequence<byte>.Concat(UnicodeStrings_Compile.__default.ASCIIToUTF8(Dafny.Sequence<char>.FromString("\"")), _439_inBytes), UnicodeStrings_Compile.__default.ASCIIToUTF8(Dafny.Sequence<char>.FromString("\""))));
      }
    }
    public static Dafny.ISequence<byte> IntToBytes(BigInteger n) {
      Dafny.ISequence<char> _440_s = JSON_mUtils_mStr_Compile.__default.OfInt(n, new BigInteger(10));
      return UnicodeStrings_Compile.__default.ASCIIToUTF8(_440_s);
    }
    public static Wrappers_Compile._IResult<Dafny.ISequence<byte>, JSON_mErrors_Compile._ISerializationError> Number(JSON_mValues_Compile._IDecimal dec) {
      return Wrappers_Compile.Result<Dafny.ISequence<byte>, JSON_mErrors_Compile._ISerializationError>.create_Success(Dafny.Sequence<byte>.Concat(JSON_mSpec_Compile.__default.IntToBytes((dec).dtor_n), ((((dec).dtor_e10).Sign == 0) ? (Dafny.Sequence<byte>.FromElements()) : (Dafny.Sequence<byte>.Concat(UnicodeStrings_Compile.__default.ASCIIToUTF8(Dafny.Sequence<char>.FromString("e")), JSON_mSpec_Compile.__default.IntToBytes((dec).dtor_e10))))));
    }
    public static Wrappers_Compile._IResult<Dafny.ISequence<byte>, JSON_mErrors_Compile._ISerializationError> KeyValue(_System._ITuple2<Dafny.ISequence<char>, JSON_mValues_Compile._IJSON> kv) {
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, JSON_mErrors_Compile._ISerializationError> _441_valueOrError0 = JSON_mSpec_Compile.__default.String((kv).dtor__0);
      if ((_441_valueOrError0).IsFailure()) {
        return (_441_valueOrError0).PropagateFailure<Dafny.ISequence<byte>>();
      } else {
        Dafny.ISequence<byte> _442_key = (_441_valueOrError0).Extract();
        Wrappers_Compile._IResult<Dafny.ISequence<byte>, JSON_mErrors_Compile._ISerializationError> _443_valueOrError1 = JSON_mSpec_Compile.__default.JSON((kv).dtor__1);
        if ((_443_valueOrError1).IsFailure()) {
          return (_443_valueOrError1).PropagateFailure<Dafny.ISequence<byte>>();
        } else {
          Dafny.ISequence<byte> _444_value = (_443_valueOrError1).Extract();
          return Wrappers_Compile.Result<Dafny.ISequence<byte>, JSON_mErrors_Compile._ISerializationError>.create_Success(Dafny.Sequence<byte>.Concat(Dafny.Sequence<byte>.Concat(_442_key, UnicodeStrings_Compile.__default.ASCIIToUTF8(Dafny.Sequence<char>.FromString(":"))), _444_value));
        }
      }
    }
    public static Wrappers_Compile._IResult<Dafny.ISequence<byte>, JSON_mErrors_Compile._ISerializationError> Join(Dafny.ISequence<byte> sep, Dafny.ISequence<Wrappers_Compile._IResult<Dafny.ISequence<byte>, JSON_mErrors_Compile._ISerializationError>> items)
    {
      if ((new BigInteger((items).Count)).Sign == 0) {
        return Wrappers_Compile.Result<Dafny.ISequence<byte>, JSON_mErrors_Compile._ISerializationError>.create_Success(Dafny.Sequence<byte>.FromElements());
      } else {
        Wrappers_Compile._IResult<Dafny.ISequence<byte>, JSON_mErrors_Compile._ISerializationError> _445_valueOrError0 = (items).Select(BigInteger.Zero);
        if ((_445_valueOrError0).IsFailure()) {
          return (_445_valueOrError0).PropagateFailure<Dafny.ISequence<byte>>();
        } else {
          Dafny.ISequence<byte> _446_first = (_445_valueOrError0).Extract();
          if ((new BigInteger((items).Count)) == (BigInteger.One)) {
            return Wrappers_Compile.Result<Dafny.ISequence<byte>, JSON_mErrors_Compile._ISerializationError>.create_Success(_446_first);
          } else {
            Wrappers_Compile._IResult<Dafny.ISequence<byte>, JSON_mErrors_Compile._ISerializationError> _447_valueOrError1 = JSON_mSpec_Compile.__default.Join(sep, (items).Drop(BigInteger.One));
            if ((_447_valueOrError1).IsFailure()) {
              return (_447_valueOrError1).PropagateFailure<Dafny.ISequence<byte>>();
            } else {
              Dafny.ISequence<byte> _448_rest = (_447_valueOrError1).Extract();
              return Wrappers_Compile.Result<Dafny.ISequence<byte>, JSON_mErrors_Compile._ISerializationError>.create_Success(Dafny.Sequence<byte>.Concat(Dafny.Sequence<byte>.Concat(_446_first, sep), _448_rest));
            }
          }
        }
      }
    }
    public static Wrappers_Compile._IResult<Dafny.ISequence<byte>, JSON_mErrors_Compile._ISerializationError> Object(Dafny.ISequence<_System._ITuple2<Dafny.ISequence<char>, JSON_mValues_Compile._IJSON>> obj) {
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, JSON_mErrors_Compile._ISerializationError> _449_valueOrError0 = JSON_mSpec_Compile.__default.Join(UnicodeStrings_Compile.__default.ASCIIToUTF8(Dafny.Sequence<char>.FromString(",")), ((System.Func<Dafny.ISequence<Wrappers_Compile._IResult<Dafny.ISequence<byte>, JSON_mErrors_Compile._ISerializationError>>>) (() => {
        BigInteger dim9 = new BigInteger((obj).Count);
        var arr9 = new Wrappers_Compile._IResult<Dafny.ISequence<byte>, JSON_mErrors_Compile._ISerializationError>[Dafny.Helpers.ToIntChecked(dim9, "array size exceeds memory limit")];
        for (int i9 = 0; i9 < dim9; i9++) {
          var _450_i = (BigInteger) i9;
          arr9[(int)(_450_i)] = JSON_mSpec_Compile.__default.KeyValue((obj).Select(_450_i));
        }
        return Dafny.Sequence<Wrappers_Compile._IResult<Dafny.ISequence<byte>, JSON_mErrors_Compile._ISerializationError>>.FromArray(arr9);
      }))());
      if ((_449_valueOrError0).IsFailure()) {
        return (_449_valueOrError0).PropagateFailure<Dafny.ISequence<byte>>();
      } else {
        Dafny.ISequence<byte> _451_middle = (_449_valueOrError0).Extract();
        return Wrappers_Compile.Result<Dafny.ISequence<byte>, JSON_mErrors_Compile._ISerializationError>.create_Success(Dafny.Sequence<byte>.Concat(Dafny.Sequence<byte>.Concat(UnicodeStrings_Compile.__default.ASCIIToUTF8(Dafny.Sequence<char>.FromString("{")), _451_middle), UnicodeStrings_Compile.__default.ASCIIToUTF8(Dafny.Sequence<char>.FromString("}"))));
      }
    }
    public static Wrappers_Compile._IResult<Dafny.ISequence<byte>, JSON_mErrors_Compile._ISerializationError> Array(Dafny.ISequence<JSON_mValues_Compile._IJSON> arr) {
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, JSON_mErrors_Compile._ISerializationError> _452_valueOrError0 = JSON_mSpec_Compile.__default.Join(UnicodeStrings_Compile.__default.ASCIIToUTF8(Dafny.Sequence<char>.FromString(",")), ((System.Func<Dafny.ISequence<Wrappers_Compile._IResult<Dafny.ISequence<byte>, JSON_mErrors_Compile._ISerializationError>>>) (() => {
        BigInteger dim10 = new BigInteger((arr).Count);
        var arr10 = new Wrappers_Compile._IResult<Dafny.ISequence<byte>, JSON_mErrors_Compile._ISerializationError>[Dafny.Helpers.ToIntChecked(dim10, "array size exceeds memory limit")];
        for (int i10 = 0; i10 < dim10; i10++) {
          var _453_i = (BigInteger) i10;
          arr10[(int)(_453_i)] = JSON_mSpec_Compile.__default.JSON((arr).Select(_453_i));
        }
        return Dafny.Sequence<Wrappers_Compile._IResult<Dafny.ISequence<byte>, JSON_mErrors_Compile._ISerializationError>>.FromArray(arr10);
      }))());
      if ((_452_valueOrError0).IsFailure()) {
        return (_452_valueOrError0).PropagateFailure<Dafny.ISequence<byte>>();
      } else {
        Dafny.ISequence<byte> _454_middle = (_452_valueOrError0).Extract();
        return Wrappers_Compile.Result<Dafny.ISequence<byte>, JSON_mErrors_Compile._ISerializationError>.create_Success(Dafny.Sequence<byte>.Concat(Dafny.Sequence<byte>.Concat(UnicodeStrings_Compile.__default.ASCIIToUTF8(Dafny.Sequence<char>.FromString("[")), _454_middle), UnicodeStrings_Compile.__default.ASCIIToUTF8(Dafny.Sequence<char>.FromString("]"))));
      }
    }
    public static Wrappers_Compile._IResult<Dafny.ISequence<byte>, JSON_mErrors_Compile._ISerializationError> JSON(JSON_mValues_Compile._IJSON js) {
      JSON_mValues_Compile._IJSON _source11 = js;
      if (_source11.is_Null) {
        return Wrappers_Compile.Result<Dafny.ISequence<byte>, JSON_mErrors_Compile._ISerializationError>.create_Success(UnicodeStrings_Compile.__default.ASCIIToUTF8(Dafny.Sequence<char>.FromString("null")));
      } else if (_source11.is_Bool) {
        bool _455___mcc_h0 = _source11.dtor_b;
        bool _456_b = _455___mcc_h0;
        return Wrappers_Compile.Result<Dafny.ISequence<byte>, JSON_mErrors_Compile._ISerializationError>.create_Success(((_456_b) ? (UnicodeStrings_Compile.__default.ASCIIToUTF8(Dafny.Sequence<char>.FromString("true"))) : (UnicodeStrings_Compile.__default.ASCIIToUTF8(Dafny.Sequence<char>.FromString("false")))));
      } else if (_source11.is_String) {
        Dafny.ISequence<char> _457___mcc_h1 = _source11.dtor_str;
        Dafny.ISequence<char> _458_str = _457___mcc_h1;
        return JSON_mSpec_Compile.__default.String(_458_str);
      } else if (_source11.is_Number) {
        JSON_mValues_Compile._IDecimal _459___mcc_h2 = _source11.dtor_num;
        JSON_mValues_Compile._IDecimal _460_dec = _459___mcc_h2;
        return JSON_mSpec_Compile.__default.Number(_460_dec);
      } else if (_source11.is_Object) {
        Dafny.ISequence<_System._ITuple2<Dafny.ISequence<char>, JSON_mValues_Compile._IJSON>> _461___mcc_h3 = _source11.dtor_obj;
        Dafny.ISequence<_System._ITuple2<Dafny.ISequence<char>, JSON_mValues_Compile._IJSON>> _462_obj = _461___mcc_h3;
        return JSON_mSpec_Compile.__default.Object(_462_obj);
      } else {
        Dafny.ISequence<JSON_mValues_Compile._IJSON> _463___mcc_h4 = _source11.dtor_arr;
        Dafny.ISequence<JSON_mValues_Compile._IJSON> _464_arr = _463___mcc_h4;
        return JSON_mSpec_Compile.__default.Array(_464_arr);
      }
    }
  }
} // end of namespace JSON_mSpec_Compile
namespace JSON_mGrammar_Compile {

  public partial class jchar {
    private static readonly JSON_mUtils_mViews_mCore_Compile._IView__ Witness = JSON_mUtils_mViews_mCore_Compile.View__.OfBytes(Dafny.Sequence<byte>.FromElements((byte)('b')));
    public static JSON_mUtils_mViews_mCore_Compile._IView__ Default() {
      return Witness;
    }
    private static readonly Dafny.TypeDescriptor<JSON_mUtils_mViews_mCore_Compile._IView__> _TYPE = new Dafny.TypeDescriptor<JSON_mUtils_mViews_mCore_Compile._IView__>(JSON_mGrammar_Compile.jchar.Default());
    public static Dafny.TypeDescriptor<JSON_mUtils_mViews_mCore_Compile._IView__> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class jquote {
    private static readonly JSON_mUtils_mViews_mCore_Compile._IView__ Witness = JSON_mGrammar_Compile.__default.DOUBLEQUOTE;
    public static JSON_mUtils_mViews_mCore_Compile._IView__ Default() {
      return Witness;
    }
    private static readonly Dafny.TypeDescriptor<JSON_mUtils_mViews_mCore_Compile._IView__> _TYPE = new Dafny.TypeDescriptor<JSON_mUtils_mViews_mCore_Compile._IView__>(JSON_mGrammar_Compile.jquote.Default());
    public static Dafny.TypeDescriptor<JSON_mUtils_mViews_mCore_Compile._IView__> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class jperiod {
    private static readonly JSON_mUtils_mViews_mCore_Compile._IView__ Witness = JSON_mGrammar_Compile.__default.PERIOD;
    public static JSON_mUtils_mViews_mCore_Compile._IView__ Default() {
      return Witness;
    }
    private static readonly Dafny.TypeDescriptor<JSON_mUtils_mViews_mCore_Compile._IView__> _TYPE = new Dafny.TypeDescriptor<JSON_mUtils_mViews_mCore_Compile._IView__>(JSON_mGrammar_Compile.jperiod.Default());
    public static Dafny.TypeDescriptor<JSON_mUtils_mViews_mCore_Compile._IView__> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class je {
    private static readonly JSON_mUtils_mViews_mCore_Compile._IView__ Witness = JSON_mGrammar_Compile.__default.E;
    public static JSON_mUtils_mViews_mCore_Compile._IView__ Default() {
      return Witness;
    }
    private static readonly Dafny.TypeDescriptor<JSON_mUtils_mViews_mCore_Compile._IView__> _TYPE = new Dafny.TypeDescriptor<JSON_mUtils_mViews_mCore_Compile._IView__>(JSON_mGrammar_Compile.je.Default());
    public static Dafny.TypeDescriptor<JSON_mUtils_mViews_mCore_Compile._IView__> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class jcolon {
    private static readonly JSON_mUtils_mViews_mCore_Compile._IView__ Witness = JSON_mGrammar_Compile.__default.COLON;
    public static JSON_mUtils_mViews_mCore_Compile._IView__ Default() {
      return Witness;
    }
    private static readonly Dafny.TypeDescriptor<JSON_mUtils_mViews_mCore_Compile._IView__> _TYPE = new Dafny.TypeDescriptor<JSON_mUtils_mViews_mCore_Compile._IView__>(JSON_mGrammar_Compile.jcolon.Default());
    public static Dafny.TypeDescriptor<JSON_mUtils_mViews_mCore_Compile._IView__> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class jcomma {
    private static readonly JSON_mUtils_mViews_mCore_Compile._IView__ Witness = JSON_mGrammar_Compile.__default.COMMA;
    public static JSON_mUtils_mViews_mCore_Compile._IView__ Default() {
      return Witness;
    }
    private static readonly Dafny.TypeDescriptor<JSON_mUtils_mViews_mCore_Compile._IView__> _TYPE = new Dafny.TypeDescriptor<JSON_mUtils_mViews_mCore_Compile._IView__>(JSON_mGrammar_Compile.jcomma.Default());
    public static Dafny.TypeDescriptor<JSON_mUtils_mViews_mCore_Compile._IView__> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class jlbrace {
    private static readonly JSON_mUtils_mViews_mCore_Compile._IView__ Witness = JSON_mGrammar_Compile.__default.LBRACE;
    public static JSON_mUtils_mViews_mCore_Compile._IView__ Default() {
      return Witness;
    }
    private static readonly Dafny.TypeDescriptor<JSON_mUtils_mViews_mCore_Compile._IView__> _TYPE = new Dafny.TypeDescriptor<JSON_mUtils_mViews_mCore_Compile._IView__>(JSON_mGrammar_Compile.jlbrace.Default());
    public static Dafny.TypeDescriptor<JSON_mUtils_mViews_mCore_Compile._IView__> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class jrbrace {
    private static readonly JSON_mUtils_mViews_mCore_Compile._IView__ Witness = JSON_mGrammar_Compile.__default.RBRACE;
    public static JSON_mUtils_mViews_mCore_Compile._IView__ Default() {
      return Witness;
    }
    private static readonly Dafny.TypeDescriptor<JSON_mUtils_mViews_mCore_Compile._IView__> _TYPE = new Dafny.TypeDescriptor<JSON_mUtils_mViews_mCore_Compile._IView__>(JSON_mGrammar_Compile.jrbrace.Default());
    public static Dafny.TypeDescriptor<JSON_mUtils_mViews_mCore_Compile._IView__> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class jlbracket {
    private static readonly JSON_mUtils_mViews_mCore_Compile._IView__ Witness = JSON_mGrammar_Compile.__default.LBRACKET;
    public static JSON_mUtils_mViews_mCore_Compile._IView__ Default() {
      return Witness;
    }
    private static readonly Dafny.TypeDescriptor<JSON_mUtils_mViews_mCore_Compile._IView__> _TYPE = new Dafny.TypeDescriptor<JSON_mUtils_mViews_mCore_Compile._IView__>(JSON_mGrammar_Compile.jlbracket.Default());
    public static Dafny.TypeDescriptor<JSON_mUtils_mViews_mCore_Compile._IView__> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class jrbracket {
    private static readonly JSON_mUtils_mViews_mCore_Compile._IView__ Witness = JSON_mGrammar_Compile.__default.RBRACKET;
    public static JSON_mUtils_mViews_mCore_Compile._IView__ Default() {
      return Witness;
    }
    private static readonly Dafny.TypeDescriptor<JSON_mUtils_mViews_mCore_Compile._IView__> _TYPE = new Dafny.TypeDescriptor<JSON_mUtils_mViews_mCore_Compile._IView__>(JSON_mGrammar_Compile.jrbracket.Default());
    public static Dafny.TypeDescriptor<JSON_mUtils_mViews_mCore_Compile._IView__> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class jminus {
    private static readonly JSON_mUtils_mViews_mCore_Compile._IView__ Witness = JSON_mGrammar_Compile.__default.MINUS;
    public static JSON_mUtils_mViews_mCore_Compile._IView__ Default() {
      return Witness;
    }
    private static readonly Dafny.TypeDescriptor<JSON_mUtils_mViews_mCore_Compile._IView__> _TYPE = new Dafny.TypeDescriptor<JSON_mUtils_mViews_mCore_Compile._IView__>(JSON_mGrammar_Compile.jminus.Default());
    public static Dafny.TypeDescriptor<JSON_mUtils_mViews_mCore_Compile._IView__> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class jsign {
    private static readonly JSON_mUtils_mViews_mCore_Compile._IView__ Witness = JSON_mGrammar_Compile.__default.EMPTY;
    public static JSON_mUtils_mViews_mCore_Compile._IView__ Default() {
      return Witness;
    }
    private static readonly Dafny.TypeDescriptor<JSON_mUtils_mViews_mCore_Compile._IView__> _TYPE = new Dafny.TypeDescriptor<JSON_mUtils_mViews_mCore_Compile._IView__>(JSON_mGrammar_Compile.jsign.Default());
    public static Dafny.TypeDescriptor<JSON_mUtils_mViews_mCore_Compile._IView__> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class jblanks {
    private static readonly JSON_mUtils_mViews_mCore_Compile._IView__ Witness = JSON_mUtils_mViews_mCore_Compile.View__.OfBytes(Dafny.Sequence<byte>.FromElements());
    public static JSON_mUtils_mViews_mCore_Compile._IView__ Default() {
      return Witness;
    }
    private static readonly Dafny.TypeDescriptor<JSON_mUtils_mViews_mCore_Compile._IView__> _TYPE = new Dafny.TypeDescriptor<JSON_mUtils_mViews_mCore_Compile._IView__>(JSON_mGrammar_Compile.jblanks.Default());
    public static Dafny.TypeDescriptor<JSON_mUtils_mViews_mCore_Compile._IView__> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public interface _IStructural<out T> {
    bool is_Structural { get; }
    JSON_mUtils_mViews_mCore_Compile._IView__ dtor_before { get; }
    T dtor_t { get; }
    JSON_mUtils_mViews_mCore_Compile._IView__ dtor_after { get; }
    _IStructural<__T> DowncastClone<__T>(Func<T, __T> converter0);
  }
  public class Structural<T> : _IStructural<T> {
    public readonly JSON_mUtils_mViews_mCore_Compile._IView__ _before;
    public readonly T _t;
    public readonly JSON_mUtils_mViews_mCore_Compile._IView__ _after;
    public Structural(JSON_mUtils_mViews_mCore_Compile._IView__ before, T t, JSON_mUtils_mViews_mCore_Compile._IView__ after) {
      this._before = before;
      this._t = t;
      this._after = after;
    }
    public _IStructural<__T> DowncastClone<__T>(Func<T, __T> converter0) {
      if (this is _IStructural<__T> dt) { return dt; }
      return new Structural<__T>(_before, converter0(_t), _after);
    }
    public override bool Equals(object other) {
      var oth = other as JSON_mGrammar_Compile.Structural<T>;
      return oth != null && object.Equals(this._before, oth._before) && object.Equals(this._t, oth._t) && object.Equals(this._after, oth._after);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._before));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._t));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._after));
      return (int) hash;
    }
    public override string ToString() {
      string s = "JSON_mGrammar_Compile.Structural.Structural";
      s += "(";
      s += Dafny.Helpers.ToString(this._before);
      s += ", ";
      s += Dafny.Helpers.ToString(this._t);
      s += ", ";
      s += Dafny.Helpers.ToString(this._after);
      s += ")";
      return s;
    }
    public static JSON_mGrammar_Compile._IStructural<T> Default(T _default_T) {
      return create(JSON_mGrammar_Compile.jblanks.Default(), _default_T, JSON_mGrammar_Compile.jblanks.Default());
    }
    public static Dafny.TypeDescriptor<JSON_mGrammar_Compile._IStructural<T>> _TypeDescriptor(Dafny.TypeDescriptor<T> _td_T) {
      return new Dafny.TypeDescriptor<JSON_mGrammar_Compile._IStructural<T>>(JSON_mGrammar_Compile.Structural<T>.Default(_td_T.Default()));
    }
    public static _IStructural<T> create(JSON_mUtils_mViews_mCore_Compile._IView__ before, T t, JSON_mUtils_mViews_mCore_Compile._IView__ after) {
      return new Structural<T>(before, t, after);
    }
    public static _IStructural<T> create_Structural(JSON_mUtils_mViews_mCore_Compile._IView__ before, T t, JSON_mUtils_mViews_mCore_Compile._IView__ after) {
      return create(before, t, after);
    }
    public bool is_Structural { get { return true; } }
    public JSON_mUtils_mViews_mCore_Compile._IView__ dtor_before {
      get {
        return this._before;
      }
    }
    public T dtor_t {
      get {
        return this._t;
      }
    }
    public JSON_mUtils_mViews_mCore_Compile._IView__ dtor_after {
      get {
        return this._after;
      }
    }
  }

  public interface _IMaybe<out T> {
    bool is_Empty { get; }
    bool is_NonEmpty { get; }
    T dtor_t { get; }
    _IMaybe<__T> DowncastClone<__T>(Func<T, __T> converter0);
  }
  public abstract class Maybe<T> : _IMaybe<T> {
    public Maybe() { }
    public static JSON_mGrammar_Compile._IMaybe<T> Default() {
      return create_Empty();
    }
    public static Dafny.TypeDescriptor<JSON_mGrammar_Compile._IMaybe<T>> _TypeDescriptor() {
      return new Dafny.TypeDescriptor<JSON_mGrammar_Compile._IMaybe<T>>(JSON_mGrammar_Compile.Maybe<T>.Default());
    }
    public static _IMaybe<T> create_Empty() {
      return new Maybe_Empty<T>();
    }
    public static _IMaybe<T> create_NonEmpty(T t) {
      return new Maybe_NonEmpty<T>(t);
    }
    public bool is_Empty { get { return this is Maybe_Empty<T>; } }
    public bool is_NonEmpty { get { return this is Maybe_NonEmpty<T>; } }
    public T dtor_t {
      get {
        var d = this;
        return ((Maybe_NonEmpty<T>)d)._t;
      }
    }
    public abstract _IMaybe<__T> DowncastClone<__T>(Func<T, __T> converter0);
  }
  public class Maybe_Empty<T> : Maybe<T> {
    public Maybe_Empty() {
    }
    public override _IMaybe<__T> DowncastClone<__T>(Func<T, __T> converter0) {
      if (this is _IMaybe<__T> dt) { return dt; }
      return new Maybe_Empty<__T>();
    }
    public override bool Equals(object other) {
      var oth = other as JSON_mGrammar_Compile.Maybe_Empty<T>;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "JSON_mGrammar_Compile.Maybe.Empty";
      return s;
    }
  }
  public class Maybe_NonEmpty<T> : Maybe<T> {
    public readonly T _t;
    public Maybe_NonEmpty(T t) {
      this._t = t;
    }
    public override _IMaybe<__T> DowncastClone<__T>(Func<T, __T> converter0) {
      if (this is _IMaybe<__T> dt) { return dt; }
      return new Maybe_NonEmpty<__T>(converter0(_t));
    }
    public override bool Equals(object other) {
      var oth = other as JSON_mGrammar_Compile.Maybe_NonEmpty<T>;
      return oth != null && object.Equals(this._t, oth._t);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._t));
      return (int) hash;
    }
    public override string ToString() {
      string s = "JSON_mGrammar_Compile.Maybe.NonEmpty";
      s += "(";
      s += Dafny.Helpers.ToString(this._t);
      s += ")";
      return s;
    }
  }

  public interface _ISuffixed<out T, out S> {
    bool is_Suffixed { get; }
    T dtor_t { get; }
    JSON_mGrammar_Compile._IMaybe<JSON_mGrammar_Compile._IStructural<S>> dtor_suffix { get; }
    _ISuffixed<__T, __S> DowncastClone<__T, __S>(Func<T, __T> converter0, Func<S, __S> converter1);
  }
  public class Suffixed<T, S> : _ISuffixed<T, S> {
    public readonly T _t;
    public readonly JSON_mGrammar_Compile._IMaybe<JSON_mGrammar_Compile._IStructural<S>> _suffix;
    public Suffixed(T t, JSON_mGrammar_Compile._IMaybe<JSON_mGrammar_Compile._IStructural<S>> suffix) {
      this._t = t;
      this._suffix = suffix;
    }
    public _ISuffixed<__T, __S> DowncastClone<__T, __S>(Func<T, __T> converter0, Func<S, __S> converter1) {
      if (this is _ISuffixed<__T, __S> dt) { return dt; }
      return new Suffixed<__T, __S>(converter0(_t), (_suffix).DowncastClone<JSON_mGrammar_Compile._IStructural<__S>>(Dafny.Helpers.CastConverter<JSON_mGrammar_Compile._IStructural<S>, JSON_mGrammar_Compile._IStructural<__S>>));
    }
    public override bool Equals(object other) {
      var oth = other as JSON_mGrammar_Compile.Suffixed<T, S>;
      return oth != null && object.Equals(this._t, oth._t) && object.Equals(this._suffix, oth._suffix);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._t));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._suffix));
      return (int) hash;
    }
    public override string ToString() {
      string s = "JSON_mGrammar_Compile.Suffixed.Suffixed";
      s += "(";
      s += Dafny.Helpers.ToString(this._t);
      s += ", ";
      s += Dafny.Helpers.ToString(this._suffix);
      s += ")";
      return s;
    }
    public static JSON_mGrammar_Compile._ISuffixed<T, S> Default(T _default_T) {
      return create(_default_T, JSON_mGrammar_Compile.Maybe<JSON_mGrammar_Compile._IStructural<S>>.Default());
    }
    public static Dafny.TypeDescriptor<JSON_mGrammar_Compile._ISuffixed<T, S>> _TypeDescriptor(Dafny.TypeDescriptor<T> _td_T) {
      return new Dafny.TypeDescriptor<JSON_mGrammar_Compile._ISuffixed<T, S>>(JSON_mGrammar_Compile.Suffixed<T, S>.Default(_td_T.Default()));
    }
    public static _ISuffixed<T, S> create(T t, JSON_mGrammar_Compile._IMaybe<JSON_mGrammar_Compile._IStructural<S>> suffix) {
      return new Suffixed<T, S>(t, suffix);
    }
    public static _ISuffixed<T, S> create_Suffixed(T t, JSON_mGrammar_Compile._IMaybe<JSON_mGrammar_Compile._IStructural<S>> suffix) {
      return create(t, suffix);
    }
    public bool is_Suffixed { get { return true; } }
    public T dtor_t {
      get {
        return this._t;
      }
    }
    public JSON_mGrammar_Compile._IMaybe<JSON_mGrammar_Compile._IStructural<S>> dtor_suffix {
      get {
        return this._suffix;
      }
    }
  }

  public partial class SuffixedSequence<D, S> {
    public static Dafny.TypeDescriptor<Dafny.ISequence<JSON_mGrammar_Compile._ISuffixed<D, S>>> _TypeDescriptor(Dafny.TypeDescriptor<D> _td_D, Dafny.TypeDescriptor<S> _td_S) {
      return new Dafny.TypeDescriptor<Dafny.ISequence<JSON_mGrammar_Compile._ISuffixed<D, S>>>(Dafny.Sequence<JSON_mGrammar_Compile._ISuffixed<D, S>>.Empty);
    }
  }

  public interface _IBracketed<out L, out D, out S, out R> {
    bool is_Bracketed { get; }
    JSON_mGrammar_Compile._IStructural<L> dtor_l { get; }
    Dafny.ISequence<JSON_mGrammar_Compile._ISuffixed<D, S>> dtor_data { get; }
    JSON_mGrammar_Compile._IStructural<R> dtor_r { get; }
    _IBracketed<__L, __D, __S, __R> DowncastClone<__L, __D, __S, __R>(Func<L, __L> converter0, Func<D, __D> converter1, Func<S, __S> converter2, Func<R, __R> converter3);
  }
  public class Bracketed<L, D, S, R> : _IBracketed<L, D, S, R> {
    public readonly JSON_mGrammar_Compile._IStructural<L> _l;
    public readonly Dafny.ISequence<JSON_mGrammar_Compile._ISuffixed<D, S>> _data;
    public readonly JSON_mGrammar_Compile._IStructural<R> _r;
    public Bracketed(JSON_mGrammar_Compile._IStructural<L> l, Dafny.ISequence<JSON_mGrammar_Compile._ISuffixed<D, S>> data, JSON_mGrammar_Compile._IStructural<R> r) {
      this._l = l;
      this._data = data;
      this._r = r;
    }
    public _IBracketed<__L, __D, __S, __R> DowncastClone<__L, __D, __S, __R>(Func<L, __L> converter0, Func<D, __D> converter1, Func<S, __S> converter2, Func<R, __R> converter3) {
      if (this is _IBracketed<__L, __D, __S, __R> dt) { return dt; }
      return new Bracketed<__L, __D, __S, __R>((_l).DowncastClone<__L>(Dafny.Helpers.CastConverter<L, __L>), (_data).DowncastClone<JSON_mGrammar_Compile._ISuffixed<__D, __S>>(Dafny.Helpers.CastConverter<JSON_mGrammar_Compile._ISuffixed<D, S>, JSON_mGrammar_Compile._ISuffixed<__D, __S>>), (_r).DowncastClone<__R>(Dafny.Helpers.CastConverter<R, __R>));
    }
    public override bool Equals(object other) {
      var oth = other as JSON_mGrammar_Compile.Bracketed<L, D, S, R>;
      return oth != null && object.Equals(this._l, oth._l) && object.Equals(this._data, oth._data) && object.Equals(this._r, oth._r);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._l));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._data));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._r));
      return (int) hash;
    }
    public override string ToString() {
      string s = "JSON_mGrammar_Compile.Bracketed.Bracketed";
      s += "(";
      s += Dafny.Helpers.ToString(this._l);
      s += ", ";
      s += Dafny.Helpers.ToString(this._data);
      s += ", ";
      s += Dafny.Helpers.ToString(this._r);
      s += ")";
      return s;
    }
    public static JSON_mGrammar_Compile._IBracketed<L, D, S, R> Default(L _default_L, R _default_R) {
      return create(JSON_mGrammar_Compile.Structural<L>.Default(_default_L), Dafny.Sequence<JSON_mGrammar_Compile._ISuffixed<D, S>>.Empty, JSON_mGrammar_Compile.Structural<R>.Default(_default_R));
    }
    public static Dafny.TypeDescriptor<JSON_mGrammar_Compile._IBracketed<L, D, S, R>> _TypeDescriptor(Dafny.TypeDescriptor<L> _td_L, Dafny.TypeDescriptor<R> _td_R) {
      return new Dafny.TypeDescriptor<JSON_mGrammar_Compile._IBracketed<L, D, S, R>>(JSON_mGrammar_Compile.Bracketed<L, D, S, R>.Default(_td_L.Default(), _td_R.Default()));
    }
    public static _IBracketed<L, D, S, R> create(JSON_mGrammar_Compile._IStructural<L> l, Dafny.ISequence<JSON_mGrammar_Compile._ISuffixed<D, S>> data, JSON_mGrammar_Compile._IStructural<R> r) {
      return new Bracketed<L, D, S, R>(l, data, r);
    }
    public static _IBracketed<L, D, S, R> create_Bracketed(JSON_mGrammar_Compile._IStructural<L> l, Dafny.ISequence<JSON_mGrammar_Compile._ISuffixed<D, S>> data, JSON_mGrammar_Compile._IStructural<R> r) {
      return create(l, data, r);
    }
    public bool is_Bracketed { get { return true; } }
    public JSON_mGrammar_Compile._IStructural<L> dtor_l {
      get {
        return this._l;
      }
    }
    public Dafny.ISequence<JSON_mGrammar_Compile._ISuffixed<D, S>> dtor_data {
      get {
        return this._data;
      }
    }
    public JSON_mGrammar_Compile._IStructural<R> dtor_r {
      get {
        return this._r;
      }
    }
  }

  public partial class jnull {
    private static readonly JSON_mUtils_mViews_mCore_Compile._IView__ Witness = JSON_mUtils_mViews_mCore_Compile.View__.OfBytes(JSON_mGrammar_Compile.__default.NULL);
    public static JSON_mUtils_mViews_mCore_Compile._IView__ Default() {
      return Witness;
    }
    private static readonly Dafny.TypeDescriptor<JSON_mUtils_mViews_mCore_Compile._IView__> _TYPE = new Dafny.TypeDescriptor<JSON_mUtils_mViews_mCore_Compile._IView__>(JSON_mGrammar_Compile.jnull.Default());
    public static Dafny.TypeDescriptor<JSON_mUtils_mViews_mCore_Compile._IView__> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class jbool {
    private static readonly JSON_mUtils_mViews_mCore_Compile._IView__ Witness = JSON_mUtils_mViews_mCore_Compile.View__.OfBytes(JSON_mGrammar_Compile.__default.TRUE);
    public static JSON_mUtils_mViews_mCore_Compile._IView__ Default() {
      return Witness;
    }
    private static readonly Dafny.TypeDescriptor<JSON_mUtils_mViews_mCore_Compile._IView__> _TYPE = new Dafny.TypeDescriptor<JSON_mUtils_mViews_mCore_Compile._IView__>(JSON_mGrammar_Compile.jbool.Default());
    public static Dafny.TypeDescriptor<JSON_mUtils_mViews_mCore_Compile._IView__> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class jdigits {
    private static readonly JSON_mUtils_mViews_mCore_Compile._IView__ Witness = JSON_mUtils_mViews_mCore_Compile.View__.OfBytes(Dafny.Sequence<byte>.FromElements());
    public static JSON_mUtils_mViews_mCore_Compile._IView__ Default() {
      return Witness;
    }
    private static readonly Dafny.TypeDescriptor<JSON_mUtils_mViews_mCore_Compile._IView__> _TYPE = new Dafny.TypeDescriptor<JSON_mUtils_mViews_mCore_Compile._IView__>(JSON_mGrammar_Compile.jdigits.Default());
    public static Dafny.TypeDescriptor<JSON_mUtils_mViews_mCore_Compile._IView__> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class jnum {
    private static readonly JSON_mUtils_mViews_mCore_Compile._IView__ Witness = JSON_mUtils_mViews_mCore_Compile.View__.OfBytes(Dafny.Sequence<byte>.FromElements((byte)('0')));
    public static JSON_mUtils_mViews_mCore_Compile._IView__ Default() {
      return Witness;
    }
    private static readonly Dafny.TypeDescriptor<JSON_mUtils_mViews_mCore_Compile._IView__> _TYPE = new Dafny.TypeDescriptor<JSON_mUtils_mViews_mCore_Compile._IView__>(JSON_mGrammar_Compile.jnum.Default());
    public static Dafny.TypeDescriptor<JSON_mUtils_mViews_mCore_Compile._IView__> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class jint {
    private static readonly JSON_mUtils_mViews_mCore_Compile._IView__ Witness = JSON_mUtils_mViews_mCore_Compile.View__.OfBytes(Dafny.Sequence<byte>.FromElements((byte)('0')));
    public static JSON_mUtils_mViews_mCore_Compile._IView__ Default() {
      return Witness;
    }
    private static readonly Dafny.TypeDescriptor<JSON_mUtils_mViews_mCore_Compile._IView__> _TYPE = new Dafny.TypeDescriptor<JSON_mUtils_mViews_mCore_Compile._IView__>(JSON_mGrammar_Compile.jint.Default());
    public static Dafny.TypeDescriptor<JSON_mUtils_mViews_mCore_Compile._IView__> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class jstr {
    private static readonly JSON_mUtils_mViews_mCore_Compile._IView__ Witness = JSON_mUtils_mViews_mCore_Compile.View__.OfBytes(Dafny.Sequence<byte>.FromElements());
    public static JSON_mUtils_mViews_mCore_Compile._IView__ Default() {
      return Witness;
    }
    private static readonly Dafny.TypeDescriptor<JSON_mUtils_mViews_mCore_Compile._IView__> _TYPE = new Dafny.TypeDescriptor<JSON_mUtils_mViews_mCore_Compile._IView__>(JSON_mGrammar_Compile.jstr.Default());
    public static Dafny.TypeDescriptor<JSON_mUtils_mViews_mCore_Compile._IView__> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public interface _Ijstring {
    bool is_JString { get; }
    JSON_mUtils_mViews_mCore_Compile._IView__ dtor_lq { get; }
    JSON_mUtils_mViews_mCore_Compile._IView__ dtor_contents { get; }
    JSON_mUtils_mViews_mCore_Compile._IView__ dtor_rq { get; }
    _Ijstring DowncastClone();
  }
  public class jstring : _Ijstring {
    public readonly JSON_mUtils_mViews_mCore_Compile._IView__ _lq;
    public readonly JSON_mUtils_mViews_mCore_Compile._IView__ _contents;
    public readonly JSON_mUtils_mViews_mCore_Compile._IView__ _rq;
    public jstring(JSON_mUtils_mViews_mCore_Compile._IView__ lq, JSON_mUtils_mViews_mCore_Compile._IView__ contents, JSON_mUtils_mViews_mCore_Compile._IView__ rq) {
      this._lq = lq;
      this._contents = contents;
      this._rq = rq;
    }
    public _Ijstring DowncastClone() {
      if (this is _Ijstring dt) { return dt; }
      return new jstring(_lq, _contents, _rq);
    }
    public override bool Equals(object other) {
      var oth = other as JSON_mGrammar_Compile.jstring;
      return oth != null && object.Equals(this._lq, oth._lq) && object.Equals(this._contents, oth._contents) && object.Equals(this._rq, oth._rq);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._lq));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._contents));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._rq));
      return (int) hash;
    }
    public override string ToString() {
      string s = "JSON_mGrammar_Compile.jstring.JString";
      s += "(";
      s += Dafny.Helpers.ToString(this._lq);
      s += ", ";
      s += Dafny.Helpers.ToString(this._contents);
      s += ", ";
      s += Dafny.Helpers.ToString(this._rq);
      s += ")";
      return s;
    }
    private static readonly JSON_mGrammar_Compile._Ijstring theDefault = create(JSON_mGrammar_Compile.jquote.Default(), JSON_mGrammar_Compile.jstr.Default(), JSON_mGrammar_Compile.jquote.Default());
    public static JSON_mGrammar_Compile._Ijstring Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<JSON_mGrammar_Compile._Ijstring> _TYPE = new Dafny.TypeDescriptor<JSON_mGrammar_Compile._Ijstring>(JSON_mGrammar_Compile.jstring.Default());
    public static Dafny.TypeDescriptor<JSON_mGrammar_Compile._Ijstring> _TypeDescriptor() {
      return _TYPE;
    }
    public static _Ijstring create(JSON_mUtils_mViews_mCore_Compile._IView__ lq, JSON_mUtils_mViews_mCore_Compile._IView__ contents, JSON_mUtils_mViews_mCore_Compile._IView__ rq) {
      return new jstring(lq, contents, rq);
    }
    public static _Ijstring create_JString(JSON_mUtils_mViews_mCore_Compile._IView__ lq, JSON_mUtils_mViews_mCore_Compile._IView__ contents, JSON_mUtils_mViews_mCore_Compile._IView__ rq) {
      return create(lq, contents, rq);
    }
    public bool is_JString { get { return true; } }
    public JSON_mUtils_mViews_mCore_Compile._IView__ dtor_lq {
      get {
        return this._lq;
      }
    }
    public JSON_mUtils_mViews_mCore_Compile._IView__ dtor_contents {
      get {
        return this._contents;
      }
    }
    public JSON_mUtils_mViews_mCore_Compile._IView__ dtor_rq {
      get {
        return this._rq;
      }
    }
  }

  public interface _IjKeyValue {
    bool is_KeyValue { get; }
    JSON_mGrammar_Compile._Ijstring dtor_k { get; }
    JSON_mGrammar_Compile._IStructural<JSON_mUtils_mViews_mCore_Compile._IView__> dtor_colon { get; }
    JSON_mGrammar_Compile._IValue dtor_v { get; }
    _IjKeyValue DowncastClone();
  }
  public class jKeyValue : _IjKeyValue {
    public readonly JSON_mGrammar_Compile._Ijstring _k;
    public readonly JSON_mGrammar_Compile._IStructural<JSON_mUtils_mViews_mCore_Compile._IView__> _colon;
    public readonly JSON_mGrammar_Compile._IValue _v;
    public jKeyValue(JSON_mGrammar_Compile._Ijstring k, JSON_mGrammar_Compile._IStructural<JSON_mUtils_mViews_mCore_Compile._IView__> colon, JSON_mGrammar_Compile._IValue v) {
      this._k = k;
      this._colon = colon;
      this._v = v;
    }
    public _IjKeyValue DowncastClone() {
      if (this is _IjKeyValue dt) { return dt; }
      return new jKeyValue(_k, _colon, _v);
    }
    public override bool Equals(object other) {
      var oth = other as JSON_mGrammar_Compile.jKeyValue;
      return oth != null && object.Equals(this._k, oth._k) && object.Equals(this._colon, oth._colon) && object.Equals(this._v, oth._v);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._k));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._colon));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._v));
      return (int) hash;
    }
    public override string ToString() {
      string s = "JSON_mGrammar_Compile.jKeyValue.KeyValue";
      s += "(";
      s += Dafny.Helpers.ToString(this._k);
      s += ", ";
      s += Dafny.Helpers.ToString(this._colon);
      s += ", ";
      s += Dafny.Helpers.ToString(this._v);
      s += ")";
      return s;
    }
    private static readonly JSON_mGrammar_Compile._IjKeyValue theDefault = create(JSON_mGrammar_Compile.jstring.Default(), JSON_mGrammar_Compile.Structural<JSON_mUtils_mViews_mCore_Compile._IView__>.Default(JSON_mGrammar_Compile.jcolon.Default()), JSON_mGrammar_Compile.Value.Default());
    public static JSON_mGrammar_Compile._IjKeyValue Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<JSON_mGrammar_Compile._IjKeyValue> _TYPE = new Dafny.TypeDescriptor<JSON_mGrammar_Compile._IjKeyValue>(JSON_mGrammar_Compile.jKeyValue.Default());
    public static Dafny.TypeDescriptor<JSON_mGrammar_Compile._IjKeyValue> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IjKeyValue create(JSON_mGrammar_Compile._Ijstring k, JSON_mGrammar_Compile._IStructural<JSON_mUtils_mViews_mCore_Compile._IView__> colon, JSON_mGrammar_Compile._IValue v) {
      return new jKeyValue(k, colon, v);
    }
    public static _IjKeyValue create_KeyValue(JSON_mGrammar_Compile._Ijstring k, JSON_mGrammar_Compile._IStructural<JSON_mUtils_mViews_mCore_Compile._IView__> colon, JSON_mGrammar_Compile._IValue v) {
      return create(k, colon, v);
    }
    public bool is_KeyValue { get { return true; } }
    public JSON_mGrammar_Compile._Ijstring dtor_k {
      get {
        return this._k;
      }
    }
    public JSON_mGrammar_Compile._IStructural<JSON_mUtils_mViews_mCore_Compile._IView__> dtor_colon {
      get {
        return this._colon;
      }
    }
    public JSON_mGrammar_Compile._IValue dtor_v {
      get {
        return this._v;
      }
    }
  }

  public interface _Ijfrac {
    bool is_JFrac { get; }
    JSON_mUtils_mViews_mCore_Compile._IView__ dtor_period { get; }
    JSON_mUtils_mViews_mCore_Compile._IView__ dtor_num { get; }
    _Ijfrac DowncastClone();
  }
  public class jfrac : _Ijfrac {
    public readonly JSON_mUtils_mViews_mCore_Compile._IView__ _period;
    public readonly JSON_mUtils_mViews_mCore_Compile._IView__ _num;
    public jfrac(JSON_mUtils_mViews_mCore_Compile._IView__ period, JSON_mUtils_mViews_mCore_Compile._IView__ num) {
      this._period = period;
      this._num = num;
    }
    public _Ijfrac DowncastClone() {
      if (this is _Ijfrac dt) { return dt; }
      return new jfrac(_period, _num);
    }
    public override bool Equals(object other) {
      var oth = other as JSON_mGrammar_Compile.jfrac;
      return oth != null && object.Equals(this._period, oth._period) && object.Equals(this._num, oth._num);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._period));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._num));
      return (int) hash;
    }
    public override string ToString() {
      string s = "JSON_mGrammar_Compile.jfrac.JFrac";
      s += "(";
      s += Dafny.Helpers.ToString(this._period);
      s += ", ";
      s += Dafny.Helpers.ToString(this._num);
      s += ")";
      return s;
    }
    private static readonly JSON_mGrammar_Compile._Ijfrac theDefault = create(JSON_mGrammar_Compile.jperiod.Default(), JSON_mGrammar_Compile.jnum.Default());
    public static JSON_mGrammar_Compile._Ijfrac Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<JSON_mGrammar_Compile._Ijfrac> _TYPE = new Dafny.TypeDescriptor<JSON_mGrammar_Compile._Ijfrac>(JSON_mGrammar_Compile.jfrac.Default());
    public static Dafny.TypeDescriptor<JSON_mGrammar_Compile._Ijfrac> _TypeDescriptor() {
      return _TYPE;
    }
    public static _Ijfrac create(JSON_mUtils_mViews_mCore_Compile._IView__ period, JSON_mUtils_mViews_mCore_Compile._IView__ num) {
      return new jfrac(period, num);
    }
    public static _Ijfrac create_JFrac(JSON_mUtils_mViews_mCore_Compile._IView__ period, JSON_mUtils_mViews_mCore_Compile._IView__ num) {
      return create(period, num);
    }
    public bool is_JFrac { get { return true; } }
    public JSON_mUtils_mViews_mCore_Compile._IView__ dtor_period {
      get {
        return this._period;
      }
    }
    public JSON_mUtils_mViews_mCore_Compile._IView__ dtor_num {
      get {
        return this._num;
      }
    }
  }

  public interface _Ijexp {
    bool is_JExp { get; }
    JSON_mUtils_mViews_mCore_Compile._IView__ dtor_e { get; }
    JSON_mUtils_mViews_mCore_Compile._IView__ dtor_sign { get; }
    JSON_mUtils_mViews_mCore_Compile._IView__ dtor_num { get; }
    _Ijexp DowncastClone();
  }
  public class jexp : _Ijexp {
    public readonly JSON_mUtils_mViews_mCore_Compile._IView__ _e;
    public readonly JSON_mUtils_mViews_mCore_Compile._IView__ _sign;
    public readonly JSON_mUtils_mViews_mCore_Compile._IView__ _num;
    public jexp(JSON_mUtils_mViews_mCore_Compile._IView__ e, JSON_mUtils_mViews_mCore_Compile._IView__ sign, JSON_mUtils_mViews_mCore_Compile._IView__ num) {
      this._e = e;
      this._sign = sign;
      this._num = num;
    }
    public _Ijexp DowncastClone() {
      if (this is _Ijexp dt) { return dt; }
      return new jexp(_e, _sign, _num);
    }
    public override bool Equals(object other) {
      var oth = other as JSON_mGrammar_Compile.jexp;
      return oth != null && object.Equals(this._e, oth._e) && object.Equals(this._sign, oth._sign) && object.Equals(this._num, oth._num);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._e));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._sign));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._num));
      return (int) hash;
    }
    public override string ToString() {
      string s = "JSON_mGrammar_Compile.jexp.JExp";
      s += "(";
      s += Dafny.Helpers.ToString(this._e);
      s += ", ";
      s += Dafny.Helpers.ToString(this._sign);
      s += ", ";
      s += Dafny.Helpers.ToString(this._num);
      s += ")";
      return s;
    }
    private static readonly JSON_mGrammar_Compile._Ijexp theDefault = create(JSON_mGrammar_Compile.je.Default(), JSON_mGrammar_Compile.jsign.Default(), JSON_mGrammar_Compile.jnum.Default());
    public static JSON_mGrammar_Compile._Ijexp Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<JSON_mGrammar_Compile._Ijexp> _TYPE = new Dafny.TypeDescriptor<JSON_mGrammar_Compile._Ijexp>(JSON_mGrammar_Compile.jexp.Default());
    public static Dafny.TypeDescriptor<JSON_mGrammar_Compile._Ijexp> _TypeDescriptor() {
      return _TYPE;
    }
    public static _Ijexp create(JSON_mUtils_mViews_mCore_Compile._IView__ e, JSON_mUtils_mViews_mCore_Compile._IView__ sign, JSON_mUtils_mViews_mCore_Compile._IView__ num) {
      return new jexp(e, sign, num);
    }
    public static _Ijexp create_JExp(JSON_mUtils_mViews_mCore_Compile._IView__ e, JSON_mUtils_mViews_mCore_Compile._IView__ sign, JSON_mUtils_mViews_mCore_Compile._IView__ num) {
      return create(e, sign, num);
    }
    public bool is_JExp { get { return true; } }
    public JSON_mUtils_mViews_mCore_Compile._IView__ dtor_e {
      get {
        return this._e;
      }
    }
    public JSON_mUtils_mViews_mCore_Compile._IView__ dtor_sign {
      get {
        return this._sign;
      }
    }
    public JSON_mUtils_mViews_mCore_Compile._IView__ dtor_num {
      get {
        return this._num;
      }
    }
  }

  public interface _Ijnumber {
    bool is_JNumber { get; }
    JSON_mUtils_mViews_mCore_Compile._IView__ dtor_minus { get; }
    JSON_mUtils_mViews_mCore_Compile._IView__ dtor_num { get; }
    JSON_mGrammar_Compile._IMaybe<JSON_mGrammar_Compile._Ijfrac> dtor_frac { get; }
    JSON_mGrammar_Compile._IMaybe<JSON_mGrammar_Compile._Ijexp> dtor_exp { get; }
    _Ijnumber DowncastClone();
  }
  public class jnumber : _Ijnumber {
    public readonly JSON_mUtils_mViews_mCore_Compile._IView__ _minus;
    public readonly JSON_mUtils_mViews_mCore_Compile._IView__ _num;
    public readonly JSON_mGrammar_Compile._IMaybe<JSON_mGrammar_Compile._Ijfrac> _frac;
    public readonly JSON_mGrammar_Compile._IMaybe<JSON_mGrammar_Compile._Ijexp> _exp;
    public jnumber(JSON_mUtils_mViews_mCore_Compile._IView__ minus, JSON_mUtils_mViews_mCore_Compile._IView__ num, JSON_mGrammar_Compile._IMaybe<JSON_mGrammar_Compile._Ijfrac> frac, JSON_mGrammar_Compile._IMaybe<JSON_mGrammar_Compile._Ijexp> exp) {
      this._minus = minus;
      this._num = num;
      this._frac = frac;
      this._exp = exp;
    }
    public _Ijnumber DowncastClone() {
      if (this is _Ijnumber dt) { return dt; }
      return new jnumber(_minus, _num, _frac, _exp);
    }
    public override bool Equals(object other) {
      var oth = other as JSON_mGrammar_Compile.jnumber;
      return oth != null && object.Equals(this._minus, oth._minus) && object.Equals(this._num, oth._num) && object.Equals(this._frac, oth._frac) && object.Equals(this._exp, oth._exp);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._minus));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._num));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._frac));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._exp));
      return (int) hash;
    }
    public override string ToString() {
      string s = "JSON_mGrammar_Compile.jnumber.JNumber";
      s += "(";
      s += Dafny.Helpers.ToString(this._minus);
      s += ", ";
      s += Dafny.Helpers.ToString(this._num);
      s += ", ";
      s += Dafny.Helpers.ToString(this._frac);
      s += ", ";
      s += Dafny.Helpers.ToString(this._exp);
      s += ")";
      return s;
    }
    private static readonly JSON_mGrammar_Compile._Ijnumber theDefault = create(JSON_mGrammar_Compile.jminus.Default(), JSON_mGrammar_Compile.jnum.Default(), JSON_mGrammar_Compile.Maybe<JSON_mGrammar_Compile._Ijfrac>.Default(), JSON_mGrammar_Compile.Maybe<JSON_mGrammar_Compile._Ijexp>.Default());
    public static JSON_mGrammar_Compile._Ijnumber Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<JSON_mGrammar_Compile._Ijnumber> _TYPE = new Dafny.TypeDescriptor<JSON_mGrammar_Compile._Ijnumber>(JSON_mGrammar_Compile.jnumber.Default());
    public static Dafny.TypeDescriptor<JSON_mGrammar_Compile._Ijnumber> _TypeDescriptor() {
      return _TYPE;
    }
    public static _Ijnumber create(JSON_mUtils_mViews_mCore_Compile._IView__ minus, JSON_mUtils_mViews_mCore_Compile._IView__ num, JSON_mGrammar_Compile._IMaybe<JSON_mGrammar_Compile._Ijfrac> frac, JSON_mGrammar_Compile._IMaybe<JSON_mGrammar_Compile._Ijexp> exp) {
      return new jnumber(minus, num, frac, exp);
    }
    public static _Ijnumber create_JNumber(JSON_mUtils_mViews_mCore_Compile._IView__ minus, JSON_mUtils_mViews_mCore_Compile._IView__ num, JSON_mGrammar_Compile._IMaybe<JSON_mGrammar_Compile._Ijfrac> frac, JSON_mGrammar_Compile._IMaybe<JSON_mGrammar_Compile._Ijexp> exp) {
      return create(minus, num, frac, exp);
    }
    public bool is_JNumber { get { return true; } }
    public JSON_mUtils_mViews_mCore_Compile._IView__ dtor_minus {
      get {
        return this._minus;
      }
    }
    public JSON_mUtils_mViews_mCore_Compile._IView__ dtor_num {
      get {
        return this._num;
      }
    }
    public JSON_mGrammar_Compile._IMaybe<JSON_mGrammar_Compile._Ijfrac> dtor_frac {
      get {
        return this._frac;
      }
    }
    public JSON_mGrammar_Compile._IMaybe<JSON_mGrammar_Compile._Ijexp> dtor_exp {
      get {
        return this._exp;
      }
    }
  }

  public interface _IValue {
    bool is_Null { get; }
    bool is_Bool { get; }
    bool is_String { get; }
    bool is_Number { get; }
    bool is_Object { get; }
    bool is_Array { get; }
    JSON_mUtils_mViews_mCore_Compile._IView__ dtor_n { get; }
    JSON_mUtils_mViews_mCore_Compile._IView__ dtor_b { get; }
    JSON_mGrammar_Compile._Ijstring dtor_str { get; }
    JSON_mGrammar_Compile._Ijnumber dtor_num { get; }
    JSON_mGrammar_Compile._IBracketed<JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mGrammar_Compile._IjKeyValue, JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mUtils_mViews_mCore_Compile._IView__> dtor_obj { get; }
    JSON_mGrammar_Compile._IBracketed<JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mGrammar_Compile._IValue, JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mUtils_mViews_mCore_Compile._IView__> dtor_arr { get; }
    _IValue DowncastClone();
  }
  public abstract class Value : _IValue {
    public Value() { }
    private static readonly JSON_mGrammar_Compile._IValue theDefault = create_Null(JSON_mGrammar_Compile.jnull.Default());
    public static JSON_mGrammar_Compile._IValue Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<JSON_mGrammar_Compile._IValue> _TYPE = new Dafny.TypeDescriptor<JSON_mGrammar_Compile._IValue>(JSON_mGrammar_Compile.Value.Default());
    public static Dafny.TypeDescriptor<JSON_mGrammar_Compile._IValue> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IValue create_Null(JSON_mUtils_mViews_mCore_Compile._IView__ n) {
      return new Value_Null(n);
    }
    public static _IValue create_Bool(JSON_mUtils_mViews_mCore_Compile._IView__ b) {
      return new Value_Bool(b);
    }
    public static _IValue create_String(JSON_mGrammar_Compile._Ijstring str) {
      return new Value_String(str);
    }
    public static _IValue create_Number(JSON_mGrammar_Compile._Ijnumber num) {
      return new Value_Number(num);
    }
    public static _IValue create_Object(JSON_mGrammar_Compile._IBracketed<JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mGrammar_Compile._IjKeyValue, JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mUtils_mViews_mCore_Compile._IView__> obj) {
      return new Value_Object(obj);
    }
    public static _IValue create_Array(JSON_mGrammar_Compile._IBracketed<JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mGrammar_Compile._IValue, JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mUtils_mViews_mCore_Compile._IView__> arr) {
      return new Value_Array(arr);
    }
    public bool is_Null { get { return this is Value_Null; } }
    public bool is_Bool { get { return this is Value_Bool; } }
    public bool is_String { get { return this is Value_String; } }
    public bool is_Number { get { return this is Value_Number; } }
    public bool is_Object { get { return this is Value_Object; } }
    public bool is_Array { get { return this is Value_Array; } }
    public JSON_mUtils_mViews_mCore_Compile._IView__ dtor_n {
      get {
        var d = this;
        return ((Value_Null)d)._n;
      }
    }
    public JSON_mUtils_mViews_mCore_Compile._IView__ dtor_b {
      get {
        var d = this;
        return ((Value_Bool)d)._b;
      }
    }
    public JSON_mGrammar_Compile._Ijstring dtor_str {
      get {
        var d = this;
        return ((Value_String)d)._str;
      }
    }
    public JSON_mGrammar_Compile._Ijnumber dtor_num {
      get {
        var d = this;
        return ((Value_Number)d)._num;
      }
    }
    public JSON_mGrammar_Compile._IBracketed<JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mGrammar_Compile._IjKeyValue, JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mUtils_mViews_mCore_Compile._IView__> dtor_obj {
      get {
        var d = this;
        return ((Value_Object)d)._obj;
      }
    }
    public JSON_mGrammar_Compile._IBracketed<JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mGrammar_Compile._IValue, JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mUtils_mViews_mCore_Compile._IView__> dtor_arr {
      get {
        var d = this;
        return ((Value_Array)d)._arr;
      }
    }
    public abstract _IValue DowncastClone();
  }
  public class Value_Null : Value {
    public readonly JSON_mUtils_mViews_mCore_Compile._IView__ _n;
    public Value_Null(JSON_mUtils_mViews_mCore_Compile._IView__ n) {
      this._n = n;
    }
    public override _IValue DowncastClone() {
      if (this is _IValue dt) { return dt; }
      return new Value_Null(_n);
    }
    public override bool Equals(object other) {
      var oth = other as JSON_mGrammar_Compile.Value_Null;
      return oth != null && object.Equals(this._n, oth._n);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._n));
      return (int) hash;
    }
    public override string ToString() {
      string s = "JSON_mGrammar_Compile.Value.Null";
      s += "(";
      s += Dafny.Helpers.ToString(this._n);
      s += ")";
      return s;
    }
  }
  public class Value_Bool : Value {
    public readonly JSON_mUtils_mViews_mCore_Compile._IView__ _b;
    public Value_Bool(JSON_mUtils_mViews_mCore_Compile._IView__ b) {
      this._b = b;
    }
    public override _IValue DowncastClone() {
      if (this is _IValue dt) { return dt; }
      return new Value_Bool(_b);
    }
    public override bool Equals(object other) {
      var oth = other as JSON_mGrammar_Compile.Value_Bool;
      return oth != null && object.Equals(this._b, oth._b);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._b));
      return (int) hash;
    }
    public override string ToString() {
      string s = "JSON_mGrammar_Compile.Value.Bool";
      s += "(";
      s += Dafny.Helpers.ToString(this._b);
      s += ")";
      return s;
    }
  }
  public class Value_String : Value {
    public readonly JSON_mGrammar_Compile._Ijstring _str;
    public Value_String(JSON_mGrammar_Compile._Ijstring str) {
      this._str = str;
    }
    public override _IValue DowncastClone() {
      if (this is _IValue dt) { return dt; }
      return new Value_String(_str);
    }
    public override bool Equals(object other) {
      var oth = other as JSON_mGrammar_Compile.Value_String;
      return oth != null && object.Equals(this._str, oth._str);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 2;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._str));
      return (int) hash;
    }
    public override string ToString() {
      string s = "JSON_mGrammar_Compile.Value.String";
      s += "(";
      s += Dafny.Helpers.ToString(this._str);
      s += ")";
      return s;
    }
  }
  public class Value_Number : Value {
    public readonly JSON_mGrammar_Compile._Ijnumber _num;
    public Value_Number(JSON_mGrammar_Compile._Ijnumber num) {
      this._num = num;
    }
    public override _IValue DowncastClone() {
      if (this is _IValue dt) { return dt; }
      return new Value_Number(_num);
    }
    public override bool Equals(object other) {
      var oth = other as JSON_mGrammar_Compile.Value_Number;
      return oth != null && object.Equals(this._num, oth._num);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 3;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._num));
      return (int) hash;
    }
    public override string ToString() {
      string s = "JSON_mGrammar_Compile.Value.Number";
      s += "(";
      s += Dafny.Helpers.ToString(this._num);
      s += ")";
      return s;
    }
  }
  public class Value_Object : Value {
    public readonly JSON_mGrammar_Compile._IBracketed<JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mGrammar_Compile._IjKeyValue, JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mUtils_mViews_mCore_Compile._IView__> _obj;
    public Value_Object(JSON_mGrammar_Compile._IBracketed<JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mGrammar_Compile._IjKeyValue, JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mUtils_mViews_mCore_Compile._IView__> obj) {
      this._obj = obj;
    }
    public override _IValue DowncastClone() {
      if (this is _IValue dt) { return dt; }
      return new Value_Object(_obj);
    }
    public override bool Equals(object other) {
      var oth = other as JSON_mGrammar_Compile.Value_Object;
      return oth != null && object.Equals(this._obj, oth._obj);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 4;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._obj));
      return (int) hash;
    }
    public override string ToString() {
      string s = "JSON_mGrammar_Compile.Value.Object";
      s += "(";
      s += Dafny.Helpers.ToString(this._obj);
      s += ")";
      return s;
    }
  }
  public class Value_Array : Value {
    public readonly JSON_mGrammar_Compile._IBracketed<JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mGrammar_Compile._IValue, JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mUtils_mViews_mCore_Compile._IView__> _arr;
    public Value_Array(JSON_mGrammar_Compile._IBracketed<JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mGrammar_Compile._IValue, JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mUtils_mViews_mCore_Compile._IView__> arr) {
      this._arr = arr;
    }
    public override _IValue DowncastClone() {
      if (this is _IValue dt) { return dt; }
      return new Value_Array(_arr);
    }
    public override bool Equals(object other) {
      var oth = other as JSON_mGrammar_Compile.Value_Array;
      return oth != null && object.Equals(this._arr, oth._arr);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 5;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._arr));
      return (int) hash;
    }
    public override string ToString() {
      string s = "JSON_mGrammar_Compile.Value.Array";
      s += "(";
      s += Dafny.Helpers.ToString(this._arr);
      s += ")";
      return s;
    }
  }

  public partial class __default {
    public static bool Blank_q(byte b) {
      return ((((b) == ((byte)(32))) || ((b) == ((byte)(9)))) || ((b) == ((byte)(10)))) || ((b) == ((byte)(13)));
    }
    public static bool Digit_q(byte b) {
      return (((byte)('0')) <= (b)) && ((b) <= ((byte)('9')));
    }
    public static JSON_mUtils_mViews_mCore_Compile._IView__ DOUBLEQUOTE { get {
      return JSON_mUtils_mViews_mCore_Compile.View__.OfBytes(Dafny.Sequence<byte>.FromElements((byte)('\"')));
    } }
    public static JSON_mUtils_mViews_mCore_Compile._IView__ PERIOD { get {
      return JSON_mUtils_mViews_mCore_Compile.View__.OfBytes(Dafny.Sequence<byte>.FromElements((byte)('.')));
    } }
    public static JSON_mUtils_mViews_mCore_Compile._IView__ E { get {
      return JSON_mUtils_mViews_mCore_Compile.View__.OfBytes(Dafny.Sequence<byte>.FromElements((byte)('e')));
    } }
    public static JSON_mUtils_mViews_mCore_Compile._IView__ COLON { get {
      return JSON_mUtils_mViews_mCore_Compile.View__.OfBytes(Dafny.Sequence<byte>.FromElements((byte)(':')));
    } }
    public static JSON_mUtils_mViews_mCore_Compile._IView__ COMMA { get {
      return JSON_mUtils_mViews_mCore_Compile.View__.OfBytes(Dafny.Sequence<byte>.FromElements((byte)(',')));
    } }
    public static JSON_mUtils_mViews_mCore_Compile._IView__ LBRACE { get {
      return JSON_mUtils_mViews_mCore_Compile.View__.OfBytes(Dafny.Sequence<byte>.FromElements((byte)('{')));
    } }
    public static JSON_mUtils_mViews_mCore_Compile._IView__ RBRACE { get {
      return JSON_mUtils_mViews_mCore_Compile.View__.OfBytes(Dafny.Sequence<byte>.FromElements((byte)('}')));
    } }
    public static JSON_mUtils_mViews_mCore_Compile._IView__ LBRACKET { get {
      return JSON_mUtils_mViews_mCore_Compile.View__.OfBytes(Dafny.Sequence<byte>.FromElements((byte)('[')));
    } }
    public static JSON_mUtils_mViews_mCore_Compile._IView__ RBRACKET { get {
      return JSON_mUtils_mViews_mCore_Compile.View__.OfBytes(Dafny.Sequence<byte>.FromElements((byte)(']')));
    } }
    public static JSON_mUtils_mViews_mCore_Compile._IView__ MINUS { get {
      return JSON_mUtils_mViews_mCore_Compile.View__.OfBytes(Dafny.Sequence<byte>.FromElements((byte)('-')));
    } }
    public static JSON_mUtils_mViews_mCore_Compile._IView__ EMPTY { get {
      return JSON_mUtils_mViews_mCore_Compile.View__.OfBytes(Dafny.Sequence<byte>.FromElements());
    } }
    public static Dafny.ISequence<byte> NULL { get {
      return Dafny.Sequence<byte>.FromElements((byte)('n'), (byte)('u'), (byte)('l'), (byte)('l'));
    } }
    public static Dafny.ISequence<byte> TRUE { get {
      return Dafny.Sequence<byte>.FromElements((byte)('t'), (byte)('r'), (byte)('u'), (byte)('e'));
    } }
    public static Dafny.ISequence<byte> FALSE { get {
      return Dafny.Sequence<byte>.FromElements((byte)('f'), (byte)('a'), (byte)('l'), (byte)('s'), (byte)('e'));
    } }
  }
} // end of namespace JSON_mGrammar_Compile
namespace JSON_mSerializer_mByteStrConversion_Compile {

  public partial class __default {
    public static Dafny.ISequence<BigInteger> Digits(BigInteger n, BigInteger @base)
    {
      if ((n).Sign == 0) {
        return Dafny.Sequence<BigInteger>.FromElements();
      } else {
        Dafny.ISequence<BigInteger> _465_digits_k = JSON_mSerializer_mByteStrConversion_Compile.__default.Digits(Dafny.Helpers.EuclideanDivision(n, @base), @base);
        Dafny.ISequence<BigInteger> _466_digits = Dafny.Sequence<BigInteger>.Concat(_465_digits_k, Dafny.Sequence<BigInteger>.FromElements(Dafny.Helpers.EuclideanModulus(n, @base)));
        return _466_digits;
      }
    }
    public static Dafny.ISequence<byte> OfDigits(Dafny.ISequence<BigInteger> digits, Dafny.ISequence<byte> chars)
    {
      Dafny.ISequence<byte> _467___accumulator = Dafny.Sequence<byte>.FromElements();
    TAIL_CALL_START: ;
      if ((digits).Equals(Dafny.Sequence<BigInteger>.FromElements())) {
        return Dafny.Sequence<byte>.Concat(_467___accumulator, Dafny.Sequence<byte>.FromElements());
      } else {
        _467___accumulator = Dafny.Sequence<byte>.Concat(_467___accumulator, Dafny.Sequence<byte>.FromElements((chars).Select((digits).Select(BigInteger.Zero))));
        Dafny.ISequence<BigInteger> _in103 = (digits).Drop(BigInteger.One);
        Dafny.ISequence<byte> _in104 = chars;
        digits = _in103;
        chars = _in104;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<byte> OfNat__any(BigInteger n, Dafny.ISequence<byte> chars)
    {
      BigInteger _468_base = new BigInteger((chars).Count);
      if ((n).Sign == 0) {
        return Dafny.Sequence<byte>.FromElements((chars).Select(BigInteger.Zero));
      } else {
        return JSON_mSerializer_mByteStrConversion_Compile.__default.OfDigits(JSON_mSerializer_mByteStrConversion_Compile.__default.Digits(n, _468_base), chars);
      }
    }
    public static bool NumberStr(Dafny.ISequence<byte> str, byte minus, Func<byte, bool> is__digit)
    {
      return !(!(str).Equals(Dafny.Sequence<byte>.FromElements())) || (((((str).Select(BigInteger.Zero)) == (minus)) || (Dafny.Helpers.Id<Func<byte, bool>>(is__digit)((str).Select(BigInteger.Zero)))) && (Dafny.Helpers.Id<Func<Dafny.ISequence<byte>, Func<byte, bool>, bool>>((_469_str, _470_is__digit) => Dafny.Helpers.Quantifier<byte>(((_469_str).Drop(BigInteger.One)).UniqueElements, true, (((_forall_var_7) => {
        byte _471_c = (byte)_forall_var_7;
        return !(((_469_str).Drop(BigInteger.One)).Contains(_471_c)) || (Dafny.Helpers.Id<Func<byte, bool>>(_470_is__digit)(_471_c));
      }))))(str, is__digit)));
    }
    public static Dafny.ISequence<byte> OfInt__any(BigInteger n, Dafny.ISequence<byte> chars, byte minus)
    {
      if ((n).Sign != -1) {
        return JSON_mSerializer_mByteStrConversion_Compile.__default.OfNat__any(n, chars);
      } else {
        return Dafny.Sequence<byte>.Concat(Dafny.Sequence<byte>.FromElements(minus), JSON_mSerializer_mByteStrConversion_Compile.__default.OfNat__any((BigInteger.Zero) - (n), chars));
      }
    }
    public static BigInteger ToNat__any(Dafny.ISequence<byte> str, BigInteger @base, Dafny.IMap<byte,BigInteger> digits)
    {
      if ((str).Equals(Dafny.Sequence<byte>.FromElements())) {
        return BigInteger.Zero;
      } else {
        return ((JSON_mSerializer_mByteStrConversion_Compile.__default.ToNat__any((str).Take((new BigInteger((str).Count)) - (BigInteger.One)), @base, digits)) * (@base)) + (Dafny.Map<byte, BigInteger>.Select(digits,(str).Select((new BigInteger((str).Count)) - (BigInteger.One))));
      }
    }
    public static BigInteger ToInt__any(Dafny.ISequence<byte> str, byte minus, BigInteger @base, Dafny.IMap<byte,BigInteger> digits)
    {
      if (Dafny.Sequence<byte>.IsPrefixOf(Dafny.Sequence<byte>.FromElements(minus), str)) {
        return (BigInteger.Zero) - (JSON_mSerializer_mByteStrConversion_Compile.__default.ToNat__any((str).Drop(BigInteger.One), @base, digits));
      } else {
        return JSON_mSerializer_mByteStrConversion_Compile.__default.ToNat__any(str, @base, digits);
      }
    }
  }
} // end of namespace JSON_mSerializer_mByteStrConversion_Compile
namespace JSON_mSerializer_Compile {

  public partial class bytes32 {
    private static readonly Dafny.TypeDescriptor<Dafny.ISequence<byte>> _TYPE = new Dafny.TypeDescriptor<Dafny.ISequence<byte>>(Dafny.Sequence<byte>.Empty);
    public static Dafny.TypeDescriptor<Dafny.ISequence<byte>> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class string32 {
    private static readonly Dafny.TypeDescriptor<Dafny.ISequence<char>> _TYPE = new Dafny.TypeDescriptor<Dafny.ISequence<char>>(Dafny.Sequence<char>.Empty);
    public static Dafny.TypeDescriptor<Dafny.ISequence<char>> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class __default {
    public static JSON_mUtils_mViews_mCore_Compile._IView__ Bool(bool b) {
      return JSON_mUtils_mViews_mCore_Compile.View__.OfBytes(((b) ? (JSON_mGrammar_Compile.__default.TRUE) : (JSON_mGrammar_Compile.__default.FALSE)));
    }
    public static Wrappers_Compile._IOutcome<JSON_mErrors_Compile._ISerializationError> CheckLength<__T>(Dafny.ISequence<__T> s, JSON_mErrors_Compile._ISerializationError err)
    {
      return Wrappers_Compile.__default.Need<JSON_mErrors_Compile._ISerializationError>((new BigInteger((s).Count)) < (BoundedInts_Compile.__default.TWO__TO__THE__32), err);
    }
    public static Wrappers_Compile._IResult<JSON_mGrammar_Compile._Ijstring, JSON_mErrors_Compile._ISerializationError> String(Dafny.ISequence<char> str) {
      Wrappers_Compile._IResult<Dafny.ISequence<byte>, JSON_mErrors_Compile._ISerializationError> _472_valueOrError0 = JSON_mSpec_Compile.__default.EscapeToUTF8(str, BigInteger.Zero);
      if ((_472_valueOrError0).IsFailure()) {
        return (_472_valueOrError0).PropagateFailure<JSON_mGrammar_Compile._Ijstring>();
      } else {
        Dafny.ISequence<byte> _473_bs = (_472_valueOrError0).Extract();
        Wrappers_Compile._IOutcome<JSON_mErrors_Compile._ISerializationError> _474_valueOrError1 = JSON_mSerializer_Compile.__default.CheckLength<byte>(_473_bs, JSON_mErrors_Compile.SerializationError.create_StringTooLong(str));
        if ((_474_valueOrError1).IsFailure()) {
          return (_474_valueOrError1).PropagateFailure<JSON_mGrammar_Compile._Ijstring>();
        } else {
          return Wrappers_Compile.Result<JSON_mGrammar_Compile._Ijstring, JSON_mErrors_Compile._ISerializationError>.create_Success(JSON_mGrammar_Compile.jstring.create(JSON_mGrammar_Compile.__default.DOUBLEQUOTE, JSON_mUtils_mViews_mCore_Compile.View__.OfBytes(_473_bs), JSON_mGrammar_Compile.__default.DOUBLEQUOTE));
        }
      }
    }
    public static JSON_mUtils_mViews_mCore_Compile._IView__ Sign(BigInteger n) {
      return JSON_mUtils_mViews_mCore_Compile.View__.OfBytes((((n).Sign == -1) ? (Dafny.Sequence<byte>.FromElements((byte)('-'))) : (Dafny.Sequence<byte>.FromElements())));
    }
    public static Dafny.ISequence<byte> Int_k(BigInteger n) {
      return JSON_mSerializer_mByteStrConversion_Compile.__default.OfInt__any(n, JSON_mSerializer_Compile.__default.DIGITS, JSON_mSerializer_Compile.__default.MINUS);
    }
    public static Wrappers_Compile._IResult<JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mErrors_Compile._ISerializationError> Int(BigInteger n) {
      Dafny.ISequence<byte> _475_bs = JSON_mSerializer_Compile.__default.Int_k(n);
      Wrappers_Compile._IOutcome<JSON_mErrors_Compile._ISerializationError> _476_valueOrError0 = JSON_mSerializer_Compile.__default.CheckLength<byte>(_475_bs, JSON_mErrors_Compile.SerializationError.create_IntTooLarge(n));
      if ((_476_valueOrError0).IsFailure()) {
        return (_476_valueOrError0).PropagateFailure<JSON_mUtils_mViews_mCore_Compile._IView__>();
      } else {
        return Wrappers_Compile.Result<JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mErrors_Compile._ISerializationError>.create_Success(JSON_mUtils_mViews_mCore_Compile.View__.OfBytes(_475_bs));
      }
    }
    public static Wrappers_Compile._IResult<JSON_mGrammar_Compile._Ijnumber, JSON_mErrors_Compile._ISerializationError> Number(JSON_mValues_Compile._IDecimal dec) {
      var _pat_let_tv4 = dec;
      var _pat_let_tv5 = dec;
      JSON_mUtils_mViews_mCore_Compile._IView__ _477_minus = JSON_mSerializer_Compile.__default.Sign((dec).dtor_n);
      Wrappers_Compile._IResult<JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mErrors_Compile._ISerializationError> _478_valueOrError0 = JSON_mSerializer_Compile.__default.Int(Math_Compile.__default.Abs((dec).dtor_n));
      if ((_478_valueOrError0).IsFailure()) {
        return (_478_valueOrError0).PropagateFailure<JSON_mGrammar_Compile._Ijnumber>();
      } else {
        JSON_mUtils_mViews_mCore_Compile._IView__ _479_num = (_478_valueOrError0).Extract();
        JSON_mGrammar_Compile._IMaybe<JSON_mGrammar_Compile._Ijfrac> _480_frac = JSON_mGrammar_Compile.Maybe<JSON_mGrammar_Compile._Ijfrac>.create_Empty();
        Wrappers_Compile._IResult<JSON_mGrammar_Compile._IMaybe<JSON_mGrammar_Compile._Ijexp>, JSON_mErrors_Compile._ISerializationError> _481_valueOrError1 = ((((dec).dtor_e10).Sign == 0) ? (Wrappers_Compile.Result<JSON_mGrammar_Compile._IMaybe<JSON_mGrammar_Compile._Ijexp>, JSON_mErrors_Compile._ISerializationError>.create_Success(JSON_mGrammar_Compile.Maybe<JSON_mGrammar_Compile._Ijexp>.create_Empty())) : (Dafny.Helpers.Let<JSON_mUtils_mViews_mCore_Compile._IView__, Wrappers_Compile._IResult<JSON_mGrammar_Compile._IMaybe<JSON_mGrammar_Compile._Ijexp>, JSON_mErrors_Compile._ISerializationError>>(JSON_mUtils_mViews_mCore_Compile.View__.OfBytes(Dafny.Sequence<byte>.FromElements((byte)('e'))), _pat_let2_0 => Dafny.Helpers.Let<JSON_mUtils_mViews_mCore_Compile._IView__, Wrappers_Compile._IResult<JSON_mGrammar_Compile._IMaybe<JSON_mGrammar_Compile._Ijexp>, JSON_mErrors_Compile._ISerializationError>>(_pat_let2_0, _482_e => Dafny.Helpers.Let<JSON_mUtils_mViews_mCore_Compile._IView__, Wrappers_Compile._IResult<JSON_mGrammar_Compile._IMaybe<JSON_mGrammar_Compile._Ijexp>, JSON_mErrors_Compile._ISerializationError>>(JSON_mSerializer_Compile.__default.Sign((_pat_let_tv4).dtor_e10), _pat_let3_0 => Dafny.Helpers.Let<JSON_mUtils_mViews_mCore_Compile._IView__, Wrappers_Compile._IResult<JSON_mGrammar_Compile._IMaybe<JSON_mGrammar_Compile._Ijexp>, JSON_mErrors_Compile._ISerializationError>>(_pat_let3_0, _483_sign => Dafny.Helpers.Let<Wrappers_Compile._IResult<JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mErrors_Compile._ISerializationError>, Wrappers_Compile._IResult<JSON_mGrammar_Compile._IMaybe<JSON_mGrammar_Compile._Ijexp>, JSON_mErrors_Compile._ISerializationError>>(JSON_mSerializer_Compile.__default.Int(Math_Compile.__default.Abs((_pat_let_tv5).dtor_e10)), _pat_let4_0 => Dafny.Helpers.Let<Wrappers_Compile._IResult<JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mErrors_Compile._ISerializationError>, Wrappers_Compile._IResult<JSON_mGrammar_Compile._IMaybe<JSON_mGrammar_Compile._Ijexp>, JSON_mErrors_Compile._ISerializationError>>(_pat_let4_0, _484_valueOrError2 => (((_484_valueOrError2).IsFailure()) ? ((_484_valueOrError2).PropagateFailure<JSON_mGrammar_Compile._IMaybe<JSON_mGrammar_Compile._Ijexp>>()) : (Dafny.Helpers.Let<JSON_mUtils_mViews_mCore_Compile._IView__, Wrappers_Compile._IResult<JSON_mGrammar_Compile._IMaybe<JSON_mGrammar_Compile._Ijexp>, JSON_mErrors_Compile._ISerializationError>>((_484_valueOrError2).Extract(), _pat_let5_0 => Dafny.Helpers.Let<JSON_mUtils_mViews_mCore_Compile._IView__, Wrappers_Compile._IResult<JSON_mGrammar_Compile._IMaybe<JSON_mGrammar_Compile._Ijexp>, JSON_mErrors_Compile._ISerializationError>>(_pat_let5_0, _485_num => Wrappers_Compile.Result<JSON_mGrammar_Compile._IMaybe<JSON_mGrammar_Compile._Ijexp>, JSON_mErrors_Compile._ISerializationError>.create_Success(JSON_mGrammar_Compile.Maybe<JSON_mGrammar_Compile._Ijexp>.create_NonEmpty(JSON_mGrammar_Compile.jexp.create(_482_e, _483_sign, _485_num)))))))))))))));
        if ((_481_valueOrError1).IsFailure()) {
          return (_481_valueOrError1).PropagateFailure<JSON_mGrammar_Compile._Ijnumber>();
        } else {
          JSON_mGrammar_Compile._IMaybe<JSON_mGrammar_Compile._Ijexp> _486_exp = (_481_valueOrError1).Extract();
          return Wrappers_Compile.Result<JSON_mGrammar_Compile._Ijnumber, JSON_mErrors_Compile._ISerializationError>.create_Success(JSON_mGrammar_Compile.jnumber.create(_477_minus, _479_num, JSON_mGrammar_Compile.Maybe<JSON_mGrammar_Compile._Ijfrac>.create_Empty(), _486_exp));
        }
      }
    }
    public static JSON_mGrammar_Compile._IStructural<__T> MkStructural<__T>(__T v) {
      return JSON_mGrammar_Compile.Structural<__T>.create(JSON_mGrammar_Compile.__default.EMPTY, v, JSON_mGrammar_Compile.__default.EMPTY);
    }
    public static Wrappers_Compile._IResult<JSON_mGrammar_Compile._IjKeyValue, JSON_mErrors_Compile._ISerializationError> KeyValue(_System._ITuple2<Dafny.ISequence<char>, JSON_mValues_Compile._IJSON> kv) {
      Wrappers_Compile._IResult<JSON_mGrammar_Compile._Ijstring, JSON_mErrors_Compile._ISerializationError> _487_valueOrError0 = JSON_mSerializer_Compile.__default.String((kv).dtor__0);
      if ((_487_valueOrError0).IsFailure()) {
        return (_487_valueOrError0).PropagateFailure<JSON_mGrammar_Compile._IjKeyValue>();
      } else {
        JSON_mGrammar_Compile._Ijstring _488_k = (_487_valueOrError0).Extract();
        Wrappers_Compile._IResult<JSON_mGrammar_Compile._IValue, JSON_mErrors_Compile._ISerializationError> _489_valueOrError1 = JSON_mSerializer_Compile.__default.Value((kv).dtor__1);
        if ((_489_valueOrError1).IsFailure()) {
          return (_489_valueOrError1).PropagateFailure<JSON_mGrammar_Compile._IjKeyValue>();
        } else {
          JSON_mGrammar_Compile._IValue _490_v = (_489_valueOrError1).Extract();
          return Wrappers_Compile.Result<JSON_mGrammar_Compile._IjKeyValue, JSON_mErrors_Compile._ISerializationError>.create_Success(JSON_mGrammar_Compile.jKeyValue.create(_488_k, JSON_mSerializer_Compile.__default.COLON, _490_v));
        }
      }
    }
    public static Dafny.ISequence<JSON_mGrammar_Compile._ISuffixed<__D, __S>> MkSuffixedSequence<__D, __S>(Dafny.ISequence<__D> ds, JSON_mGrammar_Compile._IStructural<__S> suffix, BigInteger start)
    {
      Dafny.ISequence<JSON_mGrammar_Compile._ISuffixed<__D, __S>> _491___accumulator = Dafny.Sequence<JSON_mGrammar_Compile._ISuffixed<__D, __S>>.FromElements();
    TAIL_CALL_START: ;
      if ((start) >= (new BigInteger((ds).Count))) {
        return Dafny.Sequence<JSON_mGrammar_Compile._ISuffixed<__D, __S>>.Concat(_491___accumulator, Dafny.Sequence<JSON_mGrammar_Compile._ISuffixed<__D, __S>>.FromElements());
      } else if ((start) == ((new BigInteger((ds).Count)) - (BigInteger.One))) {
        return Dafny.Sequence<JSON_mGrammar_Compile._ISuffixed<__D, __S>>.Concat(_491___accumulator, Dafny.Sequence<JSON_mGrammar_Compile._ISuffixed<__D, __S>>.FromElements(JSON_mGrammar_Compile.Suffixed<__D, __S>.create((ds).Select(start), JSON_mGrammar_Compile.Maybe<JSON_mGrammar_Compile._IStructural<__S>>.create_Empty())));
      } else {
        _491___accumulator = Dafny.Sequence<JSON_mGrammar_Compile._ISuffixed<__D, __S>>.Concat(_491___accumulator, Dafny.Sequence<JSON_mGrammar_Compile._ISuffixed<__D, __S>>.FromElements(JSON_mGrammar_Compile.Suffixed<__D, __S>.create((ds).Select(start), JSON_mGrammar_Compile.Maybe<JSON_mGrammar_Compile._IStructural<__S>>.create_NonEmpty(suffix))));
        Dafny.ISequence<__D> _in105 = ds;
        JSON_mGrammar_Compile._IStructural<__S> _in106 = suffix;
        BigInteger _in107 = (start) + (BigInteger.One);
        ds = _in105;
        suffix = _in106;
        start = _in107;
        goto TAIL_CALL_START;
      }
    }
    public static Wrappers_Compile._IResult<JSON_mGrammar_Compile._IBracketed<JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mGrammar_Compile._IjKeyValue, JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mUtils_mViews_mCore_Compile._IView__>, JSON_mErrors_Compile._ISerializationError> Object(Dafny.ISequence<_System._ITuple2<Dafny.ISequence<char>, JSON_mValues_Compile._IJSON>> obj) {
      Wrappers_Compile._IResult<Dafny.ISequence<JSON_mGrammar_Compile._IjKeyValue>, JSON_mErrors_Compile._ISerializationError> _492_valueOrError0 = Seq_Compile.__default.MapWithResult<_System._ITuple2<Dafny.ISequence<char>, JSON_mValues_Compile._IJSON>, JSON_mGrammar_Compile._IjKeyValue, JSON_mErrors_Compile._ISerializationError>(Dafny.Helpers.Id<Func<Dafny.ISequence<_System._ITuple2<Dafny.ISequence<char>, JSON_mValues_Compile._IJSON>>, Func<_System._ITuple2<Dafny.ISequence<char>, JSON_mValues_Compile._IJSON>, Wrappers_Compile._IResult<JSON_mGrammar_Compile._IjKeyValue, JSON_mErrors_Compile._ISerializationError>>>>((_493_obj) => ((System.Func<_System._ITuple2<Dafny.ISequence<char>, JSON_mValues_Compile._IJSON>, Wrappers_Compile._IResult<JSON_mGrammar_Compile._IjKeyValue, JSON_mErrors_Compile._ISerializationError>>)((_494_v) => {
        return JSON_mSerializer_Compile.__default.KeyValue(_494_v);
      })))(obj), obj);
      if ((_492_valueOrError0).IsFailure()) {
        return (_492_valueOrError0).PropagateFailure<JSON_mGrammar_Compile._IBracketed<JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mGrammar_Compile._IjKeyValue, JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mUtils_mViews_mCore_Compile._IView__>>();
      } else {
        Dafny.ISequence<JSON_mGrammar_Compile._IjKeyValue> _495_items = (_492_valueOrError0).Extract();
        return Wrappers_Compile.Result<JSON_mGrammar_Compile._IBracketed<JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mGrammar_Compile._IjKeyValue, JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mUtils_mViews_mCore_Compile._IView__>, JSON_mErrors_Compile._ISerializationError>.create_Success(JSON_mGrammar_Compile.Bracketed<JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mGrammar_Compile._IjKeyValue, JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mUtils_mViews_mCore_Compile._IView__>.create(JSON_mSerializer_Compile.__default.MkStructural<JSON_mUtils_mViews_mCore_Compile._IView__>(JSON_mGrammar_Compile.__default.LBRACE), JSON_mSerializer_Compile.__default.MkSuffixedSequence<JSON_mGrammar_Compile._IjKeyValue, JSON_mUtils_mViews_mCore_Compile._IView__>(_495_items, JSON_mSerializer_Compile.__default.COMMA, BigInteger.Zero), JSON_mSerializer_Compile.__default.MkStructural<JSON_mUtils_mViews_mCore_Compile._IView__>(JSON_mGrammar_Compile.__default.RBRACE)));
      }
    }
    public static Wrappers_Compile._IResult<JSON_mGrammar_Compile._IBracketed<JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mGrammar_Compile._IValue, JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mUtils_mViews_mCore_Compile._IView__>, JSON_mErrors_Compile._ISerializationError> Array(Dafny.ISequence<JSON_mValues_Compile._IJSON> arr) {
      Wrappers_Compile._IResult<Dafny.ISequence<JSON_mGrammar_Compile._IValue>, JSON_mErrors_Compile._ISerializationError> _496_valueOrError0 = Seq_Compile.__default.MapWithResult<JSON_mValues_Compile._IJSON, JSON_mGrammar_Compile._IValue, JSON_mErrors_Compile._ISerializationError>(Dafny.Helpers.Id<Func<Dafny.ISequence<JSON_mValues_Compile._IJSON>, Func<JSON_mValues_Compile._IJSON, Wrappers_Compile._IResult<JSON_mGrammar_Compile._IValue, JSON_mErrors_Compile._ISerializationError>>>>((_497_arr) => ((System.Func<JSON_mValues_Compile._IJSON, Wrappers_Compile._IResult<JSON_mGrammar_Compile._IValue, JSON_mErrors_Compile._ISerializationError>>)((_498_v) => {
        return JSON_mSerializer_Compile.__default.Value(_498_v);
      })))(arr), arr);
      if ((_496_valueOrError0).IsFailure()) {
        return (_496_valueOrError0).PropagateFailure<JSON_mGrammar_Compile._IBracketed<JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mGrammar_Compile._IValue, JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mUtils_mViews_mCore_Compile._IView__>>();
      } else {
        Dafny.ISequence<JSON_mGrammar_Compile._IValue> _499_items = (_496_valueOrError0).Extract();
        return Wrappers_Compile.Result<JSON_mGrammar_Compile._IBracketed<JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mGrammar_Compile._IValue, JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mUtils_mViews_mCore_Compile._IView__>, JSON_mErrors_Compile._ISerializationError>.create_Success(JSON_mGrammar_Compile.Bracketed<JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mGrammar_Compile._IValue, JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mUtils_mViews_mCore_Compile._IView__>.create(JSON_mSerializer_Compile.__default.MkStructural<JSON_mUtils_mViews_mCore_Compile._IView__>(JSON_mGrammar_Compile.__default.LBRACKET), JSON_mSerializer_Compile.__default.MkSuffixedSequence<JSON_mGrammar_Compile._IValue, JSON_mUtils_mViews_mCore_Compile._IView__>(_499_items, JSON_mSerializer_Compile.__default.COMMA, BigInteger.Zero), JSON_mSerializer_Compile.__default.MkStructural<JSON_mUtils_mViews_mCore_Compile._IView__>(JSON_mGrammar_Compile.__default.RBRACKET)));
      }
    }
    public static Wrappers_Compile._IResult<JSON_mGrammar_Compile._IValue, JSON_mErrors_Compile._ISerializationError> Value(JSON_mValues_Compile._IJSON js) {
      JSON_mValues_Compile._IJSON _source12 = js;
      if (_source12.is_Null) {
        return Wrappers_Compile.Result<JSON_mGrammar_Compile._IValue, JSON_mErrors_Compile._ISerializationError>.create_Success(JSON_mGrammar_Compile.Value.create_Null(JSON_mUtils_mViews_mCore_Compile.View__.OfBytes(JSON_mGrammar_Compile.__default.NULL)));
      } else if (_source12.is_Bool) {
        bool _500___mcc_h0 = _source12.dtor_b;
        bool _501_b = _500___mcc_h0;
        return Wrappers_Compile.Result<JSON_mGrammar_Compile._IValue, JSON_mErrors_Compile._ISerializationError>.create_Success(JSON_mGrammar_Compile.Value.create_Bool(JSON_mSerializer_Compile.__default.Bool(_501_b)));
      } else if (_source12.is_String) {
        Dafny.ISequence<char> _502___mcc_h1 = _source12.dtor_str;
        Dafny.ISequence<char> _503_str = _502___mcc_h1;
        Wrappers_Compile._IResult<JSON_mGrammar_Compile._Ijstring, JSON_mErrors_Compile._ISerializationError> _504_valueOrError0 = JSON_mSerializer_Compile.__default.String(_503_str);
        if ((_504_valueOrError0).IsFailure()) {
          return (_504_valueOrError0).PropagateFailure<JSON_mGrammar_Compile._IValue>();
        } else {
          JSON_mGrammar_Compile._Ijstring _505_s = (_504_valueOrError0).Extract();
          return Wrappers_Compile.Result<JSON_mGrammar_Compile._IValue, JSON_mErrors_Compile._ISerializationError>.create_Success(JSON_mGrammar_Compile.Value.create_String(_505_s));
        }
      } else if (_source12.is_Number) {
        JSON_mValues_Compile._IDecimal _506___mcc_h2 = _source12.dtor_num;
        JSON_mValues_Compile._IDecimal _507_dec = _506___mcc_h2;
        Wrappers_Compile._IResult<JSON_mGrammar_Compile._Ijnumber, JSON_mErrors_Compile._ISerializationError> _508_valueOrError1 = JSON_mSerializer_Compile.__default.Number(_507_dec);
        if ((_508_valueOrError1).IsFailure()) {
          return (_508_valueOrError1).PropagateFailure<JSON_mGrammar_Compile._IValue>();
        } else {
          JSON_mGrammar_Compile._Ijnumber _509_n = (_508_valueOrError1).Extract();
          return Wrappers_Compile.Result<JSON_mGrammar_Compile._IValue, JSON_mErrors_Compile._ISerializationError>.create_Success(JSON_mGrammar_Compile.Value.create_Number(_509_n));
        }
      } else if (_source12.is_Object) {
        Dafny.ISequence<_System._ITuple2<Dafny.ISequence<char>, JSON_mValues_Compile._IJSON>> _510___mcc_h3 = _source12.dtor_obj;
        Dafny.ISequence<_System._ITuple2<Dafny.ISequence<char>, JSON_mValues_Compile._IJSON>> _511_obj = _510___mcc_h3;
        Wrappers_Compile._IResult<JSON_mGrammar_Compile._IBracketed<JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mGrammar_Compile._IjKeyValue, JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mUtils_mViews_mCore_Compile._IView__>, JSON_mErrors_Compile._ISerializationError> _512_valueOrError2 = JSON_mSerializer_Compile.__default.Object(_511_obj);
        if ((_512_valueOrError2).IsFailure()) {
          return (_512_valueOrError2).PropagateFailure<JSON_mGrammar_Compile._IValue>();
        } else {
          JSON_mGrammar_Compile._IBracketed<JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mGrammar_Compile._IjKeyValue, JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mUtils_mViews_mCore_Compile._IView__> _513_o = (_512_valueOrError2).Extract();
          return Wrappers_Compile.Result<JSON_mGrammar_Compile._IValue, JSON_mErrors_Compile._ISerializationError>.create_Success(JSON_mGrammar_Compile.Value.create_Object(_513_o));
        }
      } else {
        Dafny.ISequence<JSON_mValues_Compile._IJSON> _514___mcc_h4 = _source12.dtor_arr;
        Dafny.ISequence<JSON_mValues_Compile._IJSON> _515_arr = _514___mcc_h4;
        Wrappers_Compile._IResult<JSON_mGrammar_Compile._IBracketed<JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mGrammar_Compile._IValue, JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mUtils_mViews_mCore_Compile._IView__>, JSON_mErrors_Compile._ISerializationError> _516_valueOrError3 = JSON_mSerializer_Compile.__default.Array(_515_arr);
        if ((_516_valueOrError3).IsFailure()) {
          return (_516_valueOrError3).PropagateFailure<JSON_mGrammar_Compile._IValue>();
        } else {
          JSON_mGrammar_Compile._IBracketed<JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mGrammar_Compile._IValue, JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mUtils_mViews_mCore_Compile._IView__> _517_a = (_516_valueOrError3).Extract();
          return Wrappers_Compile.Result<JSON_mGrammar_Compile._IValue, JSON_mErrors_Compile._ISerializationError>.create_Success(JSON_mGrammar_Compile.Value.create_Array(_517_a));
        }
      }
    }
    public static Wrappers_Compile._IResult<JSON_mGrammar_Compile._IStructural<JSON_mGrammar_Compile._IValue>, JSON_mErrors_Compile._ISerializationError> JSON(JSON_mValues_Compile._IJSON js) {
      Wrappers_Compile._IResult<JSON_mGrammar_Compile._IValue, JSON_mErrors_Compile._ISerializationError> _518_valueOrError0 = JSON_mSerializer_Compile.__default.Value(js);
      if ((_518_valueOrError0).IsFailure()) {
        return (_518_valueOrError0).PropagateFailure<JSON_mGrammar_Compile._IStructural<JSON_mGrammar_Compile._IValue>>();
      } else {
        JSON_mGrammar_Compile._IValue _519_val = (_518_valueOrError0).Extract();
        return Wrappers_Compile.Result<JSON_mGrammar_Compile._IStructural<JSON_mGrammar_Compile._IValue>, JSON_mErrors_Compile._ISerializationError>.create_Success(JSON_mSerializer_Compile.__default.MkStructural<JSON_mGrammar_Compile._IValue>(_519_val));
      }
    }
    public static Dafny.ISequence<byte> DIGITS { get {
      return Dafny.Sequence<byte>.FromElements((byte)('0'), (byte)('1'), (byte)('2'), (byte)('3'), (byte)('4'), (byte)('5'), (byte)('6'), (byte)('7'), (byte)('8'), (byte)('9'));
    } }
    public static byte MINUS { get {
      return (byte)('-');
    } }
    public static JSON_mGrammar_Compile._IStructural<JSON_mUtils_mViews_mCore_Compile._IView__> COLON { get {
      return JSON_mSerializer_Compile.__default.MkStructural<JSON_mUtils_mViews_mCore_Compile._IView__>(JSON_mGrammar_Compile.__default.COLON);
    } }
    public static JSON_mGrammar_Compile._IStructural<JSON_mUtils_mViews_mCore_Compile._IView__> COMMA { get {
      return JSON_mSerializer_Compile.__default.MkStructural<JSON_mUtils_mViews_mCore_Compile._IView__>(JSON_mGrammar_Compile.__default.COMMA);
    } }
  }
} // end of namespace JSON_mSerializer_Compile
namespace JSON_mDeserializer_mUint16StrConversion_Compile {

  public partial class __default {
    public static Dafny.ISequence<BigInteger> Digits(BigInteger n, BigInteger @base)
    {
      if ((n).Sign == 0) {
        return Dafny.Sequence<BigInteger>.FromElements();
      } else {
        Dafny.ISequence<BigInteger> _520_digits_k = JSON_mDeserializer_mUint16StrConversion_Compile.__default.Digits(Dafny.Helpers.EuclideanDivision(n, @base), @base);
        Dafny.ISequence<BigInteger> _521_digits = Dafny.Sequence<BigInteger>.Concat(_520_digits_k, Dafny.Sequence<BigInteger>.FromElements(Dafny.Helpers.EuclideanModulus(n, @base)));
        return _521_digits;
      }
    }
    public static Dafny.ISequence<ushort> OfDigits(Dafny.ISequence<BigInteger> digits, Dafny.ISequence<ushort> chars)
    {
      Dafny.ISequence<ushort> _522___accumulator = Dafny.Sequence<ushort>.FromElements();
    TAIL_CALL_START: ;
      if ((digits).Equals(Dafny.Sequence<BigInteger>.FromElements())) {
        return Dafny.Sequence<ushort>.Concat(_522___accumulator, Dafny.Sequence<ushort>.FromElements());
      } else {
        _522___accumulator = Dafny.Sequence<ushort>.Concat(_522___accumulator, Dafny.Sequence<ushort>.FromElements((chars).Select((digits).Select(BigInteger.Zero))));
        Dafny.ISequence<BigInteger> _in108 = (digits).Drop(BigInteger.One);
        Dafny.ISequence<ushort> _in109 = chars;
        digits = _in108;
        chars = _in109;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<ushort> OfNat__any(BigInteger n, Dafny.ISequence<ushort> chars)
    {
      BigInteger _523_base = new BigInteger((chars).Count);
      if ((n).Sign == 0) {
        return Dafny.Sequence<ushort>.FromElements((chars).Select(BigInteger.Zero));
      } else {
        return JSON_mDeserializer_mUint16StrConversion_Compile.__default.OfDigits(JSON_mDeserializer_mUint16StrConversion_Compile.__default.Digits(n, _523_base), chars);
      }
    }
    public static bool NumberStr(Dafny.ISequence<ushort> str, ushort minus, Func<ushort, bool> is__digit)
    {
      return !(!(str).Equals(Dafny.Sequence<ushort>.FromElements())) || (((((str).Select(BigInteger.Zero)) == (minus)) || (Dafny.Helpers.Id<Func<ushort, bool>>(is__digit)((str).Select(BigInteger.Zero)))) && (Dafny.Helpers.Id<Func<Dafny.ISequence<ushort>, Func<ushort, bool>, bool>>((_524_str, _525_is__digit) => Dafny.Helpers.Quantifier<ushort>(((_524_str).Drop(BigInteger.One)).UniqueElements, true, (((_forall_var_8) => {
        ushort _526_c = (ushort)_forall_var_8;
        return !(((_524_str).Drop(BigInteger.One)).Contains(_526_c)) || (Dafny.Helpers.Id<Func<ushort, bool>>(_525_is__digit)(_526_c));
      }))))(str, is__digit)));
    }
    public static Dafny.ISequence<ushort> OfInt__any(BigInteger n, Dafny.ISequence<ushort> chars, ushort minus)
    {
      if ((n).Sign != -1) {
        return JSON_mDeserializer_mUint16StrConversion_Compile.__default.OfNat__any(n, chars);
      } else {
        return Dafny.Sequence<ushort>.Concat(Dafny.Sequence<ushort>.FromElements(minus), JSON_mDeserializer_mUint16StrConversion_Compile.__default.OfNat__any((BigInteger.Zero) - (n), chars));
      }
    }
    public static BigInteger ToNat__any(Dafny.ISequence<ushort> str, BigInteger @base, Dafny.IMap<ushort,BigInteger> digits)
    {
      if ((str).Equals(Dafny.Sequence<ushort>.FromElements())) {
        return BigInteger.Zero;
      } else {
        return ((JSON_mDeserializer_mUint16StrConversion_Compile.__default.ToNat__any((str).Take((new BigInteger((str).Count)) - (BigInteger.One)), @base, digits)) * (@base)) + (Dafny.Map<ushort, BigInteger>.Select(digits,(str).Select((new BigInteger((str).Count)) - (BigInteger.One))));
      }
    }
    public static BigInteger ToInt__any(Dafny.ISequence<ushort> str, ushort minus, BigInteger @base, Dafny.IMap<ushort,BigInteger> digits)
    {
      if (Dafny.Sequence<ushort>.IsPrefixOf(Dafny.Sequence<ushort>.FromElements(minus), str)) {
        return (BigInteger.Zero) - (JSON_mDeserializer_mUint16StrConversion_Compile.__default.ToNat__any((str).Drop(BigInteger.One), @base, digits));
      } else {
        return JSON_mDeserializer_mUint16StrConversion_Compile.__default.ToNat__any(str, @base, digits);
      }
    }
  }
} // end of namespace JSON_mDeserializer_mUint16StrConversion_Compile
namespace JSON_mDeserializer_mByteStrConversion_Compile {

  public partial class __default {
    public static Dafny.ISequence<BigInteger> Digits(BigInteger n, BigInteger @base)
    {
      if ((n).Sign == 0) {
        return Dafny.Sequence<BigInteger>.FromElements();
      } else {
        Dafny.ISequence<BigInteger> _527_digits_k = JSON_mDeserializer_mByteStrConversion_Compile.__default.Digits(Dafny.Helpers.EuclideanDivision(n, @base), @base);
        Dafny.ISequence<BigInteger> _528_digits = Dafny.Sequence<BigInteger>.Concat(_527_digits_k, Dafny.Sequence<BigInteger>.FromElements(Dafny.Helpers.EuclideanModulus(n, @base)));
        return _528_digits;
      }
    }
    public static Dafny.ISequence<byte> OfDigits(Dafny.ISequence<BigInteger> digits, Dafny.ISequence<byte> chars)
    {
      Dafny.ISequence<byte> _529___accumulator = Dafny.Sequence<byte>.FromElements();
    TAIL_CALL_START: ;
      if ((digits).Equals(Dafny.Sequence<BigInteger>.FromElements())) {
        return Dafny.Sequence<byte>.Concat(_529___accumulator, Dafny.Sequence<byte>.FromElements());
      } else {
        _529___accumulator = Dafny.Sequence<byte>.Concat(_529___accumulator, Dafny.Sequence<byte>.FromElements((chars).Select((digits).Select(BigInteger.Zero))));
        Dafny.ISequence<BigInteger> _in110 = (digits).Drop(BigInteger.One);
        Dafny.ISequence<byte> _in111 = chars;
        digits = _in110;
        chars = _in111;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<byte> OfNat__any(BigInteger n, Dafny.ISequence<byte> chars)
    {
      BigInteger _530_base = new BigInteger((chars).Count);
      if ((n).Sign == 0) {
        return Dafny.Sequence<byte>.FromElements((chars).Select(BigInteger.Zero));
      } else {
        return JSON_mDeserializer_mByteStrConversion_Compile.__default.OfDigits(JSON_mDeserializer_mByteStrConversion_Compile.__default.Digits(n, _530_base), chars);
      }
    }
    public static bool NumberStr(Dafny.ISequence<byte> str, byte minus, Func<byte, bool> is__digit)
    {
      return !(!(str).Equals(Dafny.Sequence<byte>.FromElements())) || (((((str).Select(BigInteger.Zero)) == (minus)) || (Dafny.Helpers.Id<Func<byte, bool>>(is__digit)((str).Select(BigInteger.Zero)))) && (Dafny.Helpers.Id<Func<Dafny.ISequence<byte>, Func<byte, bool>, bool>>((_531_str, _532_is__digit) => Dafny.Helpers.Quantifier<byte>(((_531_str).Drop(BigInteger.One)).UniqueElements, true, (((_forall_var_9) => {
        byte _533_c = (byte)_forall_var_9;
        return !(((_531_str).Drop(BigInteger.One)).Contains(_533_c)) || (Dafny.Helpers.Id<Func<byte, bool>>(_532_is__digit)(_533_c));
      }))))(str, is__digit)));
    }
    public static Dafny.ISequence<byte> OfInt__any(BigInteger n, Dafny.ISequence<byte> chars, byte minus)
    {
      if ((n).Sign != -1) {
        return JSON_mDeserializer_mByteStrConversion_Compile.__default.OfNat__any(n, chars);
      } else {
        return Dafny.Sequence<byte>.Concat(Dafny.Sequence<byte>.FromElements(minus), JSON_mDeserializer_mByteStrConversion_Compile.__default.OfNat__any((BigInteger.Zero) - (n), chars));
      }
    }
    public static BigInteger ToNat__any(Dafny.ISequence<byte> str, BigInteger @base, Dafny.IMap<byte,BigInteger> digits)
    {
      if ((str).Equals(Dafny.Sequence<byte>.FromElements())) {
        return BigInteger.Zero;
      } else {
        return ((JSON_mDeserializer_mByteStrConversion_Compile.__default.ToNat__any((str).Take((new BigInteger((str).Count)) - (BigInteger.One)), @base, digits)) * (@base)) + (Dafny.Map<byte, BigInteger>.Select(digits,(str).Select((new BigInteger((str).Count)) - (BigInteger.One))));
      }
    }
    public static BigInteger ToInt__any(Dafny.ISequence<byte> str, byte minus, BigInteger @base, Dafny.IMap<byte,BigInteger> digits)
    {
      if (Dafny.Sequence<byte>.IsPrefixOf(Dafny.Sequence<byte>.FromElements(minus), str)) {
        return (BigInteger.Zero) - (JSON_mDeserializer_mByteStrConversion_Compile.__default.ToNat__any((str).Drop(BigInteger.One), @base, digits));
      } else {
        return JSON_mDeserializer_mByteStrConversion_Compile.__default.ToNat__any(str, @base, digits);
      }
    }
  }
} // end of namespace JSON_mDeserializer_mByteStrConversion_Compile
namespace JSON_mDeserializer_Compile {

  public partial class __default {
    public static bool Bool(JSON_mUtils_mViews_mCore_Compile._IView__ js) {
      return ((js).At(0U)) == ((byte)('t'));
    }
    public static JSON_mErrors_Compile._IDeserializationError UnsupportedEscape16(Dafny.ISequence<ushort> code) {
      return JSON_mErrors_Compile.DeserializationError.create_UnsupportedEscape(Wrappers_Compile.Option<Dafny.ISequence<char>>.UnwrapOr(UnicodeStrings_Compile.__default.FromUTF16Checked(code), Dafny.Sequence<char>.FromString("Couldn't decode UTF-16")));
    }
    public static ushort ToNat16(Dafny.ISequence<ushort> str) {
      BigInteger _534_hd = JSON_mDeserializer_mUint16StrConversion_Compile.__default.ToNat__any(str, new BigInteger(16), JSON_mDeserializer_Compile.__default.HEX__TABLE__16);
      return (ushort)(_534_hd);
    }
    public static Wrappers_Compile._IResult<Dafny.ISequence<ushort>, JSON_mErrors_Compile._IDeserializationError> Unescape(Dafny.ISequence<ushort> str, BigInteger start, Dafny.ISequence<ushort> prefix)
    {
    TAIL_CALL_START: ;
      if ((start) >= (new BigInteger((str).Count))) {
        return Wrappers_Compile.Result<Dafny.ISequence<ushort>, JSON_mErrors_Compile._IDeserializationError>.create_Success(prefix);
      } else if (((str).Select(start)) == ((ushort)('\\'))) {
        if ((new BigInteger((str).Count)) == ((start) + (BigInteger.One))) {
          return Wrappers_Compile.Result<Dafny.ISequence<ushort>, JSON_mErrors_Compile._IDeserializationError>.create_Failure(JSON_mErrors_Compile.DeserializationError.create_EscapeAtEOS());
        } else {
          ushort _535_c = (str).Select((start) + (BigInteger.One));
          if ((_535_c) == ((ushort)('u'))) {
            if ((new BigInteger((str).Count)) <= ((start) + (new BigInteger(6)))) {
              return Wrappers_Compile.Result<Dafny.ISequence<ushort>, JSON_mErrors_Compile._IDeserializationError>.create_Failure(JSON_mErrors_Compile.DeserializationError.create_EscapeAtEOS());
            } else {
              Dafny.ISequence<ushort> _536_code = (str).Subsequence((start) + (new BigInteger(2)), (start) + (new BigInteger(6)));
              if (Dafny.Helpers.Id<Func<Dafny.ISequence<ushort>, bool>>((_537_code) => Dafny.Helpers.Quantifier<ushort>((_537_code).UniqueElements, false, (((_exists_var_1) => {
                ushort _538_c = (ushort)_exists_var_1;
                return ((_537_code).Contains(_538_c)) && (!(JSON_mDeserializer_Compile.__default.HEX__TABLE__16).Contains(_538_c));
              }))))(_536_code)) {
                return Wrappers_Compile.Result<Dafny.ISequence<ushort>, JSON_mErrors_Compile._IDeserializationError>.create_Failure(JSON_mDeserializer_Compile.__default.UnsupportedEscape16(_536_code));
              } else {
                ushort _539_hd = JSON_mDeserializer_Compile.__default.ToNat16(_536_code);
                Dafny.ISequence<ushort> _in112 = str;
                BigInteger _in113 = (start) + (new BigInteger(6));
                Dafny.ISequence<ushort> _in114 = Dafny.Sequence<ushort>.Concat(prefix, Dafny.Sequence<ushort>.FromElements(_539_hd));
                str = _in112;
                start = _in113;
                prefix = _in114;
                goto TAIL_CALL_START;
              }
            }
          } else {
            ushort _540_unescaped = (((_535_c) == ((ushort)(34))) ? ((ushort)(34)) : ((((_535_c) == ((ushort)(92))) ? ((ushort)(92)) : ((((_535_c) == ((ushort)(98))) ? ((ushort)(8)) : ((((_535_c) == ((ushort)(102))) ? ((ushort)(12)) : ((((_535_c) == ((ushort)(110))) ? ((ushort)(10)) : ((((_535_c) == ((ushort)(114))) ? ((ushort)(13)) : ((((_535_c) == ((ushort)(116))) ? ((ushort)(9)) : ((ushort)(0)))))))))))))));
            if ((new BigInteger(_540_unescaped)).Sign == 0) {
              return Wrappers_Compile.Result<Dafny.ISequence<ushort>, JSON_mErrors_Compile._IDeserializationError>.create_Failure(JSON_mDeserializer_Compile.__default.UnsupportedEscape16((str).Subsequence(start, (start) + (new BigInteger(2)))));
            } else {
              Dafny.ISequence<ushort> _in115 = str;
              BigInteger _in116 = (start) + (new BigInteger(2));
              Dafny.ISequence<ushort> _in117 = Dafny.Sequence<ushort>.Concat(prefix, Dafny.Sequence<ushort>.FromElements(_540_unescaped));
              str = _in115;
              start = _in116;
              prefix = _in117;
              goto TAIL_CALL_START;
            }
          }
        }
      } else {
        Dafny.ISequence<ushort> _in118 = str;
        BigInteger _in119 = (start) + (BigInteger.One);
        Dafny.ISequence<ushort> _in120 = Dafny.Sequence<ushort>.Concat(prefix, Dafny.Sequence<ushort>.FromElements((str).Select(start)));
        str = _in118;
        start = _in119;
        prefix = _in120;
        goto TAIL_CALL_START;
      }
    }
    public static Wrappers_Compile._IResult<Dafny.ISequence<char>, JSON_mErrors_Compile._IDeserializationError> String(JSON_mGrammar_Compile._Ijstring js) {
      Wrappers_Compile._IResult<Dafny.ISequence<char>, JSON_mErrors_Compile._IDeserializationError> _541_valueOrError0 = (UnicodeStrings_Compile.__default.FromUTF8Checked(((js).dtor_contents).Bytes())).ToResult_k<JSON_mErrors_Compile._IDeserializationError>(JSON_mErrors_Compile.DeserializationError.create_InvalidUnicode());
      if ((_541_valueOrError0).IsFailure()) {
        return (_541_valueOrError0).PropagateFailure<Dafny.ISequence<char>>();
      } else {
        Dafny.ISequence<char> _542_asUtf32 = (_541_valueOrError0).Extract();
        Wrappers_Compile._IResult<Dafny.ISequence<ushort>, JSON_mErrors_Compile._IDeserializationError> _543_valueOrError1 = (UnicodeStrings_Compile.__default.ToUTF16Checked(_542_asUtf32)).ToResult_k<JSON_mErrors_Compile._IDeserializationError>(JSON_mErrors_Compile.DeserializationError.create_InvalidUnicode());
        if ((_543_valueOrError1).IsFailure()) {
          return (_543_valueOrError1).PropagateFailure<Dafny.ISequence<char>>();
        } else {
          Dafny.ISequence<ushort> _544_asUint16 = (_543_valueOrError1).Extract();
          Wrappers_Compile._IResult<Dafny.ISequence<ushort>, JSON_mErrors_Compile._IDeserializationError> _545_valueOrError2 = JSON_mDeserializer_Compile.__default.Unescape(_544_asUint16, BigInteger.Zero, Dafny.Sequence<ushort>.FromElements());
          if ((_545_valueOrError2).IsFailure()) {
            return (_545_valueOrError2).PropagateFailure<Dafny.ISequence<char>>();
          } else {
            Dafny.ISequence<ushort> _546_unescaped = (_545_valueOrError2).Extract();
            return (UnicodeStrings_Compile.__default.FromUTF16Checked(_546_unescaped)).ToResult_k<JSON_mErrors_Compile._IDeserializationError>(JSON_mErrors_Compile.DeserializationError.create_InvalidUnicode());
          }
        }
      }
    }
    public static Wrappers_Compile._IResult<BigInteger, JSON_mErrors_Compile._IDeserializationError> ToInt(JSON_mUtils_mViews_mCore_Compile._IView__ sign, JSON_mUtils_mViews_mCore_Compile._IView__ n)
    {
      BigInteger _547_n = JSON_mDeserializer_mByteStrConversion_Compile.__default.ToNat__any((n).Bytes(), new BigInteger(10), JSON_mDeserializer_Compile.__default.DIGITS);
      return Wrappers_Compile.Result<BigInteger, JSON_mErrors_Compile._IDeserializationError>.create_Success((((sign).Char_q('-')) ? ((BigInteger.Zero) - (_547_n)) : (_547_n)));
    }
    public static Wrappers_Compile._IResult<JSON_mValues_Compile._IDecimal, JSON_mErrors_Compile._IDeserializationError> Number(JSON_mGrammar_Compile._Ijnumber js) {
      JSON_mGrammar_Compile._Ijnumber _let_tmp_rhs1 = js;
      JSON_mUtils_mViews_mCore_Compile._IView__ _548_minus = _let_tmp_rhs1.dtor_minus;
      JSON_mUtils_mViews_mCore_Compile._IView__ _549_num = _let_tmp_rhs1.dtor_num;
      JSON_mGrammar_Compile._IMaybe<JSON_mGrammar_Compile._Ijfrac> _550_frac = _let_tmp_rhs1.dtor_frac;
      JSON_mGrammar_Compile._IMaybe<JSON_mGrammar_Compile._Ijexp> _551_exp = _let_tmp_rhs1.dtor_exp;
      Wrappers_Compile._IResult<BigInteger, JSON_mErrors_Compile._IDeserializationError> _552_valueOrError0 = JSON_mDeserializer_Compile.__default.ToInt(_548_minus, _549_num);
      if ((_552_valueOrError0).IsFailure()) {
        return (_552_valueOrError0).PropagateFailure<JSON_mValues_Compile._IDecimal>();
      } else {
        BigInteger _553_n = (_552_valueOrError0).Extract();
        Wrappers_Compile._IResult<BigInteger, JSON_mErrors_Compile._IDeserializationError> _554_valueOrError1 = ((System.Func<JSON_mGrammar_Compile._IMaybe<JSON_mGrammar_Compile._Ijexp>, Wrappers_Compile._IResult<BigInteger, JSON_mErrors_Compile._IDeserializationError>>)((_source13) => {
          if (_source13.is_Empty) {
            return Wrappers_Compile.Result<BigInteger, JSON_mErrors_Compile._IDeserializationError>.create_Success(BigInteger.Zero);
          } else {
            JSON_mGrammar_Compile._Ijexp _555___mcc_h0 = _source13.dtor_t;
            return ((System.Func<JSON_mGrammar_Compile._Ijexp, Wrappers_Compile._IResult<BigInteger, JSON_mErrors_Compile._IDeserializationError>>)((_source14) => {
              {
                JSON_mUtils_mViews_mCore_Compile._IView__ _556___mcc_h1 = _source14.dtor_e;
                JSON_mUtils_mViews_mCore_Compile._IView__ _557___mcc_h2 = _source14.dtor_sign;
                JSON_mUtils_mViews_mCore_Compile._IView__ _558___mcc_h3 = _source14.dtor_num;
                return Dafny.Helpers.Let<JSON_mUtils_mViews_mCore_Compile._IView__, Wrappers_Compile._IResult<BigInteger, JSON_mErrors_Compile._IDeserializationError>>(_558___mcc_h3, _pat_let6_0 => Dafny.Helpers.Let<JSON_mUtils_mViews_mCore_Compile._IView__, Wrappers_Compile._IResult<BigInteger, JSON_mErrors_Compile._IDeserializationError>>(_pat_let6_0, _559_num => Dafny.Helpers.Let<JSON_mUtils_mViews_mCore_Compile._IView__, Wrappers_Compile._IResult<BigInteger, JSON_mErrors_Compile._IDeserializationError>>(_557___mcc_h2, _pat_let7_0 => Dafny.Helpers.Let<JSON_mUtils_mViews_mCore_Compile._IView__, Wrappers_Compile._IResult<BigInteger, JSON_mErrors_Compile._IDeserializationError>>(_pat_let7_0, _560_sign => JSON_mDeserializer_Compile.__default.ToInt(_560_sign, _559_num)))));
              }
            }))(_555___mcc_h0);
          }
        }))(_551_exp);
        if ((_554_valueOrError1).IsFailure()) {
          return (_554_valueOrError1).PropagateFailure<JSON_mValues_Compile._IDecimal>();
        } else {
          BigInteger _561_e10 = (_554_valueOrError1).Extract();
          JSON_mGrammar_Compile._IMaybe<JSON_mGrammar_Compile._Ijfrac> _source15 = _550_frac;
          if (_source15.is_Empty) {
            return Wrappers_Compile.Result<JSON_mValues_Compile._IDecimal, JSON_mErrors_Compile._IDeserializationError>.create_Success(JSON_mValues_Compile.Decimal.create(_553_n, _561_e10));
          } else {
            JSON_mGrammar_Compile._Ijfrac _562___mcc_h4 = _source15.dtor_t;
            JSON_mGrammar_Compile._Ijfrac _source16 = _562___mcc_h4;
            {
              JSON_mUtils_mViews_mCore_Compile._IView__ _563___mcc_h5 = _source16.dtor_period;
              JSON_mUtils_mViews_mCore_Compile._IView__ _564___mcc_h6 = _source16.dtor_num;
              JSON_mUtils_mViews_mCore_Compile._IView__ _565_num = _564___mcc_h6;
              BigInteger _566_pow10 = new BigInteger((_565_num).Length());
              Wrappers_Compile._IResult<BigInteger, JSON_mErrors_Compile._IDeserializationError> _567_valueOrError2 = JSON_mDeserializer_Compile.__default.ToInt(_548_minus, _565_num);
              if ((_567_valueOrError2).IsFailure()) {
                return (_567_valueOrError2).PropagateFailure<JSON_mValues_Compile._IDecimal>();
              } else {
                BigInteger _568_frac = (_567_valueOrError2).Extract();
                return Wrappers_Compile.Result<JSON_mValues_Compile._IDecimal, JSON_mErrors_Compile._IDeserializationError>.create_Success(JSON_mValues_Compile.Decimal.create(((_553_n) * (Power_Compile.__default.Pow(new BigInteger(10), _566_pow10))) + (_568_frac), (_561_e10) - (_566_pow10)));
              }
            }
          }
        }
      }
    }
    public static Wrappers_Compile._IResult<_System._ITuple2<Dafny.ISequence<char>, JSON_mValues_Compile._IJSON>, JSON_mErrors_Compile._IDeserializationError> KeyValue(JSON_mGrammar_Compile._IjKeyValue js) {
      Wrappers_Compile._IResult<Dafny.ISequence<char>, JSON_mErrors_Compile._IDeserializationError> _569_valueOrError0 = JSON_mDeserializer_Compile.__default.String((js).dtor_k);
      if ((_569_valueOrError0).IsFailure()) {
        return (_569_valueOrError0).PropagateFailure<_System._ITuple2<Dafny.ISequence<char>, JSON_mValues_Compile._IJSON>>();
      } else {
        Dafny.ISequence<char> _570_k = (_569_valueOrError0).Extract();
        Wrappers_Compile._IResult<JSON_mValues_Compile._IJSON, JSON_mErrors_Compile._IDeserializationError> _571_valueOrError1 = JSON_mDeserializer_Compile.__default.Value((js).dtor_v);
        if ((_571_valueOrError1).IsFailure()) {
          return (_571_valueOrError1).PropagateFailure<_System._ITuple2<Dafny.ISequence<char>, JSON_mValues_Compile._IJSON>>();
        } else {
          JSON_mValues_Compile._IJSON _572_v = (_571_valueOrError1).Extract();
          return Wrappers_Compile.Result<_System._ITuple2<Dafny.ISequence<char>, JSON_mValues_Compile._IJSON>, JSON_mErrors_Compile._IDeserializationError>.create_Success(_System.Tuple2<Dafny.ISequence<char>, JSON_mValues_Compile._IJSON>.create(_570_k, _572_v));
        }
      }
    }
    public static Wrappers_Compile._IResult<Dafny.ISequence<_System._ITuple2<Dafny.ISequence<char>, JSON_mValues_Compile._IJSON>>, JSON_mErrors_Compile._IDeserializationError> Object(JSON_mGrammar_Compile._IBracketed<JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mGrammar_Compile._IjKeyValue, JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mUtils_mViews_mCore_Compile._IView__> js) {
      return Seq_Compile.__default.MapWithResult<JSON_mGrammar_Compile._ISuffixed<JSON_mGrammar_Compile._IjKeyValue, JSON_mUtils_mViews_mCore_Compile._IView__>, _System._ITuple2<Dafny.ISequence<char>, JSON_mValues_Compile._IJSON>, JSON_mErrors_Compile._IDeserializationError>(Dafny.Helpers.Id<Func<JSON_mGrammar_Compile._IBracketed<JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mGrammar_Compile._IjKeyValue, JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mUtils_mViews_mCore_Compile._IView__>, Func<JSON_mGrammar_Compile._ISuffixed<JSON_mGrammar_Compile._IjKeyValue, JSON_mUtils_mViews_mCore_Compile._IView__>, Wrappers_Compile._IResult<_System._ITuple2<Dafny.ISequence<char>, JSON_mValues_Compile._IJSON>, JSON_mErrors_Compile._IDeserializationError>>>>((_573_js) => ((System.Func<JSON_mGrammar_Compile._ISuffixed<JSON_mGrammar_Compile._IjKeyValue, JSON_mUtils_mViews_mCore_Compile._IView__>, Wrappers_Compile._IResult<_System._ITuple2<Dafny.ISequence<char>, JSON_mValues_Compile._IJSON>, JSON_mErrors_Compile._IDeserializationError>>)((_574_d) => {
        return JSON_mDeserializer_Compile.__default.KeyValue((_574_d).dtor_t);
      })))(js), (js).dtor_data);
    }
    public static Wrappers_Compile._IResult<Dafny.ISequence<JSON_mValues_Compile._IJSON>, JSON_mErrors_Compile._IDeserializationError> Array(JSON_mGrammar_Compile._IBracketed<JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mGrammar_Compile._IValue, JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mUtils_mViews_mCore_Compile._IView__> js) {
      return Seq_Compile.__default.MapWithResult<JSON_mGrammar_Compile._ISuffixed<JSON_mGrammar_Compile._IValue, JSON_mUtils_mViews_mCore_Compile._IView__>, JSON_mValues_Compile._IJSON, JSON_mErrors_Compile._IDeserializationError>(Dafny.Helpers.Id<Func<JSON_mGrammar_Compile._IBracketed<JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mGrammar_Compile._IValue, JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mUtils_mViews_mCore_Compile._IView__>, Func<JSON_mGrammar_Compile._ISuffixed<JSON_mGrammar_Compile._IValue, JSON_mUtils_mViews_mCore_Compile._IView__>, Wrappers_Compile._IResult<JSON_mValues_Compile._IJSON, JSON_mErrors_Compile._IDeserializationError>>>>((_575_js) => ((System.Func<JSON_mGrammar_Compile._ISuffixed<JSON_mGrammar_Compile._IValue, JSON_mUtils_mViews_mCore_Compile._IView__>, Wrappers_Compile._IResult<JSON_mValues_Compile._IJSON, JSON_mErrors_Compile._IDeserializationError>>)((_576_d) => {
        return JSON_mDeserializer_Compile.__default.Value((_576_d).dtor_t);
      })))(js), (js).dtor_data);
    }
    public static Wrappers_Compile._IResult<JSON_mValues_Compile._IJSON, JSON_mErrors_Compile._IDeserializationError> Value(JSON_mGrammar_Compile._IValue js) {
      JSON_mGrammar_Compile._IValue _source17 = js;
      if (_source17.is_Null) {
        JSON_mUtils_mViews_mCore_Compile._IView__ _577___mcc_h0 = _source17.dtor_n;
        return Wrappers_Compile.Result<JSON_mValues_Compile._IJSON, JSON_mErrors_Compile._IDeserializationError>.create_Success(JSON_mValues_Compile.JSON.create_Null());
      } else if (_source17.is_Bool) {
        JSON_mUtils_mViews_mCore_Compile._IView__ _578___mcc_h1 = _source17.dtor_b;
        JSON_mUtils_mViews_mCore_Compile._IView__ _579_b = _578___mcc_h1;
        return Wrappers_Compile.Result<JSON_mValues_Compile._IJSON, JSON_mErrors_Compile._IDeserializationError>.create_Success(JSON_mValues_Compile.JSON.create_Bool(JSON_mDeserializer_Compile.__default.Bool(_579_b)));
      } else if (_source17.is_String) {
        JSON_mGrammar_Compile._Ijstring _580___mcc_h2 = _source17.dtor_str;
        JSON_mGrammar_Compile._Ijstring _581_str = _580___mcc_h2;
        Wrappers_Compile._IResult<Dafny.ISequence<char>, JSON_mErrors_Compile._IDeserializationError> _582_valueOrError0 = JSON_mDeserializer_Compile.__default.String(_581_str);
        if ((_582_valueOrError0).IsFailure()) {
          return (_582_valueOrError0).PropagateFailure<JSON_mValues_Compile._IJSON>();
        } else {
          Dafny.ISequence<char> _583_s = (_582_valueOrError0).Extract();
          return Wrappers_Compile.Result<JSON_mValues_Compile._IJSON, JSON_mErrors_Compile._IDeserializationError>.create_Success(JSON_mValues_Compile.JSON.create_String(_583_s));
        }
      } else if (_source17.is_Number) {
        JSON_mGrammar_Compile._Ijnumber _584___mcc_h3 = _source17.dtor_num;
        JSON_mGrammar_Compile._Ijnumber _585_dec = _584___mcc_h3;
        Wrappers_Compile._IResult<JSON_mValues_Compile._IDecimal, JSON_mErrors_Compile._IDeserializationError> _586_valueOrError1 = JSON_mDeserializer_Compile.__default.Number(_585_dec);
        if ((_586_valueOrError1).IsFailure()) {
          return (_586_valueOrError1).PropagateFailure<JSON_mValues_Compile._IJSON>();
        } else {
          JSON_mValues_Compile._IDecimal _587_n = (_586_valueOrError1).Extract();
          return Wrappers_Compile.Result<JSON_mValues_Compile._IJSON, JSON_mErrors_Compile._IDeserializationError>.create_Success(JSON_mValues_Compile.JSON.create_Number(_587_n));
        }
      } else if (_source17.is_Object) {
        JSON_mGrammar_Compile._IBracketed<JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mGrammar_Compile._IjKeyValue, JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mUtils_mViews_mCore_Compile._IView__> _588___mcc_h4 = _source17.dtor_obj;
        JSON_mGrammar_Compile._IBracketed<JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mGrammar_Compile._IjKeyValue, JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mUtils_mViews_mCore_Compile._IView__> _589_obj = _588___mcc_h4;
        Wrappers_Compile._IResult<Dafny.ISequence<_System._ITuple2<Dafny.ISequence<char>, JSON_mValues_Compile._IJSON>>, JSON_mErrors_Compile._IDeserializationError> _590_valueOrError2 = JSON_mDeserializer_Compile.__default.Object(_589_obj);
        if ((_590_valueOrError2).IsFailure()) {
          return (_590_valueOrError2).PropagateFailure<JSON_mValues_Compile._IJSON>();
        } else {
          Dafny.ISequence<_System._ITuple2<Dafny.ISequence<char>, JSON_mValues_Compile._IJSON>> _591_o = (_590_valueOrError2).Extract();
          return Wrappers_Compile.Result<JSON_mValues_Compile._IJSON, JSON_mErrors_Compile._IDeserializationError>.create_Success(JSON_mValues_Compile.JSON.create_Object(_591_o));
        }
      } else {
        JSON_mGrammar_Compile._IBracketed<JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mGrammar_Compile._IValue, JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mUtils_mViews_mCore_Compile._IView__> _592___mcc_h5 = _source17.dtor_arr;
        JSON_mGrammar_Compile._IBracketed<JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mGrammar_Compile._IValue, JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mUtils_mViews_mCore_Compile._IView__> _593_arr = _592___mcc_h5;
        Wrappers_Compile._IResult<Dafny.ISequence<JSON_mValues_Compile._IJSON>, JSON_mErrors_Compile._IDeserializationError> _594_valueOrError3 = JSON_mDeserializer_Compile.__default.Array(_593_arr);
        if ((_594_valueOrError3).IsFailure()) {
          return (_594_valueOrError3).PropagateFailure<JSON_mValues_Compile._IJSON>();
        } else {
          Dafny.ISequence<JSON_mValues_Compile._IJSON> _595_a = (_594_valueOrError3).Extract();
          return Wrappers_Compile.Result<JSON_mValues_Compile._IJSON, JSON_mErrors_Compile._IDeserializationError>.create_Success(JSON_mValues_Compile.JSON.create_Array(_595_a));
        }
      }
    }
    public static Wrappers_Compile._IResult<JSON_mValues_Compile._IJSON, JSON_mErrors_Compile._IDeserializationError> JSON(JSON_mGrammar_Compile._IStructural<JSON_mGrammar_Compile._IValue> js) {
      return JSON_mDeserializer_Compile.__default.Value((js).dtor_t);
    }
    public static Dafny.IMap<ushort,BigInteger> HEX__TABLE__16 { get {
      return Dafny.Map<ushort, BigInteger>.FromElements(new Dafny.Pair<ushort, BigInteger>((ushort)('0'), BigInteger.Zero), new Dafny.Pair<ushort, BigInteger>((ushort)('1'), BigInteger.One), new Dafny.Pair<ushort, BigInteger>((ushort)('2'), new BigInteger(2)), new Dafny.Pair<ushort, BigInteger>((ushort)('3'), new BigInteger(3)), new Dafny.Pair<ushort, BigInteger>((ushort)('4'), new BigInteger(4)), new Dafny.Pair<ushort, BigInteger>((ushort)('5'), new BigInteger(5)), new Dafny.Pair<ushort, BigInteger>((ushort)('6'), new BigInteger(6)), new Dafny.Pair<ushort, BigInteger>((ushort)('7'), new BigInteger(7)), new Dafny.Pair<ushort, BigInteger>((ushort)('8'), new BigInteger(8)), new Dafny.Pair<ushort, BigInteger>((ushort)('9'), new BigInteger(9)), new Dafny.Pair<ushort, BigInteger>((ushort)('a'), new BigInteger(10)), new Dafny.Pair<ushort, BigInteger>((ushort)('b'), new BigInteger(11)), new Dafny.Pair<ushort, BigInteger>((ushort)('c'), new BigInteger(12)), new Dafny.Pair<ushort, BigInteger>((ushort)('d'), new BigInteger(13)), new Dafny.Pair<ushort, BigInteger>((ushort)('e'), new BigInteger(14)), new Dafny.Pair<ushort, BigInteger>((ushort)('f'), new BigInteger(15)), new Dafny.Pair<ushort, BigInteger>((ushort)('A'), new BigInteger(10)), new Dafny.Pair<ushort, BigInteger>((ushort)('B'), new BigInteger(11)), new Dafny.Pair<ushort, BigInteger>((ushort)('C'), new BigInteger(12)), new Dafny.Pair<ushort, BigInteger>((ushort)('D'), new BigInteger(13)), new Dafny.Pair<ushort, BigInteger>((ushort)('E'), new BigInteger(14)), new Dafny.Pair<ushort, BigInteger>((ushort)('F'), new BigInteger(15)));
    } }
    public static Dafny.IMap<byte,BigInteger> DIGITS { get {
      return Dafny.Map<byte, BigInteger>.FromElements(new Dafny.Pair<byte, BigInteger>((byte)('0'), BigInteger.Zero), new Dafny.Pair<byte, BigInteger>((byte)('1'), BigInteger.One), new Dafny.Pair<byte, BigInteger>((byte)('2'), new BigInteger(2)), new Dafny.Pair<byte, BigInteger>((byte)('3'), new BigInteger(3)), new Dafny.Pair<byte, BigInteger>((byte)('4'), new BigInteger(4)), new Dafny.Pair<byte, BigInteger>((byte)('5'), new BigInteger(5)), new Dafny.Pair<byte, BigInteger>((byte)('6'), new BigInteger(6)), new Dafny.Pair<byte, BigInteger>((byte)('7'), new BigInteger(7)), new Dafny.Pair<byte, BigInteger>((byte)('8'), new BigInteger(8)), new Dafny.Pair<byte, BigInteger>((byte)('9'), new BigInteger(9)));
    } }
    public static byte MINUS { get {
      return (byte)('-');
    } }
  }
} // end of namespace JSON_mDeserializer_Compile
namespace JSON_mConcreteSyntax_mSpec_Compile {

  public partial class __default {
    public static Dafny.ISequence<byte> View(JSON_mUtils_mViews_mCore_Compile._IView__ v) {
      return (v).Bytes();
    }
    public static Dafny.ISequence<byte> Structural<__T>(JSON_mGrammar_Compile._IStructural<__T> self, Func<__T, Dafny.ISequence<byte>> fT)
    {
      return Dafny.Sequence<byte>.Concat(Dafny.Sequence<byte>.Concat(JSON_mConcreteSyntax_mSpec_Compile.__default.View((self).dtor_before), Dafny.Helpers.Id<Func<__T, Dafny.ISequence<byte>>>(fT)((self).dtor_t)), JSON_mConcreteSyntax_mSpec_Compile.__default.View((self).dtor_after));
    }
    public static Dafny.ISequence<byte> StructuralView(JSON_mGrammar_Compile._IStructural<JSON_mUtils_mViews_mCore_Compile._IView__> self) {
      return JSON_mConcreteSyntax_mSpec_Compile.__default.Structural<JSON_mUtils_mViews_mCore_Compile._IView__>(self, JSON_mConcreteSyntax_mSpec_Compile.__default.View);
    }
    public static Dafny.ISequence<byte> Maybe<__T>(JSON_mGrammar_Compile._IMaybe<__T> self, Func<__T, Dafny.ISequence<byte>> fT)
    {
      if ((self).is_Empty) {
        return Dafny.Sequence<byte>.FromElements();
      } else {
        return Dafny.Helpers.Id<Func<__T, Dafny.ISequence<byte>>>(fT)((self).dtor_t);
      }
    }
    public static Dafny.ISequence<byte> ConcatBytes<__T>(Dafny.ISequence<__T> ts, Func<__T, Dafny.ISequence<byte>> fT)
    {
      Dafny.ISequence<byte> _596___accumulator = Dafny.Sequence<byte>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((ts).Count)).Sign == 0) {
        return Dafny.Sequence<byte>.Concat(_596___accumulator, Dafny.Sequence<byte>.FromElements());
      } else {
        _596___accumulator = Dafny.Sequence<byte>.Concat(_596___accumulator, Dafny.Helpers.Id<Func<__T, Dafny.ISequence<byte>>>(fT)((ts).Select(BigInteger.Zero)));
        Dafny.ISequence<__T> _in121 = (ts).Drop(BigInteger.One);
        Func<__T, Dafny.ISequence<byte>> _in122 = fT;
        ts = _in121;
        fT = _in122;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<byte> Bracketed<__D, __S>(JSON_mGrammar_Compile._IBracketed<JSON_mUtils_mViews_mCore_Compile._IView__, __D, __S, JSON_mUtils_mViews_mCore_Compile._IView__> self, Func<JSON_mGrammar_Compile._ISuffixed<__D, __S>, Dafny.ISequence<byte>> fDatum)
    {
      return Dafny.Sequence<byte>.Concat(Dafny.Sequence<byte>.Concat(JSON_mConcreteSyntax_mSpec_Compile.__default.StructuralView((self).dtor_l), JSON_mConcreteSyntax_mSpec_Compile.__default.ConcatBytes<JSON_mGrammar_Compile._ISuffixed<__D, __S>>((self).dtor_data, fDatum)), JSON_mConcreteSyntax_mSpec_Compile.__default.StructuralView((self).dtor_r));
    }
    public static Dafny.ISequence<byte> KeyValue(JSON_mGrammar_Compile._IjKeyValue self) {
      return Dafny.Sequence<byte>.Concat(Dafny.Sequence<byte>.Concat(JSON_mConcreteSyntax_mSpec_Compile.__default.String((self).dtor_k), JSON_mConcreteSyntax_mSpec_Compile.__default.StructuralView((self).dtor_colon)), JSON_mConcreteSyntax_mSpec_Compile.__default.Value((self).dtor_v));
    }
    public static Dafny.ISequence<byte> Frac(JSON_mGrammar_Compile._Ijfrac self) {
      return Dafny.Sequence<byte>.Concat(JSON_mConcreteSyntax_mSpec_Compile.__default.View((self).dtor_period), JSON_mConcreteSyntax_mSpec_Compile.__default.View((self).dtor_num));
    }
    public static Dafny.ISequence<byte> Exp(JSON_mGrammar_Compile._Ijexp self) {
      return Dafny.Sequence<byte>.Concat(Dafny.Sequence<byte>.Concat(JSON_mConcreteSyntax_mSpec_Compile.__default.View((self).dtor_e), JSON_mConcreteSyntax_mSpec_Compile.__default.View((self).dtor_sign)), JSON_mConcreteSyntax_mSpec_Compile.__default.View((self).dtor_num));
    }
    public static Dafny.ISequence<byte> Number(JSON_mGrammar_Compile._Ijnumber self) {
      return Dafny.Sequence<byte>.Concat(Dafny.Sequence<byte>.Concat(Dafny.Sequence<byte>.Concat(JSON_mConcreteSyntax_mSpec_Compile.__default.View((self).dtor_minus), JSON_mConcreteSyntax_mSpec_Compile.__default.View((self).dtor_num)), JSON_mConcreteSyntax_mSpec_Compile.__default.Maybe<JSON_mGrammar_Compile._Ijfrac>((self).dtor_frac, JSON_mConcreteSyntax_mSpec_Compile.__default.Frac)), JSON_mConcreteSyntax_mSpec_Compile.__default.Maybe<JSON_mGrammar_Compile._Ijexp>((self).dtor_exp, JSON_mConcreteSyntax_mSpec_Compile.__default.Exp));
    }
    public static Dafny.ISequence<byte> String(JSON_mGrammar_Compile._Ijstring self) {
      return Dafny.Sequence<byte>.Concat(Dafny.Sequence<byte>.Concat(JSON_mConcreteSyntax_mSpec_Compile.__default.View((self).dtor_lq), JSON_mConcreteSyntax_mSpec_Compile.__default.View((self).dtor_contents)), JSON_mConcreteSyntax_mSpec_Compile.__default.View((self).dtor_rq));
    }
    public static Dafny.ISequence<byte> CommaSuffix(JSON_mGrammar_Compile._IMaybe<JSON_mGrammar_Compile._IStructural<JSON_mUtils_mViews_mCore_Compile._IView__>> c) {
      return JSON_mConcreteSyntax_mSpec_Compile.__default.Maybe<JSON_mGrammar_Compile._IStructural<JSON_mUtils_mViews_mCore_Compile._IView__>>(c, JSON_mConcreteSyntax_mSpec_Compile.__default.StructuralView);
    }
    public static Dafny.ISequence<byte> Member(JSON_mGrammar_Compile._ISuffixed<JSON_mGrammar_Compile._IjKeyValue, JSON_mUtils_mViews_mCore_Compile._IView__> self) {
      return Dafny.Sequence<byte>.Concat(JSON_mConcreteSyntax_mSpec_Compile.__default.KeyValue((self).dtor_t), JSON_mConcreteSyntax_mSpec_Compile.__default.CommaSuffix((self).dtor_suffix));
    }
    public static Dafny.ISequence<byte> Item(JSON_mGrammar_Compile._ISuffixed<JSON_mGrammar_Compile._IValue, JSON_mUtils_mViews_mCore_Compile._IView__> self) {
      return Dafny.Sequence<byte>.Concat(JSON_mConcreteSyntax_mSpec_Compile.__default.Value((self).dtor_t), JSON_mConcreteSyntax_mSpec_Compile.__default.CommaSuffix((self).dtor_suffix));
    }
    public static Dafny.ISequence<byte> Object(JSON_mGrammar_Compile._IBracketed<JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mGrammar_Compile._IjKeyValue, JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mUtils_mViews_mCore_Compile._IView__> obj) {
      return JSON_mConcreteSyntax_mSpec_Compile.__default.Bracketed<JSON_mGrammar_Compile._IjKeyValue, JSON_mUtils_mViews_mCore_Compile._IView__>(obj, Dafny.Helpers.Id<Func<JSON_mGrammar_Compile._IBracketed<JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mGrammar_Compile._IjKeyValue, JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mUtils_mViews_mCore_Compile._IView__>, Func<JSON_mGrammar_Compile._ISuffixed<JSON_mGrammar_Compile._IjKeyValue, JSON_mUtils_mViews_mCore_Compile._IView__>, Dafny.ISequence<byte>>>>((_597_obj) => ((System.Func<JSON_mGrammar_Compile._ISuffixed<JSON_mGrammar_Compile._IjKeyValue, JSON_mUtils_mViews_mCore_Compile._IView__>, Dafny.ISequence<byte>>)((_598_d) => {
        return JSON_mConcreteSyntax_mSpec_Compile.__default.Member(_598_d);
      })))(obj));
    }
    public static Dafny.ISequence<byte> Array(JSON_mGrammar_Compile._IBracketed<JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mGrammar_Compile._IValue, JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mUtils_mViews_mCore_Compile._IView__> arr) {
      return JSON_mConcreteSyntax_mSpec_Compile.__default.Bracketed<JSON_mGrammar_Compile._IValue, JSON_mUtils_mViews_mCore_Compile._IView__>(arr, Dafny.Helpers.Id<Func<JSON_mGrammar_Compile._IBracketed<JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mGrammar_Compile._IValue, JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mUtils_mViews_mCore_Compile._IView__>, Func<JSON_mGrammar_Compile._ISuffixed<JSON_mGrammar_Compile._IValue, JSON_mUtils_mViews_mCore_Compile._IView__>, Dafny.ISequence<byte>>>>((_599_arr) => ((System.Func<JSON_mGrammar_Compile._ISuffixed<JSON_mGrammar_Compile._IValue, JSON_mUtils_mViews_mCore_Compile._IView__>, Dafny.ISequence<byte>>)((_600_d) => {
        return JSON_mConcreteSyntax_mSpec_Compile.__default.Item(_600_d);
      })))(arr));
    }
    public static Dafny.ISequence<byte> Value(JSON_mGrammar_Compile._IValue self) {
      JSON_mGrammar_Compile._IValue _source18 = self;
      if (_source18.is_Null) {
        JSON_mUtils_mViews_mCore_Compile._IView__ _601___mcc_h0 = _source18.dtor_n;
        JSON_mUtils_mViews_mCore_Compile._IView__ _602_n = _601___mcc_h0;
        return JSON_mConcreteSyntax_mSpec_Compile.__default.View(_602_n);
      } else if (_source18.is_Bool) {
        JSON_mUtils_mViews_mCore_Compile._IView__ _603___mcc_h1 = _source18.dtor_b;
        JSON_mUtils_mViews_mCore_Compile._IView__ _604_b = _603___mcc_h1;
        return JSON_mConcreteSyntax_mSpec_Compile.__default.View(_604_b);
      } else if (_source18.is_String) {
        JSON_mGrammar_Compile._Ijstring _605___mcc_h2 = _source18.dtor_str;
        JSON_mGrammar_Compile._Ijstring _606_str = _605___mcc_h2;
        return JSON_mConcreteSyntax_mSpec_Compile.__default.String(_606_str);
      } else if (_source18.is_Number) {
        JSON_mGrammar_Compile._Ijnumber _607___mcc_h3 = _source18.dtor_num;
        JSON_mGrammar_Compile._Ijnumber _608_num = _607___mcc_h3;
        return JSON_mConcreteSyntax_mSpec_Compile.__default.Number(_608_num);
      } else if (_source18.is_Object) {
        JSON_mGrammar_Compile._IBracketed<JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mGrammar_Compile._IjKeyValue, JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mUtils_mViews_mCore_Compile._IView__> _609___mcc_h4 = _source18.dtor_obj;
        JSON_mGrammar_Compile._IBracketed<JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mGrammar_Compile._IjKeyValue, JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mUtils_mViews_mCore_Compile._IView__> _610_obj = _609___mcc_h4;
        return JSON_mConcreteSyntax_mSpec_Compile.__default.Object(_610_obj);
      } else {
        JSON_mGrammar_Compile._IBracketed<JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mGrammar_Compile._IValue, JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mUtils_mViews_mCore_Compile._IView__> _611___mcc_h5 = _source18.dtor_arr;
        JSON_mGrammar_Compile._IBracketed<JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mGrammar_Compile._IValue, JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mUtils_mViews_mCore_Compile._IView__> _612_arr = _611___mcc_h5;
        return JSON_mConcreteSyntax_mSpec_Compile.__default.Array(_612_arr);
      }
    }
    public static Dafny.ISequence<byte> JSON(JSON_mGrammar_Compile._IStructural<JSON_mGrammar_Compile._IValue> js) {
      return JSON_mConcreteSyntax_mSpec_Compile.__default.Structural<JSON_mGrammar_Compile._IValue>(js, JSON_mConcreteSyntax_mSpec_Compile.__default.Value);
    }
  }
} // end of namespace JSON_mConcreteSyntax_mSpec_Compile
namespace JSON_mConcreteSyntax_mSpecProperties_Compile {

} // end of namespace JSON_mConcreteSyntax_mSpecProperties_Compile
namespace JSON_mConcreteSyntax_Compile {

} // end of namespace JSON_mConcreteSyntax_Compile
namespace JSON_mZeroCopy_mSerializer_Compile {

  public partial class __default {
    public static Wrappers_Compile._IResult<byte[], JSON_mErrors_Compile._ISerializationError> Serialize(JSON_mGrammar_Compile._IStructural<JSON_mGrammar_Compile._IValue> js)
    {
      Wrappers_Compile._IResult<byte[], JSON_mErrors_Compile._ISerializationError> rbs = Wrappers_Compile.Result<byte[], JSON_mErrors_Compile._ISerializationError>.Default(new byte[0]);
      JSON_mUtils_mViews_mWriters_Compile._IWriter__ _613_writer;
      _613_writer = JSON_mZeroCopy_mSerializer_Compile.__default.Text(js);
      Wrappers_Compile._IOutcome<JSON_mErrors_Compile._ISerializationError> _614_valueOrError0 = Wrappers_Compile.Outcome<JSON_mErrors_Compile._ISerializationError>.Default();
      _614_valueOrError0 = Wrappers_Compile.__default.Need<JSON_mErrors_Compile._ISerializationError>((_613_writer).Unsaturated_q, JSON_mErrors_Compile.SerializationError.create_OutOfMemory());
      if ((_614_valueOrError0).IsFailure()) {
        rbs = (_614_valueOrError0).PropagateFailure<byte[]>();
        return rbs;
      }
      byte[] _615_bs;
      byte[] _out24;
      _out24 = (_613_writer).ToArray();
      _615_bs = _out24;
      rbs = Wrappers_Compile.Result<byte[], JSON_mErrors_Compile._ISerializationError>.create_Success(_615_bs);
      return rbs;
      return rbs;
    }
    public static Wrappers_Compile._IResult<uint, JSON_mErrors_Compile._ISerializationError> SerializeTo(JSON_mGrammar_Compile._IStructural<JSON_mGrammar_Compile._IValue> js, byte[] dest)
    {
      Wrappers_Compile._IResult<uint, JSON_mErrors_Compile._ISerializationError> len = Wrappers_Compile.Result<uint, JSON_mErrors_Compile._ISerializationError>.Default(0);
      JSON_mUtils_mViews_mWriters_Compile._IWriter__ _616_writer;
      _616_writer = JSON_mZeroCopy_mSerializer_Compile.__default.Text(js);
      Wrappers_Compile._IOutcome<JSON_mErrors_Compile._ISerializationError> _617_valueOrError0 = Wrappers_Compile.Outcome<JSON_mErrors_Compile._ISerializationError>.Default();
      _617_valueOrError0 = Wrappers_Compile.__default.Need<JSON_mErrors_Compile._ISerializationError>((_616_writer).Unsaturated_q, JSON_mErrors_Compile.SerializationError.create_OutOfMemory());
      if ((_617_valueOrError0).IsFailure()) {
        len = (_617_valueOrError0).PropagateFailure<uint>();
        return len;
      }
      Wrappers_Compile._IOutcome<JSON_mErrors_Compile._ISerializationError> _618_valueOrError1 = Wrappers_Compile.Outcome<JSON_mErrors_Compile._ISerializationError>.Default();
      _618_valueOrError1 = Wrappers_Compile.__default.Need<JSON_mErrors_Compile._ISerializationError>((new BigInteger((_616_writer).dtor_length)) <= (new BigInteger((dest).Length)), JSON_mErrors_Compile.SerializationError.create_OutOfMemory());
      if ((_618_valueOrError1).IsFailure()) {
        len = (_618_valueOrError1).PropagateFailure<uint>();
        return len;
      }
      (_616_writer).CopyTo(dest);
      len = Wrappers_Compile.Result<uint, JSON_mErrors_Compile._ISerializationError>.create_Success((_616_writer).dtor_length);
      return len;
      return len;
    }
    public static JSON_mUtils_mViews_mWriters_Compile._IWriter__ Text(JSON_mGrammar_Compile._IStructural<JSON_mGrammar_Compile._IValue> js) {
      return JSON_mZeroCopy_mSerializer_Compile.__default.JSON(js, JSON_mUtils_mViews_mWriters_Compile.Writer__.Empty);
    }
    public static JSON_mUtils_mViews_mWriters_Compile._IWriter__ JSON(JSON_mGrammar_Compile._IStructural<JSON_mGrammar_Compile._IValue> js, JSON_mUtils_mViews_mWriters_Compile._IWriter__ writer)
    {
      return (((writer).Append((js).dtor_before)).Then(Dafny.Helpers.Id<Func<JSON_mGrammar_Compile._IStructural<JSON_mGrammar_Compile._IValue>, Func<JSON_mUtils_mViews_mWriters_Compile._IWriter__, JSON_mUtils_mViews_mWriters_Compile._IWriter__>>>((_619_js) => ((System.Func<JSON_mUtils_mViews_mWriters_Compile._IWriter__, JSON_mUtils_mViews_mWriters_Compile._IWriter__>)((_620_wr) => {
        return JSON_mZeroCopy_mSerializer_Compile.__default.Value((_619_js).dtor_t, _620_wr);
      })))(js))).Append((js).dtor_after);
    }
    public static JSON_mUtils_mViews_mWriters_Compile._IWriter__ Value(JSON_mGrammar_Compile._IValue v, JSON_mUtils_mViews_mWriters_Compile._IWriter__ writer)
    {
      JSON_mGrammar_Compile._IValue _source19 = v;
      if (_source19.is_Null) {
        JSON_mUtils_mViews_mCore_Compile._IView__ _621___mcc_h0 = _source19.dtor_n;
        JSON_mUtils_mViews_mCore_Compile._IView__ _622_n = _621___mcc_h0;
        return (writer).Append(_622_n);
      } else if (_source19.is_Bool) {
        JSON_mUtils_mViews_mCore_Compile._IView__ _623___mcc_h1 = _source19.dtor_b;
        JSON_mUtils_mViews_mCore_Compile._IView__ _624_b = _623___mcc_h1;
        JSON_mUtils_mViews_mWriters_Compile._IWriter__ _625_wr = (writer).Append(_624_b);
        return _625_wr;
      } else if (_source19.is_String) {
        JSON_mGrammar_Compile._Ijstring _626___mcc_h2 = _source19.dtor_str;
        JSON_mGrammar_Compile._Ijstring _627_str = _626___mcc_h2;
        JSON_mUtils_mViews_mWriters_Compile._IWriter__ _628_wr = JSON_mZeroCopy_mSerializer_Compile.__default.String(_627_str, writer);
        return _628_wr;
      } else if (_source19.is_Number) {
        JSON_mGrammar_Compile._Ijnumber _629___mcc_h3 = _source19.dtor_num;
        JSON_mGrammar_Compile._Ijnumber _630_num = _629___mcc_h3;
        JSON_mUtils_mViews_mWriters_Compile._IWriter__ _631_wr = JSON_mZeroCopy_mSerializer_Compile.__default.Number(_630_num, writer);
        return _631_wr;
      } else if (_source19.is_Object) {
        JSON_mGrammar_Compile._IBracketed<JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mGrammar_Compile._IjKeyValue, JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mUtils_mViews_mCore_Compile._IView__> _632___mcc_h4 = _source19.dtor_obj;
        JSON_mGrammar_Compile._IBracketed<JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mGrammar_Compile._IjKeyValue, JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mUtils_mViews_mCore_Compile._IView__> _633_obj = _632___mcc_h4;
        JSON_mUtils_mViews_mWriters_Compile._IWriter__ _634_wr = JSON_mZeroCopy_mSerializer_Compile.__default.Object(_633_obj, writer);
        return _634_wr;
      } else {
        JSON_mGrammar_Compile._IBracketed<JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mGrammar_Compile._IValue, JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mUtils_mViews_mCore_Compile._IView__> _635___mcc_h5 = _source19.dtor_arr;
        JSON_mGrammar_Compile._IBracketed<JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mGrammar_Compile._IValue, JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mUtils_mViews_mCore_Compile._IView__> _636_arr = _635___mcc_h5;
        JSON_mUtils_mViews_mWriters_Compile._IWriter__ _637_wr = JSON_mZeroCopy_mSerializer_Compile.__default.Array(_636_arr, writer);
        return _637_wr;
      }
    }
    public static JSON_mUtils_mViews_mWriters_Compile._IWriter__ String(JSON_mGrammar_Compile._Ijstring str, JSON_mUtils_mViews_mWriters_Compile._IWriter__ writer)
    {
      return (((writer).Append((str).dtor_lq)).Append((str).dtor_contents)).Append((str).dtor_rq);
    }
    public static JSON_mUtils_mViews_mWriters_Compile._IWriter__ Number(JSON_mGrammar_Compile._Ijnumber num, JSON_mUtils_mViews_mWriters_Compile._IWriter__ writer)
    {
      JSON_mUtils_mViews_mWriters_Compile._IWriter__ _638_wr = ((writer).Append((num).dtor_minus)).Append((num).dtor_num);
      JSON_mUtils_mViews_mWriters_Compile._IWriter__ _639_wr = ((((num).dtor_frac).is_NonEmpty) ? (((_638_wr).Append((((num).dtor_frac).dtor_t).dtor_period)).Append((((num).dtor_frac).dtor_t).dtor_num)) : (_638_wr));
      JSON_mUtils_mViews_mWriters_Compile._IWriter__ _640_wr = ((((num).dtor_exp).is_NonEmpty) ? ((((_639_wr).Append((((num).dtor_exp).dtor_t).dtor_e)).Append((((num).dtor_exp).dtor_t).dtor_sign)).Append((((num).dtor_exp).dtor_t).dtor_num)) : (_639_wr));
      return _640_wr;
    }
    public static JSON_mUtils_mViews_mWriters_Compile._IWriter__ StructuralView(JSON_mGrammar_Compile._IStructural<JSON_mUtils_mViews_mCore_Compile._IView__> st, JSON_mUtils_mViews_mWriters_Compile._IWriter__ writer)
    {
      return (((writer).Append((st).dtor_before)).Append((st).dtor_t)).Append((st).dtor_after);
    }
    public static JSON_mUtils_mViews_mWriters_Compile._IWriter__ Object(JSON_mGrammar_Compile._IBracketed<JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mGrammar_Compile._IjKeyValue, JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mUtils_mViews_mCore_Compile._IView__> obj, JSON_mUtils_mViews_mWriters_Compile._IWriter__ writer)
    {
      JSON_mUtils_mViews_mWriters_Compile._IWriter__ _641_wr = JSON_mZeroCopy_mSerializer_Compile.__default.StructuralView((obj).dtor_l, writer);
      JSON_mUtils_mViews_mWriters_Compile._IWriter__ _642_wr = JSON_mZeroCopy_mSerializer_Compile.__default.Members(obj, _641_wr);
      JSON_mUtils_mViews_mWriters_Compile._IWriter__ _643_wr = JSON_mZeroCopy_mSerializer_Compile.__default.StructuralView((obj).dtor_r, _642_wr);
      return _643_wr;
    }
    public static JSON_mUtils_mViews_mWriters_Compile._IWriter__ Array(JSON_mGrammar_Compile._IBracketed<JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mGrammar_Compile._IValue, JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mUtils_mViews_mCore_Compile._IView__> arr, JSON_mUtils_mViews_mWriters_Compile._IWriter__ writer)
    {
      JSON_mUtils_mViews_mWriters_Compile._IWriter__ _644_wr = JSON_mZeroCopy_mSerializer_Compile.__default.StructuralView((arr).dtor_l, writer);
      JSON_mUtils_mViews_mWriters_Compile._IWriter__ _645_wr = JSON_mZeroCopy_mSerializer_Compile.__default.Items(arr, _644_wr);
      JSON_mUtils_mViews_mWriters_Compile._IWriter__ _646_wr = JSON_mZeroCopy_mSerializer_Compile.__default.StructuralView((arr).dtor_r, _645_wr);
      return _646_wr;
    }
    public static JSON_mUtils_mViews_mWriters_Compile._IWriter__ Members(JSON_mGrammar_Compile._IBracketed<JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mGrammar_Compile._IjKeyValue, JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mUtils_mViews_mCore_Compile._IView__> obj, JSON_mUtils_mViews_mWriters_Compile._IWriter__ writer)
    {
      JSON_mUtils_mViews_mWriters_Compile._IWriter__ wr = JSON_mUtils_mViews_mWriters_Compile.Writer.Default();
      JSON_mUtils_mViews_mWriters_Compile._IWriter__ _out25;
      _out25 = JSON_mZeroCopy_mSerializer_Compile.__default.MembersImpl(obj, writer);
      wr = _out25;
      return wr;
    }
    public static JSON_mUtils_mViews_mWriters_Compile._IWriter__ Items(JSON_mGrammar_Compile._IBracketed<JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mGrammar_Compile._IValue, JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mUtils_mViews_mCore_Compile._IView__> arr, JSON_mUtils_mViews_mWriters_Compile._IWriter__ writer)
    {
      JSON_mUtils_mViews_mWriters_Compile._IWriter__ wr = JSON_mUtils_mViews_mWriters_Compile.Writer.Default();
      JSON_mUtils_mViews_mWriters_Compile._IWriter__ _out26;
      _out26 = JSON_mZeroCopy_mSerializer_Compile.__default.ItemsImpl(arr, writer);
      wr = _out26;
      return wr;
    }
    public static JSON_mUtils_mViews_mWriters_Compile._IWriter__ MembersImpl(JSON_mGrammar_Compile._IBracketed<JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mGrammar_Compile._IjKeyValue, JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mUtils_mViews_mCore_Compile._IView__> obj, JSON_mUtils_mViews_mWriters_Compile._IWriter__ writer)
    {
      JSON_mUtils_mViews_mWriters_Compile._IWriter__ wr = JSON_mUtils_mViews_mWriters_Compile.Writer.Default();
      wr = writer;
      Dafny.ISequence<JSON_mGrammar_Compile._ISuffixed<JSON_mGrammar_Compile._IjKeyValue, JSON_mUtils_mViews_mCore_Compile._IView__>> _647_members;
      _647_members = (obj).dtor_data;
      BigInteger _hi9 = new BigInteger((_647_members).Count);
      for (BigInteger _648_i = BigInteger.Zero; _648_i < _hi9; _648_i++) {
        wr = JSON_mZeroCopy_mSerializer_Compile.__default.Member((_647_members).Select(_648_i), wr);
      }
      return wr;
    }
    public static JSON_mUtils_mViews_mWriters_Compile._IWriter__ ItemsImpl(JSON_mGrammar_Compile._IBracketed<JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mGrammar_Compile._IValue, JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mUtils_mViews_mCore_Compile._IView__> arr, JSON_mUtils_mViews_mWriters_Compile._IWriter__ writer)
    {
      JSON_mUtils_mViews_mWriters_Compile._IWriter__ wr = JSON_mUtils_mViews_mWriters_Compile.Writer.Default();
      wr = writer;
      Dafny.ISequence<JSON_mGrammar_Compile._ISuffixed<JSON_mGrammar_Compile._IValue, JSON_mUtils_mViews_mCore_Compile._IView__>> _649_items;
      _649_items = (arr).dtor_data;
      BigInteger _hi10 = new BigInteger((_649_items).Count);
      for (BigInteger _650_i = BigInteger.Zero; _650_i < _hi10; _650_i++) {
        wr = JSON_mZeroCopy_mSerializer_Compile.__default.Item((_649_items).Select(_650_i), wr);
      }
      return wr;
    }
    public static JSON_mUtils_mViews_mWriters_Compile._IWriter__ Member(JSON_mGrammar_Compile._ISuffixed<JSON_mGrammar_Compile._IjKeyValue, JSON_mUtils_mViews_mCore_Compile._IView__> m, JSON_mUtils_mViews_mWriters_Compile._IWriter__ writer)
    {
      JSON_mUtils_mViews_mWriters_Compile._IWriter__ _651_wr = JSON_mZeroCopy_mSerializer_Compile.__default.String(((m).dtor_t).dtor_k, writer);
      JSON_mUtils_mViews_mWriters_Compile._IWriter__ _652_wr = JSON_mZeroCopy_mSerializer_Compile.__default.StructuralView(((m).dtor_t).dtor_colon, _651_wr);
      JSON_mUtils_mViews_mWriters_Compile._IWriter__ _653_wr = JSON_mZeroCopy_mSerializer_Compile.__default.Value(((m).dtor_t).dtor_v, _652_wr);
      JSON_mUtils_mViews_mWriters_Compile._IWriter__ _654_wr = ((((m).dtor_suffix).is_Empty) ? (_653_wr) : (JSON_mZeroCopy_mSerializer_Compile.__default.StructuralView(((m).dtor_suffix).dtor_t, _653_wr)));
      return _654_wr;
    }
    public static JSON_mUtils_mViews_mWriters_Compile._IWriter__ Item(JSON_mGrammar_Compile._ISuffixed<JSON_mGrammar_Compile._IValue, JSON_mUtils_mViews_mCore_Compile._IView__> m, JSON_mUtils_mViews_mWriters_Compile._IWriter__ writer)
    {
      JSON_mUtils_mViews_mWriters_Compile._IWriter__ _655_wr = JSON_mZeroCopy_mSerializer_Compile.__default.Value((m).dtor_t, writer);
      JSON_mUtils_mViews_mWriters_Compile._IWriter__ _656_wr = ((((m).dtor_suffix).is_Empty) ? (_655_wr) : (JSON_mZeroCopy_mSerializer_Compile.__default.StructuralView(((m).dtor_suffix).dtor_t, _655_wr)));
      return _656_wr;
    }
  }
} // end of namespace JSON_mZeroCopy_mSerializer_Compile
namespace JSON_mZeroCopy_mDeserializer_mCore_Compile {

  public partial class jopt {
    private static readonly JSON_mUtils_mViews_mCore_Compile._IView__ Witness = JSON_mUtils_mViews_mCore_Compile.View__.OfBytes(Dafny.Sequence<byte>.FromElements());
    public static JSON_mUtils_mViews_mCore_Compile._IView__ Default() {
      return Witness;
    }
    private static readonly Dafny.TypeDescriptor<JSON_mUtils_mViews_mCore_Compile._IView__> _TYPE = new Dafny.TypeDescriptor<JSON_mUtils_mViews_mCore_Compile._IView__>(JSON_mZeroCopy_mDeserializer_mCore_Compile.jopt.Default());
    public static Dafny.TypeDescriptor<JSON_mUtils_mViews_mCore_Compile._IView__> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class ValueParser {
    private static readonly Dafny.TypeDescriptor<JSON_mUtils_mParsers_Compile._ISubParser__<JSON_mGrammar_Compile._IValue, JSON_mErrors_Compile._IDeserializationError>> _TYPE = new Dafny.TypeDescriptor<JSON_mUtils_mParsers_Compile._ISubParser__<JSON_mGrammar_Compile._IValue, JSON_mErrors_Compile._IDeserializationError>>(JSON_mUtils_mParsers_Compile.SubParser<JSON_mGrammar_Compile._IValue, JSON_mErrors_Compile._IDeserializationError>.Default());
    public static Dafny.TypeDescriptor<JSON_mUtils_mParsers_Compile._ISubParser__<JSON_mGrammar_Compile._IValue, JSON_mErrors_Compile._IDeserializationError>> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class __default {
    public static Wrappers_Compile._IResult<JSON_mUtils_mCursors_Compile._ISplit<JSON_mUtils_mViews_mCore_Compile._IView__>, JSON_mUtils_mCursors_Compile._ICursorError<JSON_mErrors_Compile._IDeserializationError>> Get(JSON_mUtils_mCursors_Compile._ICursor__ cs, JSON_mErrors_Compile._IDeserializationError err)
    {
      Wrappers_Compile._IResult<JSON_mUtils_mCursors_Compile._ICursor__, JSON_mUtils_mCursors_Compile._ICursorError<JSON_mErrors_Compile._IDeserializationError>> _657_valueOrError0 = (cs).Get<JSON_mErrors_Compile._IDeserializationError>(err);
      if ((_657_valueOrError0).IsFailure()) {
        return (_657_valueOrError0).PropagateFailure<JSON_mUtils_mCursors_Compile._ISplit<JSON_mUtils_mViews_mCore_Compile._IView__>>();
      } else {
        JSON_mUtils_mCursors_Compile._ICursor__ _658_cs = (_657_valueOrError0).Extract();
        return Wrappers_Compile.Result<JSON_mUtils_mCursors_Compile._ISplit<JSON_mUtils_mViews_mCore_Compile._IView__>, JSON_mUtils_mCursors_Compile._ICursorError<JSON_mErrors_Compile._IDeserializationError>>.create_Success((_658_cs).Split());
      }
    }
    public static JSON_mUtils_mCursors_Compile._ISplit<JSON_mUtils_mViews_mCore_Compile._IView__> WS(JSON_mUtils_mCursors_Compile._ICursor__ cs)
    {
      JSON_mUtils_mCursors_Compile._ISplit<JSON_mUtils_mViews_mCore_Compile._IView__> sp = JSON_mUtils_mCursors_Compile.Split<JSON_mUtils_mViews_mCore_Compile._IView__>.Default(JSON_mGrammar_Compile.jblanks.Default());
      uint _659_point_k;
      _659_point_k = (cs).dtor_point;
      uint _660_end;
      _660_end = (cs).dtor_end;
      while (((_659_point_k) < (_660_end)) && (JSON_mGrammar_Compile.__default.Blank_q(((cs).dtor_s).Select(_659_point_k)))) {
        _659_point_k = (_659_point_k) + (1U);
      }
      sp = (JSON_mUtils_mCursors_Compile.Cursor__.create((cs).dtor_s, (cs).dtor_beg, _659_point_k, (cs).dtor_end)).Split();
      return sp;
      return sp;
    }
    public static Wrappers_Compile._IResult<JSON_mUtils_mCursors_Compile._ISplit<JSON_mGrammar_Compile._IStructural<__T>>, JSON_mUtils_mCursors_Compile._ICursorError<JSON_mErrors_Compile._IDeserializationError>> Structural<__T>(JSON_mUtils_mCursors_Compile._ICursor__ cs, JSON_mUtils_mParsers_Compile._IParser__<__T, JSON_mErrors_Compile._IDeserializationError> parser)
    {
      JSON_mUtils_mCursors_Compile._ISplit<JSON_mUtils_mViews_mCore_Compile._IView__> _let_tmp_rhs2 = JSON_mZeroCopy_mDeserializer_mCore_Compile.__default.WS(cs);
      JSON_mUtils_mViews_mCore_Compile._IView__ _661_before = _let_tmp_rhs2.dtor_t;
      JSON_mUtils_mCursors_Compile._ICursor__ _662_cs = _let_tmp_rhs2.dtor_cs;
      Wrappers_Compile._IResult<JSON_mUtils_mCursors_Compile._ISplit<__T>, JSON_mUtils_mCursors_Compile._ICursorError<JSON_mErrors_Compile._IDeserializationError>> _663_valueOrError0 = Dafny.Helpers.Id<Func<JSON_mUtils_mCursors_Compile._ICursor__, Wrappers_Compile._IResult<JSON_mUtils_mCursors_Compile._ISplit<__T>, JSON_mUtils_mCursors_Compile._ICursorError<JSON_mErrors_Compile._IDeserializationError>>>>((parser).dtor_fn)(_662_cs);
      if ((_663_valueOrError0).IsFailure()) {
        return (_663_valueOrError0).PropagateFailure<JSON_mUtils_mCursors_Compile._ISplit<JSON_mGrammar_Compile._IStructural<__T>>>();
      } else {
        JSON_mUtils_mCursors_Compile._ISplit<__T> _let_tmp_rhs3 = (_663_valueOrError0).Extract();
        __T _664_val = _let_tmp_rhs3.dtor_t;
        JSON_mUtils_mCursors_Compile._ICursor__ _665_cs = _let_tmp_rhs3.dtor_cs;
        JSON_mUtils_mCursors_Compile._ISplit<JSON_mUtils_mViews_mCore_Compile._IView__> _let_tmp_rhs4 = JSON_mZeroCopy_mDeserializer_mCore_Compile.__default.WS(_665_cs);
        JSON_mUtils_mViews_mCore_Compile._IView__ _666_after = _let_tmp_rhs4.dtor_t;
        JSON_mUtils_mCursors_Compile._ICursor__ _667_cs = _let_tmp_rhs4.dtor_cs;
        return Wrappers_Compile.Result<JSON_mUtils_mCursors_Compile._ISplit<JSON_mGrammar_Compile._IStructural<__T>>, JSON_mUtils_mCursors_Compile._ICursorError<JSON_mErrors_Compile._IDeserializationError>>.create_Success(JSON_mUtils_mCursors_Compile.Split<JSON_mGrammar_Compile._IStructural<__T>>.create(JSON_mGrammar_Compile.Structural<__T>.create(_661_before, _664_val, _666_after), _667_cs));
      }
    }
    public static JSON_mUtils_mCursors_Compile._ISplit<JSON_mGrammar_Compile._IStructural<JSON_mUtils_mViews_mCore_Compile._IView__>> TryStructural(JSON_mUtils_mCursors_Compile._ICursor__ cs) {
      JSON_mUtils_mCursors_Compile._ISplit<JSON_mUtils_mViews_mCore_Compile._IView__> _let_tmp_rhs5 = JSON_mZeroCopy_mDeserializer_mCore_Compile.__default.WS(cs);
      JSON_mUtils_mViews_mCore_Compile._IView__ _668_before = _let_tmp_rhs5.dtor_t;
      JSON_mUtils_mCursors_Compile._ICursor__ _669_cs = _let_tmp_rhs5.dtor_cs;
      JSON_mUtils_mCursors_Compile._ISplit<JSON_mUtils_mViews_mCore_Compile._IView__> _let_tmp_rhs6 = ((_669_cs).SkipByte()).Split();
      JSON_mUtils_mViews_mCore_Compile._IView__ _670_val = _let_tmp_rhs6.dtor_t;
      JSON_mUtils_mCursors_Compile._ICursor__ _671_cs = _let_tmp_rhs6.dtor_cs;
      JSON_mUtils_mCursors_Compile._ISplit<JSON_mUtils_mViews_mCore_Compile._IView__> _let_tmp_rhs7 = JSON_mZeroCopy_mDeserializer_mCore_Compile.__default.WS(_671_cs);
      JSON_mUtils_mViews_mCore_Compile._IView__ _672_after = _let_tmp_rhs7.dtor_t;
      JSON_mUtils_mCursors_Compile._ICursor__ _673_cs = _let_tmp_rhs7.dtor_cs;
      return JSON_mUtils_mCursors_Compile.Split<JSON_mGrammar_Compile._IStructural<JSON_mUtils_mViews_mCore_Compile._IView__>>.create(JSON_mGrammar_Compile.Structural<JSON_mUtils_mViews_mCore_Compile._IView__>.create(_668_before, _670_val, _672_after), _673_cs);
    }
    public static Func<JSON_mUtils_mViews_mCore_Compile._IView__, Dafny.ISequence<byte>> SpecView { get {
      return ((System.Func<JSON_mUtils_mViews_mCore_Compile._IView__, Dafny.ISequence<byte>>)((_674_v) => {
        return JSON_mConcreteSyntax_mSpec_Compile.__default.View(_674_v);
      }));
    } }
  }
} // end of namespace JSON_mZeroCopy_mDeserializer_mCore_Compile
namespace JSON_mZeroCopy_mDeserializer_mStrings_Compile {

  public partial class __default {
    public static Wrappers_Compile._IResult<JSON_mUtils_mCursors_Compile._ICursor__, JSON_mUtils_mCursors_Compile._ICursorError<JSON_mErrors_Compile._IDeserializationError>> StringBody(JSON_mUtils_mCursors_Compile._ICursor__ cs)
    {
      Wrappers_Compile._IResult<JSON_mUtils_mCursors_Compile._ICursor__, JSON_mUtils_mCursors_Compile._ICursorError<JSON_mErrors_Compile._IDeserializationError>> pr = Wrappers_Compile.Result<JSON_mUtils_mCursors_Compile._ICursor__, JSON_mUtils_mCursors_Compile._ICursorError<JSON_mErrors_Compile._IDeserializationError>>.Default(JSON_mUtils_mCursors_Compile.Cursor.Default());
      bool _675_escaped;
      _675_escaped = false;
      uint _hi11 = (cs).dtor_end;
      for (uint _676_point_k = (cs).dtor_point; _676_point_k < _hi11; _676_point_k++) {
        byte _677_byte;
        _677_byte = ((cs).dtor_s).Select(_676_point_k);
        if (((_677_byte) == ((byte)('\"'))) && (!(_675_escaped))) {
          pr = Wrappers_Compile.Result<JSON_mUtils_mCursors_Compile._ICursor__, JSON_mUtils_mCursors_Compile._ICursorError<JSON_mErrors_Compile._IDeserializationError>>.create_Success(JSON_mUtils_mCursors_Compile.Cursor__.create((cs).dtor_s, (cs).dtor_beg, _676_point_k, (cs).dtor_end));
          return pr;
        } else if ((_677_byte) == ((byte)('\\'))) {
          _675_escaped = !(_675_escaped);
        } else {
          _675_escaped = false;
        }
      }
      pr = Wrappers_Compile.Result<JSON_mUtils_mCursors_Compile._ICursor__, JSON_mUtils_mCursors_Compile._ICursorError<JSON_mErrors_Compile._IDeserializationError>>.create_Failure(JSON_mUtils_mCursors_Compile.CursorError<JSON_mErrors_Compile._IDeserializationError>.create_EOF());
      return pr;
      return pr;
    }
    public static Wrappers_Compile._IResult<JSON_mUtils_mCursors_Compile._ISplit<JSON_mUtils_mViews_mCore_Compile._IView__>, JSON_mUtils_mCursors_Compile._ICursorError<JSON_mErrors_Compile._IDeserializationError>> Quote(JSON_mUtils_mCursors_Compile._ICursor__ cs) {
      Wrappers_Compile._IResult<JSON_mUtils_mCursors_Compile._ICursor__, JSON_mUtils_mCursors_Compile._ICursorError<JSON_mErrors_Compile._IDeserializationError>> _678_valueOrError0 = (cs).AssertChar<JSON_mErrors_Compile._IDeserializationError>('\"');
      if ((_678_valueOrError0).IsFailure()) {
        return (_678_valueOrError0).PropagateFailure<JSON_mUtils_mCursors_Compile._ISplit<JSON_mUtils_mViews_mCore_Compile._IView__>>();
      } else {
        JSON_mUtils_mCursors_Compile._ICursor__ _679_cs = (_678_valueOrError0).Extract();
        return Wrappers_Compile.Result<JSON_mUtils_mCursors_Compile._ISplit<JSON_mUtils_mViews_mCore_Compile._IView__>, JSON_mUtils_mCursors_Compile._ICursorError<JSON_mErrors_Compile._IDeserializationError>>.create_Success((_679_cs).Split());
      }
    }
    public static Wrappers_Compile._IResult<JSON_mUtils_mCursors_Compile._ISplit<JSON_mGrammar_Compile._Ijstring>, JSON_mUtils_mCursors_Compile._ICursorError<JSON_mErrors_Compile._IDeserializationError>> String(JSON_mUtils_mCursors_Compile._ICursor__ cs) {
      Wrappers_Compile._IResult<JSON_mUtils_mCursors_Compile._ISplit<JSON_mUtils_mViews_mCore_Compile._IView__>, JSON_mUtils_mCursors_Compile._ICursorError<JSON_mErrors_Compile._IDeserializationError>> _680_valueOrError0 = JSON_mZeroCopy_mDeserializer_mStrings_Compile.__default.Quote(cs);
      if ((_680_valueOrError0).IsFailure()) {
        return (_680_valueOrError0).PropagateFailure<JSON_mUtils_mCursors_Compile._ISplit<JSON_mGrammar_Compile._Ijstring>>();
      } else {
        JSON_mUtils_mCursors_Compile._ISplit<JSON_mUtils_mViews_mCore_Compile._IView__> _let_tmp_rhs8 = (_680_valueOrError0).Extract();
        JSON_mUtils_mViews_mCore_Compile._IView__ _681_lq = _let_tmp_rhs8.dtor_t;
        JSON_mUtils_mCursors_Compile._ICursor__ _682_cs = _let_tmp_rhs8.dtor_cs;
        Wrappers_Compile._IResult<JSON_mUtils_mCursors_Compile._ICursor__, JSON_mUtils_mCursors_Compile._ICursorError<JSON_mErrors_Compile._IDeserializationError>> _683_valueOrError1 = JSON_mZeroCopy_mDeserializer_mStrings_Compile.__default.StringBody(_682_cs);
        if ((_683_valueOrError1).IsFailure()) {
          return (_683_valueOrError1).PropagateFailure<JSON_mUtils_mCursors_Compile._ISplit<JSON_mGrammar_Compile._Ijstring>>();
        } else {
          JSON_mUtils_mCursors_Compile._ICursor__ _684_contents = (_683_valueOrError1).Extract();
          JSON_mUtils_mCursors_Compile._ISplit<JSON_mUtils_mViews_mCore_Compile._IView__> _let_tmp_rhs9 = (_684_contents).Split();
          JSON_mUtils_mViews_mCore_Compile._IView__ _685_contents = _let_tmp_rhs9.dtor_t;
          JSON_mUtils_mCursors_Compile._ICursor__ _686_cs = _let_tmp_rhs9.dtor_cs;
          Wrappers_Compile._IResult<JSON_mUtils_mCursors_Compile._ISplit<JSON_mUtils_mViews_mCore_Compile._IView__>, JSON_mUtils_mCursors_Compile._ICursorError<JSON_mErrors_Compile._IDeserializationError>> _687_valueOrError2 = JSON_mZeroCopy_mDeserializer_mStrings_Compile.__default.Quote(_686_cs);
          if ((_687_valueOrError2).IsFailure()) {
            return (_687_valueOrError2).PropagateFailure<JSON_mUtils_mCursors_Compile._ISplit<JSON_mGrammar_Compile._Ijstring>>();
          } else {
            JSON_mUtils_mCursors_Compile._ISplit<JSON_mUtils_mViews_mCore_Compile._IView__> _let_tmp_rhs10 = (_687_valueOrError2).Extract();
            JSON_mUtils_mViews_mCore_Compile._IView__ _688_rq = _let_tmp_rhs10.dtor_t;
            JSON_mUtils_mCursors_Compile._ICursor__ _689_cs = _let_tmp_rhs10.dtor_cs;
            return Wrappers_Compile.Result<JSON_mUtils_mCursors_Compile._ISplit<JSON_mGrammar_Compile._Ijstring>, JSON_mUtils_mCursors_Compile._ICursorError<JSON_mErrors_Compile._IDeserializationError>>.create_Success(JSON_mUtils_mCursors_Compile.Split<JSON_mGrammar_Compile._Ijstring>.create(JSON_mGrammar_Compile.jstring.create(_681_lq, _685_contents, _688_rq), _689_cs));
          }
        }
      }
    }
  }
} // end of namespace JSON_mZeroCopy_mDeserializer_mStrings_Compile
namespace JSON_mZeroCopy_mDeserializer_mNumbers_Compile {

  public partial class __default {
    public static JSON_mUtils_mCursors_Compile._ISplit<JSON_mUtils_mViews_mCore_Compile._IView__> Digits(JSON_mUtils_mCursors_Compile._ICursor__ cs) {
      return ((cs).SkipWhile(JSON_mGrammar_Compile.__default.Digit_q)).Split();
    }
    public static Wrappers_Compile._IResult<JSON_mUtils_mCursors_Compile._ISplit<JSON_mUtils_mViews_mCore_Compile._IView__>, JSON_mUtils_mCursors_Compile._ICursorError<JSON_mErrors_Compile._IDeserializationError>> NonEmptyDigits(JSON_mUtils_mCursors_Compile._ICursor__ cs) {
      JSON_mUtils_mCursors_Compile._ISplit<JSON_mUtils_mViews_mCore_Compile._IView__> _690_sp = JSON_mZeroCopy_mDeserializer_mNumbers_Compile.__default.Digits(cs);
      Wrappers_Compile._IOutcome<JSON_mUtils_mCursors_Compile._ICursorError<JSON_mErrors_Compile._IDeserializationError>> _691_valueOrError0 = Wrappers_Compile.__default.Need<JSON_mUtils_mCursors_Compile._ICursorError<JSON_mErrors_Compile._IDeserializationError>>(!(((_690_sp).dtor_t).Empty_q), JSON_mUtils_mCursors_Compile.CursorError<JSON_mErrors_Compile._IDeserializationError>.create_OtherError(JSON_mErrors_Compile.DeserializationError.create_EmptyNumber()));
      if ((_691_valueOrError0).IsFailure()) {
        return (_691_valueOrError0).PropagateFailure<JSON_mUtils_mCursors_Compile._ISplit<JSON_mUtils_mViews_mCore_Compile._IView__>>();
      } else {
        return Wrappers_Compile.Result<JSON_mUtils_mCursors_Compile._ISplit<JSON_mUtils_mViews_mCore_Compile._IView__>, JSON_mUtils_mCursors_Compile._ICursorError<JSON_mErrors_Compile._IDeserializationError>>.create_Success(_690_sp);
      }
    }
    public static Wrappers_Compile._IResult<JSON_mUtils_mCursors_Compile._ISplit<JSON_mUtils_mViews_mCore_Compile._IView__>, JSON_mUtils_mCursors_Compile._ICursorError<JSON_mErrors_Compile._IDeserializationError>> NonZeroInt(JSON_mUtils_mCursors_Compile._ICursor__ cs) {
      return JSON_mZeroCopy_mDeserializer_mNumbers_Compile.__default.NonEmptyDigits(cs);
    }
    public static JSON_mUtils_mCursors_Compile._ISplit<JSON_mUtils_mViews_mCore_Compile._IView__> OptionalMinus(JSON_mUtils_mCursors_Compile._ICursor__ cs) {
      return ((cs).SkipIf(((System.Func<byte, bool>)((_692_c) => {
        return (_692_c) == ((byte)('-'));
      })))).Split();
    }
    public static JSON_mUtils_mCursors_Compile._ISplit<JSON_mUtils_mViews_mCore_Compile._IView__> OptionalSign(JSON_mUtils_mCursors_Compile._ICursor__ cs) {
      return ((cs).SkipIf(((System.Func<byte, bool>)((_693_c) => {
        return ((_693_c) == ((byte)('-'))) || ((_693_c) == ((byte)('+')));
      })))).Split();
    }
    public static Wrappers_Compile._IResult<JSON_mUtils_mCursors_Compile._ISplit<JSON_mUtils_mViews_mCore_Compile._IView__>, JSON_mUtils_mCursors_Compile._ICursorError<JSON_mErrors_Compile._IDeserializationError>> TrimmedInt(JSON_mUtils_mCursors_Compile._ICursor__ cs) {
      JSON_mUtils_mCursors_Compile._ISplit<JSON_mUtils_mViews_mCore_Compile._IView__> _694_sp = ((cs).SkipIf(((System.Func<byte, bool>)((_695_c) => {
        return (_695_c) == ((byte)('0'));
      })))).Split();
      if (((_694_sp).dtor_t).Empty_q) {
        return JSON_mZeroCopy_mDeserializer_mNumbers_Compile.__default.NonZeroInt((_694_sp).dtor_cs);
      } else {
        return Wrappers_Compile.Result<JSON_mUtils_mCursors_Compile._ISplit<JSON_mUtils_mViews_mCore_Compile._IView__>, JSON_mUtils_mCursors_Compile._ICursorError<JSON_mErrors_Compile._IDeserializationError>>.create_Success(_694_sp);
      }
    }
    public static Wrappers_Compile._IResult<JSON_mUtils_mCursors_Compile._ISplit<JSON_mGrammar_Compile._IMaybe<JSON_mGrammar_Compile._Ijexp>>, JSON_mUtils_mCursors_Compile._ICursorError<JSON_mErrors_Compile._IDeserializationError>> Exp(JSON_mUtils_mCursors_Compile._ICursor__ cs) {
      JSON_mUtils_mCursors_Compile._ISplit<JSON_mUtils_mViews_mCore_Compile._IView__> _let_tmp_rhs11 = ((cs).SkipIf(((System.Func<byte, bool>)((_696_c) => {
        return ((_696_c) == ((byte)('e'))) || ((_696_c) == ((byte)('E')));
      })))).Split();
      JSON_mUtils_mViews_mCore_Compile._IView__ _697_e = _let_tmp_rhs11.dtor_t;
      JSON_mUtils_mCursors_Compile._ICursor__ _698_cs = _let_tmp_rhs11.dtor_cs;
      if ((_697_e).Empty_q) {
        return Wrappers_Compile.Result<JSON_mUtils_mCursors_Compile._ISplit<JSON_mGrammar_Compile._IMaybe<JSON_mGrammar_Compile._Ijexp>>, JSON_mUtils_mCursors_Compile._ICursorError<JSON_mErrors_Compile._IDeserializationError>>.create_Success(JSON_mUtils_mCursors_Compile.Split<JSON_mGrammar_Compile._IMaybe<JSON_mGrammar_Compile._Ijexp>>.create(JSON_mGrammar_Compile.Maybe<JSON_mGrammar_Compile._Ijexp>.create_Empty(), _698_cs));
      } else {
        JSON_mUtils_mCursors_Compile._ISplit<JSON_mUtils_mViews_mCore_Compile._IView__> _let_tmp_rhs12 = JSON_mZeroCopy_mDeserializer_mNumbers_Compile.__default.OptionalSign(_698_cs);
        JSON_mUtils_mViews_mCore_Compile._IView__ _699_sign = _let_tmp_rhs12.dtor_t;
        JSON_mUtils_mCursors_Compile._ICursor__ _700_cs = _let_tmp_rhs12.dtor_cs;
        Wrappers_Compile._IResult<JSON_mUtils_mCursors_Compile._ISplit<JSON_mUtils_mViews_mCore_Compile._IView__>, JSON_mUtils_mCursors_Compile._ICursorError<JSON_mErrors_Compile._IDeserializationError>> _701_valueOrError0 = JSON_mZeroCopy_mDeserializer_mNumbers_Compile.__default.NonEmptyDigits(_700_cs);
        if ((_701_valueOrError0).IsFailure()) {
          return (_701_valueOrError0).PropagateFailure<JSON_mUtils_mCursors_Compile._ISplit<JSON_mGrammar_Compile._IMaybe<JSON_mGrammar_Compile._Ijexp>>>();
        } else {
          JSON_mUtils_mCursors_Compile._ISplit<JSON_mUtils_mViews_mCore_Compile._IView__> _let_tmp_rhs13 = (_701_valueOrError0).Extract();
          JSON_mUtils_mViews_mCore_Compile._IView__ _702_num = _let_tmp_rhs13.dtor_t;
          JSON_mUtils_mCursors_Compile._ICursor__ _703_cs = _let_tmp_rhs13.dtor_cs;
          return Wrappers_Compile.Result<JSON_mUtils_mCursors_Compile._ISplit<JSON_mGrammar_Compile._IMaybe<JSON_mGrammar_Compile._Ijexp>>, JSON_mUtils_mCursors_Compile._ICursorError<JSON_mErrors_Compile._IDeserializationError>>.create_Success(JSON_mUtils_mCursors_Compile.Split<JSON_mGrammar_Compile._IMaybe<JSON_mGrammar_Compile._Ijexp>>.create(JSON_mGrammar_Compile.Maybe<JSON_mGrammar_Compile._Ijexp>.create_NonEmpty(JSON_mGrammar_Compile.jexp.create(_697_e, _699_sign, _702_num)), _703_cs));
        }
      }
    }
    public static Wrappers_Compile._IResult<JSON_mUtils_mCursors_Compile._ISplit<JSON_mGrammar_Compile._IMaybe<JSON_mGrammar_Compile._Ijfrac>>, JSON_mUtils_mCursors_Compile._ICursorError<JSON_mErrors_Compile._IDeserializationError>> Frac(JSON_mUtils_mCursors_Compile._ICursor__ cs) {
      JSON_mUtils_mCursors_Compile._ISplit<JSON_mUtils_mViews_mCore_Compile._IView__> _let_tmp_rhs14 = ((cs).SkipIf(((System.Func<byte, bool>)((_704_c) => {
        return (_704_c) == ((byte)('.'));
      })))).Split();
      JSON_mUtils_mViews_mCore_Compile._IView__ _705_period = _let_tmp_rhs14.dtor_t;
      JSON_mUtils_mCursors_Compile._ICursor__ _706_cs = _let_tmp_rhs14.dtor_cs;
      if ((_705_period).Empty_q) {
        return Wrappers_Compile.Result<JSON_mUtils_mCursors_Compile._ISplit<JSON_mGrammar_Compile._IMaybe<JSON_mGrammar_Compile._Ijfrac>>, JSON_mUtils_mCursors_Compile._ICursorError<JSON_mErrors_Compile._IDeserializationError>>.create_Success(JSON_mUtils_mCursors_Compile.Split<JSON_mGrammar_Compile._IMaybe<JSON_mGrammar_Compile._Ijfrac>>.create(JSON_mGrammar_Compile.Maybe<JSON_mGrammar_Compile._Ijfrac>.create_Empty(), _706_cs));
      } else {
        Wrappers_Compile._IResult<JSON_mUtils_mCursors_Compile._ISplit<JSON_mUtils_mViews_mCore_Compile._IView__>, JSON_mUtils_mCursors_Compile._ICursorError<JSON_mErrors_Compile._IDeserializationError>> _707_valueOrError0 = JSON_mZeroCopy_mDeserializer_mNumbers_Compile.__default.NonEmptyDigits(_706_cs);
        if ((_707_valueOrError0).IsFailure()) {
          return (_707_valueOrError0).PropagateFailure<JSON_mUtils_mCursors_Compile._ISplit<JSON_mGrammar_Compile._IMaybe<JSON_mGrammar_Compile._Ijfrac>>>();
        } else {
          JSON_mUtils_mCursors_Compile._ISplit<JSON_mUtils_mViews_mCore_Compile._IView__> _let_tmp_rhs15 = (_707_valueOrError0).Extract();
          JSON_mUtils_mViews_mCore_Compile._IView__ _708_num = _let_tmp_rhs15.dtor_t;
          JSON_mUtils_mCursors_Compile._ICursor__ _709_cs = _let_tmp_rhs15.dtor_cs;
          return Wrappers_Compile.Result<JSON_mUtils_mCursors_Compile._ISplit<JSON_mGrammar_Compile._IMaybe<JSON_mGrammar_Compile._Ijfrac>>, JSON_mUtils_mCursors_Compile._ICursorError<JSON_mErrors_Compile._IDeserializationError>>.create_Success(JSON_mUtils_mCursors_Compile.Split<JSON_mGrammar_Compile._IMaybe<JSON_mGrammar_Compile._Ijfrac>>.create(JSON_mGrammar_Compile.Maybe<JSON_mGrammar_Compile._Ijfrac>.create_NonEmpty(JSON_mGrammar_Compile.jfrac.create(_705_period, _708_num)), _709_cs));
        }
      }
    }
    public static JSON_mUtils_mCursors_Compile._ISplit<JSON_mGrammar_Compile._Ijnumber> NumberFromParts(JSON_mUtils_mCursors_Compile._ISplit<JSON_mUtils_mViews_mCore_Compile._IView__> minus, JSON_mUtils_mCursors_Compile._ISplit<JSON_mUtils_mViews_mCore_Compile._IView__> num, JSON_mUtils_mCursors_Compile._ISplit<JSON_mGrammar_Compile._IMaybe<JSON_mGrammar_Compile._Ijfrac>> frac, JSON_mUtils_mCursors_Compile._ISplit<JSON_mGrammar_Compile._IMaybe<JSON_mGrammar_Compile._Ijexp>> exp)
    {
      JSON_mUtils_mCursors_Compile._ISplit<JSON_mGrammar_Compile._Ijnumber> _710_sp = JSON_mUtils_mCursors_Compile.Split<JSON_mGrammar_Compile._Ijnumber>.create(JSON_mGrammar_Compile.jnumber.create((minus).dtor_t, (num).dtor_t, (frac).dtor_t, (exp).dtor_t), (exp).dtor_cs);
      return _710_sp;
    }
    public static Wrappers_Compile._IResult<JSON_mUtils_mCursors_Compile._ISplit<JSON_mGrammar_Compile._Ijnumber>, JSON_mUtils_mCursors_Compile._ICursorError<JSON_mErrors_Compile._IDeserializationError>> Number(JSON_mUtils_mCursors_Compile._ICursor__ cs) {
      JSON_mUtils_mCursors_Compile._ISplit<JSON_mUtils_mViews_mCore_Compile._IView__> _711_minus = JSON_mZeroCopy_mDeserializer_mNumbers_Compile.__default.OptionalMinus(cs);
      Wrappers_Compile._IResult<JSON_mUtils_mCursors_Compile._ISplit<JSON_mUtils_mViews_mCore_Compile._IView__>, JSON_mUtils_mCursors_Compile._ICursorError<JSON_mErrors_Compile._IDeserializationError>> _712_valueOrError0 = JSON_mZeroCopy_mDeserializer_mNumbers_Compile.__default.TrimmedInt((_711_minus).dtor_cs);
      if ((_712_valueOrError0).IsFailure()) {
        return (_712_valueOrError0).PropagateFailure<JSON_mUtils_mCursors_Compile._ISplit<JSON_mGrammar_Compile._Ijnumber>>();
      } else {
        JSON_mUtils_mCursors_Compile._ISplit<JSON_mUtils_mViews_mCore_Compile._IView__> _713_num = (_712_valueOrError0).Extract();
        Wrappers_Compile._IResult<JSON_mUtils_mCursors_Compile._ISplit<JSON_mGrammar_Compile._IMaybe<JSON_mGrammar_Compile._Ijfrac>>, JSON_mUtils_mCursors_Compile._ICursorError<JSON_mErrors_Compile._IDeserializationError>> _714_valueOrError1 = JSON_mZeroCopy_mDeserializer_mNumbers_Compile.__default.Frac((_713_num).dtor_cs);
        if ((_714_valueOrError1).IsFailure()) {
          return (_714_valueOrError1).PropagateFailure<JSON_mUtils_mCursors_Compile._ISplit<JSON_mGrammar_Compile._Ijnumber>>();
        } else {
          JSON_mUtils_mCursors_Compile._ISplit<JSON_mGrammar_Compile._IMaybe<JSON_mGrammar_Compile._Ijfrac>> _715_frac = (_714_valueOrError1).Extract();
          Wrappers_Compile._IResult<JSON_mUtils_mCursors_Compile._ISplit<JSON_mGrammar_Compile._IMaybe<JSON_mGrammar_Compile._Ijexp>>, JSON_mUtils_mCursors_Compile._ICursorError<JSON_mErrors_Compile._IDeserializationError>> _716_valueOrError2 = JSON_mZeroCopy_mDeserializer_mNumbers_Compile.__default.Exp((_715_frac).dtor_cs);
          if ((_716_valueOrError2).IsFailure()) {
            return (_716_valueOrError2).PropagateFailure<JSON_mUtils_mCursors_Compile._ISplit<JSON_mGrammar_Compile._Ijnumber>>();
          } else {
            JSON_mUtils_mCursors_Compile._ISplit<JSON_mGrammar_Compile._IMaybe<JSON_mGrammar_Compile._Ijexp>> _717_exp = (_716_valueOrError2).Extract();
            return Wrappers_Compile.Result<JSON_mUtils_mCursors_Compile._ISplit<JSON_mGrammar_Compile._Ijnumber>, JSON_mUtils_mCursors_Compile._ICursorError<JSON_mErrors_Compile._IDeserializationError>>.create_Success(JSON_mZeroCopy_mDeserializer_mNumbers_Compile.__default.NumberFromParts(_711_minus, _713_num, _715_frac, _717_exp));
          }
        }
      }
    }
  }
} // end of namespace JSON_mZeroCopy_mDeserializer_mNumbers_Compile
namespace JSON_mZeroCopy_mDeserializer_mObjectParams_Compile {

  public partial class __default {
    public static Wrappers_Compile._IResult<JSON_mUtils_mCursors_Compile._ISplit<JSON_mUtils_mViews_mCore_Compile._IView__>, JSON_mUtils_mCursors_Compile._ICursorError<JSON_mErrors_Compile._IDeserializationError>> Colon(JSON_mUtils_mCursors_Compile._ICursor__ cs) {
      Wrappers_Compile._IResult<JSON_mUtils_mCursors_Compile._ICursor__, JSON_mUtils_mCursors_Compile._ICursorError<JSON_mErrors_Compile._IDeserializationError>> _718_valueOrError0 = (cs).AssertChar<JSON_mErrors_Compile._IDeserializationError>(':');
      if ((_718_valueOrError0).IsFailure()) {
        return (_718_valueOrError0).PropagateFailure<JSON_mUtils_mCursors_Compile._ISplit<JSON_mUtils_mViews_mCore_Compile._IView__>>();
      } else {
        JSON_mUtils_mCursors_Compile._ICursor__ _719_cs = (_718_valueOrError0).Extract();
        return Wrappers_Compile.Result<JSON_mUtils_mCursors_Compile._ISplit<JSON_mUtils_mViews_mCore_Compile._IView__>, JSON_mUtils_mCursors_Compile._ICursorError<JSON_mErrors_Compile._IDeserializationError>>.create_Success((_719_cs).Split());
      }
    }
    public static JSON_mUtils_mCursors_Compile._ISplit<JSON_mGrammar_Compile._IjKeyValue> KeyValueFromParts(JSON_mUtils_mCursors_Compile._ISplit<JSON_mGrammar_Compile._Ijstring> k, JSON_mUtils_mCursors_Compile._ISplit<JSON_mGrammar_Compile._IStructural<JSON_mUtils_mViews_mCore_Compile._IView__>> colon, JSON_mUtils_mCursors_Compile._ISplit<JSON_mGrammar_Compile._IValue> v)
    {
      JSON_mUtils_mCursors_Compile._ISplit<JSON_mGrammar_Compile._IjKeyValue> _720_sp = JSON_mUtils_mCursors_Compile.Split<JSON_mGrammar_Compile._IjKeyValue>.create(JSON_mGrammar_Compile.jKeyValue.create((k).dtor_t, (colon).dtor_t, (v).dtor_t), (v).dtor_cs);
      return _720_sp;
    }
    public static Dafny.ISequence<byte> ElementSpec(JSON_mGrammar_Compile._IjKeyValue t) {
      return JSON_mConcreteSyntax_mSpec_Compile.__default.KeyValue(t);
    }
    public static Wrappers_Compile._IResult<JSON_mUtils_mCursors_Compile._ISplit<JSON_mGrammar_Compile._IjKeyValue>, JSON_mUtils_mCursors_Compile._ICursorError<JSON_mErrors_Compile._IDeserializationError>> Element(JSON_mUtils_mCursors_Compile._ICursor__ cs, JSON_mUtils_mParsers_Compile._ISubParser__<JSON_mGrammar_Compile._IValue, JSON_mErrors_Compile._IDeserializationError> json)
    {
      Wrappers_Compile._IResult<JSON_mUtils_mCursors_Compile._ISplit<JSON_mGrammar_Compile._Ijstring>, JSON_mUtils_mCursors_Compile._ICursorError<JSON_mErrors_Compile._IDeserializationError>> _721_valueOrError0 = JSON_mZeroCopy_mDeserializer_mStrings_Compile.__default.String(cs);
      if ((_721_valueOrError0).IsFailure()) {
        return (_721_valueOrError0).PropagateFailure<JSON_mUtils_mCursors_Compile._ISplit<JSON_mGrammar_Compile._IjKeyValue>>();
      } else {
        JSON_mUtils_mCursors_Compile._ISplit<JSON_mGrammar_Compile._Ijstring> _722_k = (_721_valueOrError0).Extract();
        JSON_mUtils_mParsers_Compile._IParser__<JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mErrors_Compile._IDeserializationError> _723_p = JSON_mUtils_mParsers_Compile.Parser__<JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mErrors_Compile._IDeserializationError>.create(JSON_mZeroCopy_mDeserializer_mObjectParams_Compile.__default.Colon);
        Wrappers_Compile._IResult<JSON_mUtils_mCursors_Compile._ISplit<JSON_mGrammar_Compile._IStructural<JSON_mUtils_mViews_mCore_Compile._IView__>>, JSON_mUtils_mCursors_Compile._ICursorError<JSON_mErrors_Compile._IDeserializationError>> _724_valueOrError1 = JSON_mZeroCopy_mDeserializer_mCore_Compile.__default.Structural<JSON_mUtils_mViews_mCore_Compile._IView__>((_722_k).dtor_cs, _723_p);
        if ((_724_valueOrError1).IsFailure()) {
          return (_724_valueOrError1).PropagateFailure<JSON_mUtils_mCursors_Compile._ISplit<JSON_mGrammar_Compile._IjKeyValue>>();
        } else {
          JSON_mUtils_mCursors_Compile._ISplit<JSON_mGrammar_Compile._IStructural<JSON_mUtils_mViews_mCore_Compile._IView__>> _725_colon = (_724_valueOrError1).Extract();
          Wrappers_Compile._IResult<JSON_mUtils_mCursors_Compile._ISplit<JSON_mGrammar_Compile._IValue>, JSON_mUtils_mCursors_Compile._ICursorError<JSON_mErrors_Compile._IDeserializationError>> _726_valueOrError2 = Dafny.Helpers.Id<Func<JSON_mUtils_mCursors_Compile._ICursor__, Wrappers_Compile._IResult<JSON_mUtils_mCursors_Compile._ISplit<JSON_mGrammar_Compile._IValue>, JSON_mUtils_mCursors_Compile._ICursorError<JSON_mErrors_Compile._IDeserializationError>>>>((json).dtor_fn)((_725_colon).dtor_cs);
          if ((_726_valueOrError2).IsFailure()) {
            return (_726_valueOrError2).PropagateFailure<JSON_mUtils_mCursors_Compile._ISplit<JSON_mGrammar_Compile._IjKeyValue>>();
          } else {
            JSON_mUtils_mCursors_Compile._ISplit<JSON_mGrammar_Compile._IValue> _727_v = (_726_valueOrError2).Extract();
            JSON_mUtils_mCursors_Compile._ISplit<JSON_mGrammar_Compile._IjKeyValue> _728_kv = JSON_mZeroCopy_mDeserializer_mObjectParams_Compile.__default.KeyValueFromParts(_722_k, _725_colon, _727_v);
            return Wrappers_Compile.Result<JSON_mUtils_mCursors_Compile._ISplit<JSON_mGrammar_Compile._IjKeyValue>, JSON_mUtils_mCursors_Compile._ICursorError<JSON_mErrors_Compile._IDeserializationError>>.create_Success(_728_kv);
          }
        }
      }
    }
    public static byte OPEN { get {
      return (byte)('{');
    } }
    public static byte CLOSE { get {
      return (byte)('}');
    } }
  }
} // end of namespace JSON_mZeroCopy_mDeserializer_mObjectParams_Compile
namespace JSON_mZeroCopy_mDeserializer_mObjects_Compile {

  public partial class __default {
    public static Wrappers_Compile._IResult<JSON_mUtils_mCursors_Compile._ISplit<JSON_mGrammar_Compile._IBracketed<JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mGrammar_Compile._IjKeyValue, JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mUtils_mViews_mCore_Compile._IView__>>, JSON_mUtils_mCursors_Compile._ICursorError<JSON_mErrors_Compile._IDeserializationError>> Object(JSON_mUtils_mCursors_Compile._ICursor__ cs, JSON_mUtils_mParsers_Compile._ISubParser__<JSON_mGrammar_Compile._IValue, JSON_mErrors_Compile._IDeserializationError> json)
    {
      Wrappers_Compile._IResult<JSON_mUtils_mCursors_Compile._ISplit<JSON_mGrammar_Compile._IBracketed<JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mGrammar_Compile._IjKeyValue, JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mUtils_mViews_mCore_Compile._IView__>>, JSON_mUtils_mCursors_Compile._ICursorError<JSON_mErrors_Compile._IDeserializationError>> _729_valueOrError0 = JSON_mZeroCopy_mDeserializer_mObjects_Compile.__default.Bracketed(cs, json);
      if ((_729_valueOrError0).IsFailure()) {
        return (_729_valueOrError0).PropagateFailure<JSON_mUtils_mCursors_Compile._ISplit<JSON_mGrammar_Compile._IBracketed<JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mGrammar_Compile._IjKeyValue, JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mUtils_mViews_mCore_Compile._IView__>>>();
      } else {
        JSON_mUtils_mCursors_Compile._ISplit<JSON_mGrammar_Compile._IBracketed<JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mGrammar_Compile._IjKeyValue, JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mUtils_mViews_mCore_Compile._IView__>> _730_sp = (_729_valueOrError0).Extract();
        return Wrappers_Compile.Result<JSON_mUtils_mCursors_Compile._ISplit<JSON_mGrammar_Compile._IBracketed<JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mGrammar_Compile._IjKeyValue, JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mUtils_mViews_mCore_Compile._IView__>>, JSON_mUtils_mCursors_Compile._ICursorError<JSON_mErrors_Compile._IDeserializationError>>.create_Success(_730_sp);
      }
    }
    public static Wrappers_Compile._IResult<JSON_mUtils_mCursors_Compile._ISplit<JSON_mUtils_mViews_mCore_Compile._IView__>, JSON_mUtils_mCursors_Compile._ICursorError<JSON_mErrors_Compile._IDeserializationError>> Open(JSON_mUtils_mCursors_Compile._ICursor__ cs) {
      Wrappers_Compile._IResult<JSON_mUtils_mCursors_Compile._ICursor__, JSON_mUtils_mCursors_Compile._ICursorError<JSON_mErrors_Compile._IDeserializationError>> _731_valueOrError0 = (cs).AssertByte<JSON_mErrors_Compile._IDeserializationError>(JSON_mZeroCopy_mDeserializer_mObjectParams_Compile.__default.OPEN);
      if ((_731_valueOrError0).IsFailure()) {
        return (_731_valueOrError0).PropagateFailure<JSON_mUtils_mCursors_Compile._ISplit<JSON_mUtils_mViews_mCore_Compile._IView__>>();
      } else {
        JSON_mUtils_mCursors_Compile._ICursor__ _732_cs = (_731_valueOrError0).Extract();
        return Wrappers_Compile.Result<JSON_mUtils_mCursors_Compile._ISplit<JSON_mUtils_mViews_mCore_Compile._IView__>, JSON_mUtils_mCursors_Compile._ICursorError<JSON_mErrors_Compile._IDeserializationError>>.create_Success((_732_cs).Split());
      }
    }
    public static Wrappers_Compile._IResult<JSON_mUtils_mCursors_Compile._ISplit<JSON_mUtils_mViews_mCore_Compile._IView__>, JSON_mUtils_mCursors_Compile._ICursorError<JSON_mErrors_Compile._IDeserializationError>> Close(JSON_mUtils_mCursors_Compile._ICursor__ cs) {
      Wrappers_Compile._IResult<JSON_mUtils_mCursors_Compile._ICursor__, JSON_mUtils_mCursors_Compile._ICursorError<JSON_mErrors_Compile._IDeserializationError>> _733_valueOrError0 = (cs).AssertByte<JSON_mErrors_Compile._IDeserializationError>(JSON_mZeroCopy_mDeserializer_mObjectParams_Compile.__default.CLOSE);
      if ((_733_valueOrError0).IsFailure()) {
        return (_733_valueOrError0).PropagateFailure<JSON_mUtils_mCursors_Compile._ISplit<JSON_mUtils_mViews_mCore_Compile._IView__>>();
      } else {
        JSON_mUtils_mCursors_Compile._ICursor__ _734_cs = (_733_valueOrError0).Extract();
        return Wrappers_Compile.Result<JSON_mUtils_mCursors_Compile._ISplit<JSON_mUtils_mViews_mCore_Compile._IView__>, JSON_mUtils_mCursors_Compile._ICursorError<JSON_mErrors_Compile._IDeserializationError>>.create_Success((_734_cs).Split());
      }
    }
    public static JSON_mUtils_mCursors_Compile._ISplit<JSON_mGrammar_Compile._IBracketed<JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mGrammar_Compile._IjKeyValue, JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mUtils_mViews_mCore_Compile._IView__>> BracketedFromParts(JSON_mUtils_mCursors_Compile._ISplit<JSON_mGrammar_Compile._IStructural<JSON_mUtils_mViews_mCore_Compile._IView__>> open, JSON_mUtils_mCursors_Compile._ISplit<Dafny.ISequence<JSON_mGrammar_Compile._ISuffixed<JSON_mGrammar_Compile._IjKeyValue, JSON_mUtils_mViews_mCore_Compile._IView__>>> elems, JSON_mUtils_mCursors_Compile._ISplit<JSON_mGrammar_Compile._IStructural<JSON_mUtils_mViews_mCore_Compile._IView__>> close)
    {
      JSON_mUtils_mCursors_Compile._ISplit<JSON_mGrammar_Compile._IBracketed<JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mGrammar_Compile._IjKeyValue, JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mUtils_mViews_mCore_Compile._IView__>> _735_sp = JSON_mUtils_mCursors_Compile.Split<JSON_mGrammar_Compile._IBracketed<JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mGrammar_Compile._IjKeyValue, JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mUtils_mViews_mCore_Compile._IView__>>.create(JSON_mGrammar_Compile.Bracketed<JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mGrammar_Compile._IjKeyValue, JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mUtils_mViews_mCore_Compile._IView__>.create((open).dtor_t, (elems).dtor_t, (close).dtor_t), (close).dtor_cs);
      return _735_sp;
    }
    public static JSON_mUtils_mCursors_Compile._ISplit<Dafny.ISequence<JSON_mGrammar_Compile._ISuffixed<JSON_mGrammar_Compile._IjKeyValue, JSON_mUtils_mViews_mCore_Compile._IView__>>> AppendWithSuffix(JSON_mUtils_mCursors_Compile._ISplit<Dafny.ISequence<JSON_mGrammar_Compile._ISuffixed<JSON_mGrammar_Compile._IjKeyValue, JSON_mUtils_mViews_mCore_Compile._IView__>>> elems, JSON_mUtils_mCursors_Compile._ISplit<JSON_mGrammar_Compile._IjKeyValue> elem, JSON_mUtils_mCursors_Compile._ISplit<JSON_mGrammar_Compile._IStructural<JSON_mUtils_mViews_mCore_Compile._IView__>> sep)
    {
      JSON_mGrammar_Compile._ISuffixed<JSON_mGrammar_Compile._IjKeyValue, JSON_mUtils_mViews_mCore_Compile._IView__> _736_suffixed = JSON_mGrammar_Compile.Suffixed<JSON_mGrammar_Compile._IjKeyValue, JSON_mUtils_mViews_mCore_Compile._IView__>.create((elem).dtor_t, JSON_mGrammar_Compile.Maybe<JSON_mGrammar_Compile._IStructural<JSON_mUtils_mViews_mCore_Compile._IView__>>.create_NonEmpty((sep).dtor_t));
      JSON_mUtils_mCursors_Compile._ISplit<Dafny.ISequence<JSON_mGrammar_Compile._ISuffixed<JSON_mGrammar_Compile._IjKeyValue, JSON_mUtils_mViews_mCore_Compile._IView__>>> _737_elems_k = JSON_mUtils_mCursors_Compile.Split<Dafny.ISequence<JSON_mGrammar_Compile._ISuffixed<JSON_mGrammar_Compile._IjKeyValue, JSON_mUtils_mViews_mCore_Compile._IView__>>>.create(Dafny.Sequence<JSON_mGrammar_Compile._ISuffixed<JSON_mGrammar_Compile._IjKeyValue, JSON_mUtils_mViews_mCore_Compile._IView__>>.Concat((elems).dtor_t, Dafny.Sequence<JSON_mGrammar_Compile._ISuffixed<JSON_mGrammar_Compile._IjKeyValue, JSON_mUtils_mViews_mCore_Compile._IView__>>.FromElements(_736_suffixed)), (sep).dtor_cs);
      return _737_elems_k;
    }
    public static JSON_mUtils_mCursors_Compile._ISplit<Dafny.ISequence<JSON_mGrammar_Compile._ISuffixed<JSON_mGrammar_Compile._IjKeyValue, JSON_mUtils_mViews_mCore_Compile._IView__>>> AppendLast(JSON_mUtils_mCursors_Compile._ISplit<Dafny.ISequence<JSON_mGrammar_Compile._ISuffixed<JSON_mGrammar_Compile._IjKeyValue, JSON_mUtils_mViews_mCore_Compile._IView__>>> elems, JSON_mUtils_mCursors_Compile._ISplit<JSON_mGrammar_Compile._IjKeyValue> elem, JSON_mUtils_mCursors_Compile._ISplit<JSON_mGrammar_Compile._IStructural<JSON_mUtils_mViews_mCore_Compile._IView__>> sep)
    {
      JSON_mGrammar_Compile._ISuffixed<JSON_mGrammar_Compile._IjKeyValue, JSON_mUtils_mViews_mCore_Compile._IView__> _738_suffixed = JSON_mGrammar_Compile.Suffixed<JSON_mGrammar_Compile._IjKeyValue, JSON_mUtils_mViews_mCore_Compile._IView__>.create((elem).dtor_t, JSON_mGrammar_Compile.Maybe<JSON_mGrammar_Compile._IStructural<JSON_mUtils_mViews_mCore_Compile._IView__>>.create_Empty());
      JSON_mUtils_mCursors_Compile._ISplit<Dafny.ISequence<JSON_mGrammar_Compile._ISuffixed<JSON_mGrammar_Compile._IjKeyValue, JSON_mUtils_mViews_mCore_Compile._IView__>>> _739_elems_k = JSON_mUtils_mCursors_Compile.Split<Dafny.ISequence<JSON_mGrammar_Compile._ISuffixed<JSON_mGrammar_Compile._IjKeyValue, JSON_mUtils_mViews_mCore_Compile._IView__>>>.create(Dafny.Sequence<JSON_mGrammar_Compile._ISuffixed<JSON_mGrammar_Compile._IjKeyValue, JSON_mUtils_mViews_mCore_Compile._IView__>>.Concat((elems).dtor_t, Dafny.Sequence<JSON_mGrammar_Compile._ISuffixed<JSON_mGrammar_Compile._IjKeyValue, JSON_mUtils_mViews_mCore_Compile._IView__>>.FromElements(_738_suffixed)), (elem).dtor_cs);
      return _739_elems_k;
    }
    public static Wrappers_Compile._IResult<JSON_mUtils_mCursors_Compile._ISplit<JSON_mGrammar_Compile._IBracketed<JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mGrammar_Compile._IjKeyValue, JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mUtils_mViews_mCore_Compile._IView__>>, JSON_mUtils_mCursors_Compile._ICursorError<JSON_mErrors_Compile._IDeserializationError>> Elements(JSON_mUtils_mParsers_Compile._ISubParser__<JSON_mGrammar_Compile._IValue, JSON_mErrors_Compile._IDeserializationError> json, JSON_mUtils_mCursors_Compile._ISplit<JSON_mGrammar_Compile._IStructural<JSON_mUtils_mViews_mCore_Compile._IView__>> open, JSON_mUtils_mCursors_Compile._ISplit<Dafny.ISequence<JSON_mGrammar_Compile._ISuffixed<JSON_mGrammar_Compile._IjKeyValue, JSON_mUtils_mViews_mCore_Compile._IView__>>> elems)
    {
    TAIL_CALL_START: ;
      Wrappers_Compile._IResult<JSON_mUtils_mCursors_Compile._ISplit<JSON_mGrammar_Compile._IjKeyValue>, JSON_mUtils_mCursors_Compile._ICursorError<JSON_mErrors_Compile._IDeserializationError>> _740_valueOrError0 = JSON_mZeroCopy_mDeserializer_mObjectParams_Compile.__default.Element((elems).dtor_cs, json);
      if ((_740_valueOrError0).IsFailure()) {
        return (_740_valueOrError0).PropagateFailure<JSON_mUtils_mCursors_Compile._ISplit<JSON_mGrammar_Compile._IBracketed<JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mGrammar_Compile._IjKeyValue, JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mUtils_mViews_mCore_Compile._IView__>>>();
      } else {
        JSON_mUtils_mCursors_Compile._ISplit<JSON_mGrammar_Compile._IjKeyValue> _741_elem = (_740_valueOrError0).Extract();
        JSON_mUtils_mCursors_Compile._ISplit<JSON_mGrammar_Compile._IStructural<JSON_mUtils_mViews_mCore_Compile._IView__>> _742_sep = JSON_mZeroCopy_mDeserializer_mCore_Compile.__default.TryStructural((_741_elem).dtor_cs);
        short _743_s0 = (((_742_sep).dtor_t).dtor_t).Peek();
        if ((_743_s0) == ((short)(JSON_mZeroCopy_mDeserializer_mObjects_Compile.__default.SEPARATOR))) {
          JSON_mUtils_mCursors_Compile._ISplit<Dafny.ISequence<JSON_mGrammar_Compile._ISuffixed<JSON_mGrammar_Compile._IjKeyValue, JSON_mUtils_mViews_mCore_Compile._IView__>>> _744_elems = JSON_mZeroCopy_mDeserializer_mObjects_Compile.__default.AppendWithSuffix(elems, _741_elem, _742_sep);
          JSON_mUtils_mParsers_Compile._ISubParser__<JSON_mGrammar_Compile._IValue, JSON_mErrors_Compile._IDeserializationError> _in123 = json;
          JSON_mUtils_mCursors_Compile._ISplit<JSON_mGrammar_Compile._IStructural<JSON_mUtils_mViews_mCore_Compile._IView__>> _in124 = open;
          JSON_mUtils_mCursors_Compile._ISplit<Dafny.ISequence<JSON_mGrammar_Compile._ISuffixed<JSON_mGrammar_Compile._IjKeyValue, JSON_mUtils_mViews_mCore_Compile._IView__>>> _in125 = _744_elems;
          json = _in123;
          open = _in124;
          elems = _in125;
          goto TAIL_CALL_START;
        } else if ((_743_s0) == ((short)(JSON_mZeroCopy_mDeserializer_mObjectParams_Compile.__default.CLOSE))) {
          JSON_mUtils_mCursors_Compile._ISplit<Dafny.ISequence<JSON_mGrammar_Compile._ISuffixed<JSON_mGrammar_Compile._IjKeyValue, JSON_mUtils_mViews_mCore_Compile._IView__>>> _745_elems_k = JSON_mZeroCopy_mDeserializer_mObjects_Compile.__default.AppendLast(elems, _741_elem, _742_sep);
          JSON_mUtils_mCursors_Compile._ISplit<JSON_mGrammar_Compile._IBracketed<JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mGrammar_Compile._IjKeyValue, JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mUtils_mViews_mCore_Compile._IView__>> _746_bracketed = JSON_mZeroCopy_mDeserializer_mObjects_Compile.__default.BracketedFromParts(open, _745_elems_k, _742_sep);
          return Wrappers_Compile.Result<JSON_mUtils_mCursors_Compile._ISplit<JSON_mGrammar_Compile._IBracketed<JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mGrammar_Compile._IjKeyValue, JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mUtils_mViews_mCore_Compile._IView__>>, JSON_mUtils_mCursors_Compile._ICursorError<JSON_mErrors_Compile._IDeserializationError>>.create_Success(_746_bracketed);
        } else {
          byte _747_separator = JSON_mZeroCopy_mDeserializer_mObjects_Compile.__default.SEPARATOR;
          Wrappers_Compile._IResult<JSON_mUtils_mCursors_Compile._ISplit<JSON_mGrammar_Compile._IBracketed<JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mGrammar_Compile._IjKeyValue, JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mUtils_mViews_mCore_Compile._IView__>>, JSON_mUtils_mCursors_Compile._ICursorError<JSON_mErrors_Compile._IDeserializationError>> _748_pr = Wrappers_Compile.Result<JSON_mUtils_mCursors_Compile._ISplit<JSON_mGrammar_Compile._IBracketed<JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mGrammar_Compile._IjKeyValue, JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mUtils_mViews_mCore_Compile._IView__>>, JSON_mUtils_mCursors_Compile._ICursorError<JSON_mErrors_Compile._IDeserializationError>>.create_Failure(JSON_mUtils_mCursors_Compile.CursorError<JSON_mErrors_Compile._IDeserializationError>.create_ExpectingAnyByte(Dafny.Sequence<byte>.FromElements(JSON_mZeroCopy_mDeserializer_mObjectParams_Compile.__default.CLOSE, _747_separator), _743_s0));
          return _748_pr;
        }
      }
    }
    public static Wrappers_Compile._IResult<JSON_mUtils_mCursors_Compile._ISplit<JSON_mGrammar_Compile._IBracketed<JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mGrammar_Compile._IjKeyValue, JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mUtils_mViews_mCore_Compile._IView__>>, JSON_mUtils_mCursors_Compile._ICursorError<JSON_mErrors_Compile._IDeserializationError>> Bracketed(JSON_mUtils_mCursors_Compile._ICursor__ cs, JSON_mUtils_mParsers_Compile._ISubParser__<JSON_mGrammar_Compile._IValue, JSON_mErrors_Compile._IDeserializationError> json)
    {
      Wrappers_Compile._IResult<JSON_mUtils_mCursors_Compile._ISplit<JSON_mGrammar_Compile._IStructural<JSON_mUtils_mViews_mCore_Compile._IView__>>, JSON_mUtils_mCursors_Compile._ICursorError<JSON_mErrors_Compile._IDeserializationError>> _749_valueOrError0 = JSON_mZeroCopy_mDeserializer_mCore_Compile.__default.Structural<JSON_mUtils_mViews_mCore_Compile._IView__>(cs, JSON_mUtils_mParsers_Compile.Parser__<JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mErrors_Compile._IDeserializationError>.create(JSON_mZeroCopy_mDeserializer_mObjects_Compile.__default.Open));
      if ((_749_valueOrError0).IsFailure()) {
        return (_749_valueOrError0).PropagateFailure<JSON_mUtils_mCursors_Compile._ISplit<JSON_mGrammar_Compile._IBracketed<JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mGrammar_Compile._IjKeyValue, JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mUtils_mViews_mCore_Compile._IView__>>>();
      } else {
        JSON_mUtils_mCursors_Compile._ISplit<JSON_mGrammar_Compile._IStructural<JSON_mUtils_mViews_mCore_Compile._IView__>> _750_open = (_749_valueOrError0).Extract();
        JSON_mUtils_mCursors_Compile._ISplit<Dafny.ISequence<JSON_mGrammar_Compile._ISuffixed<JSON_mGrammar_Compile._IjKeyValue, JSON_mUtils_mViews_mCore_Compile._IView__>>> _751_elems = JSON_mUtils_mCursors_Compile.Split<Dafny.ISequence<JSON_mGrammar_Compile._ISuffixed<JSON_mGrammar_Compile._IjKeyValue, JSON_mUtils_mViews_mCore_Compile._IView__>>>.create(Dafny.Sequence<JSON_mGrammar_Compile._ISuffixed<JSON_mGrammar_Compile._IjKeyValue, JSON_mUtils_mViews_mCore_Compile._IView__>>.FromElements(), (_750_open).dtor_cs);
        if ((((_750_open).dtor_cs).Peek()) == ((short)(JSON_mZeroCopy_mDeserializer_mObjectParams_Compile.__default.CLOSE))) {
          Wrappers_Compile._IResult<JSON_mUtils_mCursors_Compile._ISplit<JSON_mGrammar_Compile._IStructural<JSON_mUtils_mViews_mCore_Compile._IView__>>, JSON_mUtils_mCursors_Compile._ICursorError<JSON_mErrors_Compile._IDeserializationError>> _752_valueOrError1 = JSON_mZeroCopy_mDeserializer_mCore_Compile.__default.Structural<JSON_mUtils_mViews_mCore_Compile._IView__>((_750_open).dtor_cs, JSON_mUtils_mParsers_Compile.Parser__<JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mErrors_Compile._IDeserializationError>.create(JSON_mZeroCopy_mDeserializer_mObjects_Compile.__default.Close));
          if ((_752_valueOrError1).IsFailure()) {
            return (_752_valueOrError1).PropagateFailure<JSON_mUtils_mCursors_Compile._ISplit<JSON_mGrammar_Compile._IBracketed<JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mGrammar_Compile._IjKeyValue, JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mUtils_mViews_mCore_Compile._IView__>>>();
          } else {
            JSON_mUtils_mCursors_Compile._ISplit<JSON_mGrammar_Compile._IStructural<JSON_mUtils_mViews_mCore_Compile._IView__>> _753_close = (_752_valueOrError1).Extract();
            return Wrappers_Compile.Result<JSON_mUtils_mCursors_Compile._ISplit<JSON_mGrammar_Compile._IBracketed<JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mGrammar_Compile._IjKeyValue, JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mUtils_mViews_mCore_Compile._IView__>>, JSON_mUtils_mCursors_Compile._ICursorError<JSON_mErrors_Compile._IDeserializationError>>.create_Success(JSON_mZeroCopy_mDeserializer_mObjects_Compile.__default.BracketedFromParts(_750_open, _751_elems, _753_close));
          }
        } else {
          return JSON_mZeroCopy_mDeserializer_mObjects_Compile.__default.Elements(json, _750_open, _751_elems);
        }
      }
    }
    public static byte SEPARATOR { get {
      return (byte)(',');
    } }
  }

  public partial class jopen {
    private static readonly JSON_mUtils_mViews_mCore_Compile._IView__ Witness = JSON_mUtils_mViews_mCore_Compile.View__.OfBytes(Dafny.Sequence<byte>.FromElements(JSON_mZeroCopy_mDeserializer_mObjectParams_Compile.__default.OPEN));
    public static JSON_mUtils_mViews_mCore_Compile._IView__ Default() {
      return Witness;
    }
    private static readonly Dafny.TypeDescriptor<JSON_mUtils_mViews_mCore_Compile._IView__> _TYPE = new Dafny.TypeDescriptor<JSON_mUtils_mViews_mCore_Compile._IView__>(JSON_mZeroCopy_mDeserializer_mObjects_Compile.jopen.Default());
    public static Dafny.TypeDescriptor<JSON_mUtils_mViews_mCore_Compile._IView__> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class jclose {
    private static readonly JSON_mUtils_mViews_mCore_Compile._IView__ Witness = JSON_mUtils_mViews_mCore_Compile.View__.OfBytes(Dafny.Sequence<byte>.FromElements(JSON_mZeroCopy_mDeserializer_mObjectParams_Compile.__default.CLOSE));
    public static JSON_mUtils_mViews_mCore_Compile._IView__ Default() {
      return Witness;
    }
    private static readonly Dafny.TypeDescriptor<JSON_mUtils_mViews_mCore_Compile._IView__> _TYPE = new Dafny.TypeDescriptor<JSON_mUtils_mViews_mCore_Compile._IView__>(JSON_mZeroCopy_mDeserializer_mObjects_Compile.jclose.Default());
    public static Dafny.TypeDescriptor<JSON_mUtils_mViews_mCore_Compile._IView__> _TypeDescriptor() {
      return _TYPE;
    }
  }
} // end of namespace JSON_mZeroCopy_mDeserializer_mObjects_Compile
namespace JSON_mZeroCopy_mDeserializer_mArrayParams_Compile {

  public partial class __default {
    public static Dafny.ISequence<byte> ElementSpec(JSON_mGrammar_Compile._IValue t) {
      return JSON_mConcreteSyntax_mSpec_Compile.__default.Value(t);
    }
    public static Wrappers_Compile._IResult<JSON_mUtils_mCursors_Compile._ISplit<JSON_mGrammar_Compile._IValue>, JSON_mUtils_mCursors_Compile._ICursorError<JSON_mErrors_Compile._IDeserializationError>> Element(JSON_mUtils_mCursors_Compile._ICursor__ cs, JSON_mUtils_mParsers_Compile._ISubParser__<JSON_mGrammar_Compile._IValue, JSON_mErrors_Compile._IDeserializationError> json)
    {
      return Dafny.Helpers.Id<Func<JSON_mUtils_mCursors_Compile._ICursor__, Wrappers_Compile._IResult<JSON_mUtils_mCursors_Compile._ISplit<JSON_mGrammar_Compile._IValue>, JSON_mUtils_mCursors_Compile._ICursorError<JSON_mErrors_Compile._IDeserializationError>>>>((json).dtor_fn)(cs);
    }
    public static byte OPEN { get {
      return (byte)('[');
    } }
    public static byte CLOSE { get {
      return (byte)(']');
    } }
  }
} // end of namespace JSON_mZeroCopy_mDeserializer_mArrayParams_Compile
namespace JSON_mZeroCopy_mDeserializer_mArrays_Compile {

  public partial class __default {
    public static Wrappers_Compile._IResult<JSON_mUtils_mCursors_Compile._ISplit<JSON_mGrammar_Compile._IBracketed<JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mGrammar_Compile._IValue, JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mUtils_mViews_mCore_Compile._IView__>>, JSON_mUtils_mCursors_Compile._ICursorError<JSON_mErrors_Compile._IDeserializationError>> Array(JSON_mUtils_mCursors_Compile._ICursor__ cs, JSON_mUtils_mParsers_Compile._ISubParser__<JSON_mGrammar_Compile._IValue, JSON_mErrors_Compile._IDeserializationError> json)
    {
      Wrappers_Compile._IResult<JSON_mUtils_mCursors_Compile._ISplit<JSON_mGrammar_Compile._IBracketed<JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mGrammar_Compile._IValue, JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mUtils_mViews_mCore_Compile._IView__>>, JSON_mUtils_mCursors_Compile._ICursorError<JSON_mErrors_Compile._IDeserializationError>> _754_valueOrError0 = JSON_mZeroCopy_mDeserializer_mArrays_Compile.__default.Bracketed(cs, json);
      if ((_754_valueOrError0).IsFailure()) {
        return (_754_valueOrError0).PropagateFailure<JSON_mUtils_mCursors_Compile._ISplit<JSON_mGrammar_Compile._IBracketed<JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mGrammar_Compile._IValue, JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mUtils_mViews_mCore_Compile._IView__>>>();
      } else {
        JSON_mUtils_mCursors_Compile._ISplit<JSON_mGrammar_Compile._IBracketed<JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mGrammar_Compile._IValue, JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mUtils_mViews_mCore_Compile._IView__>> _755_sp = (_754_valueOrError0).Extract();
        return Wrappers_Compile.Result<JSON_mUtils_mCursors_Compile._ISplit<JSON_mGrammar_Compile._IBracketed<JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mGrammar_Compile._IValue, JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mUtils_mViews_mCore_Compile._IView__>>, JSON_mUtils_mCursors_Compile._ICursorError<JSON_mErrors_Compile._IDeserializationError>>.create_Success(_755_sp);
      }
    }
    public static Wrappers_Compile._IResult<JSON_mUtils_mCursors_Compile._ISplit<JSON_mUtils_mViews_mCore_Compile._IView__>, JSON_mUtils_mCursors_Compile._ICursorError<JSON_mErrors_Compile._IDeserializationError>> Open(JSON_mUtils_mCursors_Compile._ICursor__ cs) {
      Wrappers_Compile._IResult<JSON_mUtils_mCursors_Compile._ICursor__, JSON_mUtils_mCursors_Compile._ICursorError<JSON_mErrors_Compile._IDeserializationError>> _756_valueOrError0 = (cs).AssertByte<JSON_mErrors_Compile._IDeserializationError>(JSON_mZeroCopy_mDeserializer_mArrayParams_Compile.__default.OPEN);
      if ((_756_valueOrError0).IsFailure()) {
        return (_756_valueOrError0).PropagateFailure<JSON_mUtils_mCursors_Compile._ISplit<JSON_mUtils_mViews_mCore_Compile._IView__>>();
      } else {
        JSON_mUtils_mCursors_Compile._ICursor__ _757_cs = (_756_valueOrError0).Extract();
        return Wrappers_Compile.Result<JSON_mUtils_mCursors_Compile._ISplit<JSON_mUtils_mViews_mCore_Compile._IView__>, JSON_mUtils_mCursors_Compile._ICursorError<JSON_mErrors_Compile._IDeserializationError>>.create_Success((_757_cs).Split());
      }
    }
    public static Wrappers_Compile._IResult<JSON_mUtils_mCursors_Compile._ISplit<JSON_mUtils_mViews_mCore_Compile._IView__>, JSON_mUtils_mCursors_Compile._ICursorError<JSON_mErrors_Compile._IDeserializationError>> Close(JSON_mUtils_mCursors_Compile._ICursor__ cs) {
      Wrappers_Compile._IResult<JSON_mUtils_mCursors_Compile._ICursor__, JSON_mUtils_mCursors_Compile._ICursorError<JSON_mErrors_Compile._IDeserializationError>> _758_valueOrError0 = (cs).AssertByte<JSON_mErrors_Compile._IDeserializationError>(JSON_mZeroCopy_mDeserializer_mArrayParams_Compile.__default.CLOSE);
      if ((_758_valueOrError0).IsFailure()) {
        return (_758_valueOrError0).PropagateFailure<JSON_mUtils_mCursors_Compile._ISplit<JSON_mUtils_mViews_mCore_Compile._IView__>>();
      } else {
        JSON_mUtils_mCursors_Compile._ICursor__ _759_cs = (_758_valueOrError0).Extract();
        return Wrappers_Compile.Result<JSON_mUtils_mCursors_Compile._ISplit<JSON_mUtils_mViews_mCore_Compile._IView__>, JSON_mUtils_mCursors_Compile._ICursorError<JSON_mErrors_Compile._IDeserializationError>>.create_Success((_759_cs).Split());
      }
    }
    public static JSON_mUtils_mCursors_Compile._ISplit<JSON_mGrammar_Compile._IBracketed<JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mGrammar_Compile._IValue, JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mUtils_mViews_mCore_Compile._IView__>> BracketedFromParts(JSON_mUtils_mCursors_Compile._ISplit<JSON_mGrammar_Compile._IStructural<JSON_mUtils_mViews_mCore_Compile._IView__>> open, JSON_mUtils_mCursors_Compile._ISplit<Dafny.ISequence<JSON_mGrammar_Compile._ISuffixed<JSON_mGrammar_Compile._IValue, JSON_mUtils_mViews_mCore_Compile._IView__>>> elems, JSON_mUtils_mCursors_Compile._ISplit<JSON_mGrammar_Compile._IStructural<JSON_mUtils_mViews_mCore_Compile._IView__>> close)
    {
      JSON_mUtils_mCursors_Compile._ISplit<JSON_mGrammar_Compile._IBracketed<JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mGrammar_Compile._IValue, JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mUtils_mViews_mCore_Compile._IView__>> _760_sp = JSON_mUtils_mCursors_Compile.Split<JSON_mGrammar_Compile._IBracketed<JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mGrammar_Compile._IValue, JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mUtils_mViews_mCore_Compile._IView__>>.create(JSON_mGrammar_Compile.Bracketed<JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mGrammar_Compile._IValue, JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mUtils_mViews_mCore_Compile._IView__>.create((open).dtor_t, (elems).dtor_t, (close).dtor_t), (close).dtor_cs);
      return _760_sp;
    }
    public static JSON_mUtils_mCursors_Compile._ISplit<Dafny.ISequence<JSON_mGrammar_Compile._ISuffixed<JSON_mGrammar_Compile._IValue, JSON_mUtils_mViews_mCore_Compile._IView__>>> AppendWithSuffix(JSON_mUtils_mCursors_Compile._ISplit<Dafny.ISequence<JSON_mGrammar_Compile._ISuffixed<JSON_mGrammar_Compile._IValue, JSON_mUtils_mViews_mCore_Compile._IView__>>> elems, JSON_mUtils_mCursors_Compile._ISplit<JSON_mGrammar_Compile._IValue> elem, JSON_mUtils_mCursors_Compile._ISplit<JSON_mGrammar_Compile._IStructural<JSON_mUtils_mViews_mCore_Compile._IView__>> sep)
    {
      JSON_mGrammar_Compile._ISuffixed<JSON_mGrammar_Compile._IValue, JSON_mUtils_mViews_mCore_Compile._IView__> _761_suffixed = JSON_mGrammar_Compile.Suffixed<JSON_mGrammar_Compile._IValue, JSON_mUtils_mViews_mCore_Compile._IView__>.create((elem).dtor_t, JSON_mGrammar_Compile.Maybe<JSON_mGrammar_Compile._IStructural<JSON_mUtils_mViews_mCore_Compile._IView__>>.create_NonEmpty((sep).dtor_t));
      JSON_mUtils_mCursors_Compile._ISplit<Dafny.ISequence<JSON_mGrammar_Compile._ISuffixed<JSON_mGrammar_Compile._IValue, JSON_mUtils_mViews_mCore_Compile._IView__>>> _762_elems_k = JSON_mUtils_mCursors_Compile.Split<Dafny.ISequence<JSON_mGrammar_Compile._ISuffixed<JSON_mGrammar_Compile._IValue, JSON_mUtils_mViews_mCore_Compile._IView__>>>.create(Dafny.Sequence<JSON_mGrammar_Compile._ISuffixed<JSON_mGrammar_Compile._IValue, JSON_mUtils_mViews_mCore_Compile._IView__>>.Concat((elems).dtor_t, Dafny.Sequence<JSON_mGrammar_Compile._ISuffixed<JSON_mGrammar_Compile._IValue, JSON_mUtils_mViews_mCore_Compile._IView__>>.FromElements(_761_suffixed)), (sep).dtor_cs);
      return _762_elems_k;
    }
    public static JSON_mUtils_mCursors_Compile._ISplit<Dafny.ISequence<JSON_mGrammar_Compile._ISuffixed<JSON_mGrammar_Compile._IValue, JSON_mUtils_mViews_mCore_Compile._IView__>>> AppendLast(JSON_mUtils_mCursors_Compile._ISplit<Dafny.ISequence<JSON_mGrammar_Compile._ISuffixed<JSON_mGrammar_Compile._IValue, JSON_mUtils_mViews_mCore_Compile._IView__>>> elems, JSON_mUtils_mCursors_Compile._ISplit<JSON_mGrammar_Compile._IValue> elem, JSON_mUtils_mCursors_Compile._ISplit<JSON_mGrammar_Compile._IStructural<JSON_mUtils_mViews_mCore_Compile._IView__>> sep)
    {
      JSON_mGrammar_Compile._ISuffixed<JSON_mGrammar_Compile._IValue, JSON_mUtils_mViews_mCore_Compile._IView__> _763_suffixed = JSON_mGrammar_Compile.Suffixed<JSON_mGrammar_Compile._IValue, JSON_mUtils_mViews_mCore_Compile._IView__>.create((elem).dtor_t, JSON_mGrammar_Compile.Maybe<JSON_mGrammar_Compile._IStructural<JSON_mUtils_mViews_mCore_Compile._IView__>>.create_Empty());
      JSON_mUtils_mCursors_Compile._ISplit<Dafny.ISequence<JSON_mGrammar_Compile._ISuffixed<JSON_mGrammar_Compile._IValue, JSON_mUtils_mViews_mCore_Compile._IView__>>> _764_elems_k = JSON_mUtils_mCursors_Compile.Split<Dafny.ISequence<JSON_mGrammar_Compile._ISuffixed<JSON_mGrammar_Compile._IValue, JSON_mUtils_mViews_mCore_Compile._IView__>>>.create(Dafny.Sequence<JSON_mGrammar_Compile._ISuffixed<JSON_mGrammar_Compile._IValue, JSON_mUtils_mViews_mCore_Compile._IView__>>.Concat((elems).dtor_t, Dafny.Sequence<JSON_mGrammar_Compile._ISuffixed<JSON_mGrammar_Compile._IValue, JSON_mUtils_mViews_mCore_Compile._IView__>>.FromElements(_763_suffixed)), (elem).dtor_cs);
      return _764_elems_k;
    }
    public static Wrappers_Compile._IResult<JSON_mUtils_mCursors_Compile._ISplit<JSON_mGrammar_Compile._IBracketed<JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mGrammar_Compile._IValue, JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mUtils_mViews_mCore_Compile._IView__>>, JSON_mUtils_mCursors_Compile._ICursorError<JSON_mErrors_Compile._IDeserializationError>> Elements(JSON_mUtils_mParsers_Compile._ISubParser__<JSON_mGrammar_Compile._IValue, JSON_mErrors_Compile._IDeserializationError> json, JSON_mUtils_mCursors_Compile._ISplit<JSON_mGrammar_Compile._IStructural<JSON_mUtils_mViews_mCore_Compile._IView__>> open, JSON_mUtils_mCursors_Compile._ISplit<Dafny.ISequence<JSON_mGrammar_Compile._ISuffixed<JSON_mGrammar_Compile._IValue, JSON_mUtils_mViews_mCore_Compile._IView__>>> elems)
    {
    TAIL_CALL_START: ;
      Wrappers_Compile._IResult<JSON_mUtils_mCursors_Compile._ISplit<JSON_mGrammar_Compile._IValue>, JSON_mUtils_mCursors_Compile._ICursorError<JSON_mErrors_Compile._IDeserializationError>> _765_valueOrError0 = JSON_mZeroCopy_mDeserializer_mArrayParams_Compile.__default.Element((elems).dtor_cs, json);
      if ((_765_valueOrError0).IsFailure()) {
        return (_765_valueOrError0).PropagateFailure<JSON_mUtils_mCursors_Compile._ISplit<JSON_mGrammar_Compile._IBracketed<JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mGrammar_Compile._IValue, JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mUtils_mViews_mCore_Compile._IView__>>>();
      } else {
        JSON_mUtils_mCursors_Compile._ISplit<JSON_mGrammar_Compile._IValue> _766_elem = (_765_valueOrError0).Extract();
        JSON_mUtils_mCursors_Compile._ISplit<JSON_mGrammar_Compile._IStructural<JSON_mUtils_mViews_mCore_Compile._IView__>> _767_sep = JSON_mZeroCopy_mDeserializer_mCore_Compile.__default.TryStructural((_766_elem).dtor_cs);
        short _768_s0 = (((_767_sep).dtor_t).dtor_t).Peek();
        if ((_768_s0) == ((short)(JSON_mZeroCopy_mDeserializer_mArrays_Compile.__default.SEPARATOR))) {
          JSON_mUtils_mCursors_Compile._ISplit<Dafny.ISequence<JSON_mGrammar_Compile._ISuffixed<JSON_mGrammar_Compile._IValue, JSON_mUtils_mViews_mCore_Compile._IView__>>> _769_elems = JSON_mZeroCopy_mDeserializer_mArrays_Compile.__default.AppendWithSuffix(elems, _766_elem, _767_sep);
          JSON_mUtils_mParsers_Compile._ISubParser__<JSON_mGrammar_Compile._IValue, JSON_mErrors_Compile._IDeserializationError> _in126 = json;
          JSON_mUtils_mCursors_Compile._ISplit<JSON_mGrammar_Compile._IStructural<JSON_mUtils_mViews_mCore_Compile._IView__>> _in127 = open;
          JSON_mUtils_mCursors_Compile._ISplit<Dafny.ISequence<JSON_mGrammar_Compile._ISuffixed<JSON_mGrammar_Compile._IValue, JSON_mUtils_mViews_mCore_Compile._IView__>>> _in128 = _769_elems;
          json = _in126;
          open = _in127;
          elems = _in128;
          goto TAIL_CALL_START;
        } else if ((_768_s0) == ((short)(JSON_mZeroCopy_mDeserializer_mArrayParams_Compile.__default.CLOSE))) {
          JSON_mUtils_mCursors_Compile._ISplit<Dafny.ISequence<JSON_mGrammar_Compile._ISuffixed<JSON_mGrammar_Compile._IValue, JSON_mUtils_mViews_mCore_Compile._IView__>>> _770_elems_k = JSON_mZeroCopy_mDeserializer_mArrays_Compile.__default.AppendLast(elems, _766_elem, _767_sep);
          JSON_mUtils_mCursors_Compile._ISplit<JSON_mGrammar_Compile._IBracketed<JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mGrammar_Compile._IValue, JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mUtils_mViews_mCore_Compile._IView__>> _771_bracketed = JSON_mZeroCopy_mDeserializer_mArrays_Compile.__default.BracketedFromParts(open, _770_elems_k, _767_sep);
          return Wrappers_Compile.Result<JSON_mUtils_mCursors_Compile._ISplit<JSON_mGrammar_Compile._IBracketed<JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mGrammar_Compile._IValue, JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mUtils_mViews_mCore_Compile._IView__>>, JSON_mUtils_mCursors_Compile._ICursorError<JSON_mErrors_Compile._IDeserializationError>>.create_Success(_771_bracketed);
        } else {
          byte _772_separator = JSON_mZeroCopy_mDeserializer_mArrays_Compile.__default.SEPARATOR;
          Wrappers_Compile._IResult<JSON_mUtils_mCursors_Compile._ISplit<JSON_mGrammar_Compile._IBracketed<JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mGrammar_Compile._IValue, JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mUtils_mViews_mCore_Compile._IView__>>, JSON_mUtils_mCursors_Compile._ICursorError<JSON_mErrors_Compile._IDeserializationError>> _773_pr = Wrappers_Compile.Result<JSON_mUtils_mCursors_Compile._ISplit<JSON_mGrammar_Compile._IBracketed<JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mGrammar_Compile._IValue, JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mUtils_mViews_mCore_Compile._IView__>>, JSON_mUtils_mCursors_Compile._ICursorError<JSON_mErrors_Compile._IDeserializationError>>.create_Failure(JSON_mUtils_mCursors_Compile.CursorError<JSON_mErrors_Compile._IDeserializationError>.create_ExpectingAnyByte(Dafny.Sequence<byte>.FromElements(JSON_mZeroCopy_mDeserializer_mArrayParams_Compile.__default.CLOSE, _772_separator), _768_s0));
          return _773_pr;
        }
      }
    }
    public static Wrappers_Compile._IResult<JSON_mUtils_mCursors_Compile._ISplit<JSON_mGrammar_Compile._IBracketed<JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mGrammar_Compile._IValue, JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mUtils_mViews_mCore_Compile._IView__>>, JSON_mUtils_mCursors_Compile._ICursorError<JSON_mErrors_Compile._IDeserializationError>> Bracketed(JSON_mUtils_mCursors_Compile._ICursor__ cs, JSON_mUtils_mParsers_Compile._ISubParser__<JSON_mGrammar_Compile._IValue, JSON_mErrors_Compile._IDeserializationError> json)
    {
      Wrappers_Compile._IResult<JSON_mUtils_mCursors_Compile._ISplit<JSON_mGrammar_Compile._IStructural<JSON_mUtils_mViews_mCore_Compile._IView__>>, JSON_mUtils_mCursors_Compile._ICursorError<JSON_mErrors_Compile._IDeserializationError>> _774_valueOrError0 = JSON_mZeroCopy_mDeserializer_mCore_Compile.__default.Structural<JSON_mUtils_mViews_mCore_Compile._IView__>(cs, JSON_mUtils_mParsers_Compile.Parser__<JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mErrors_Compile._IDeserializationError>.create(JSON_mZeroCopy_mDeserializer_mArrays_Compile.__default.Open));
      if ((_774_valueOrError0).IsFailure()) {
        return (_774_valueOrError0).PropagateFailure<JSON_mUtils_mCursors_Compile._ISplit<JSON_mGrammar_Compile._IBracketed<JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mGrammar_Compile._IValue, JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mUtils_mViews_mCore_Compile._IView__>>>();
      } else {
        JSON_mUtils_mCursors_Compile._ISplit<JSON_mGrammar_Compile._IStructural<JSON_mUtils_mViews_mCore_Compile._IView__>> _775_open = (_774_valueOrError0).Extract();
        JSON_mUtils_mCursors_Compile._ISplit<Dafny.ISequence<JSON_mGrammar_Compile._ISuffixed<JSON_mGrammar_Compile._IValue, JSON_mUtils_mViews_mCore_Compile._IView__>>> _776_elems = JSON_mUtils_mCursors_Compile.Split<Dafny.ISequence<JSON_mGrammar_Compile._ISuffixed<JSON_mGrammar_Compile._IValue, JSON_mUtils_mViews_mCore_Compile._IView__>>>.create(Dafny.Sequence<JSON_mGrammar_Compile._ISuffixed<JSON_mGrammar_Compile._IValue, JSON_mUtils_mViews_mCore_Compile._IView__>>.FromElements(), (_775_open).dtor_cs);
        if ((((_775_open).dtor_cs).Peek()) == ((short)(JSON_mZeroCopy_mDeserializer_mArrayParams_Compile.__default.CLOSE))) {
          Wrappers_Compile._IResult<JSON_mUtils_mCursors_Compile._ISplit<JSON_mGrammar_Compile._IStructural<JSON_mUtils_mViews_mCore_Compile._IView__>>, JSON_mUtils_mCursors_Compile._ICursorError<JSON_mErrors_Compile._IDeserializationError>> _777_valueOrError1 = JSON_mZeroCopy_mDeserializer_mCore_Compile.__default.Structural<JSON_mUtils_mViews_mCore_Compile._IView__>((_775_open).dtor_cs, JSON_mUtils_mParsers_Compile.Parser__<JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mErrors_Compile._IDeserializationError>.create(JSON_mZeroCopy_mDeserializer_mArrays_Compile.__default.Close));
          if ((_777_valueOrError1).IsFailure()) {
            return (_777_valueOrError1).PropagateFailure<JSON_mUtils_mCursors_Compile._ISplit<JSON_mGrammar_Compile._IBracketed<JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mGrammar_Compile._IValue, JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mUtils_mViews_mCore_Compile._IView__>>>();
          } else {
            JSON_mUtils_mCursors_Compile._ISplit<JSON_mGrammar_Compile._IStructural<JSON_mUtils_mViews_mCore_Compile._IView__>> _778_close = (_777_valueOrError1).Extract();
            return Wrappers_Compile.Result<JSON_mUtils_mCursors_Compile._ISplit<JSON_mGrammar_Compile._IBracketed<JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mGrammar_Compile._IValue, JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mUtils_mViews_mCore_Compile._IView__>>, JSON_mUtils_mCursors_Compile._ICursorError<JSON_mErrors_Compile._IDeserializationError>>.create_Success(JSON_mZeroCopy_mDeserializer_mArrays_Compile.__default.BracketedFromParts(_775_open, _776_elems, _778_close));
          }
        } else {
          return JSON_mZeroCopy_mDeserializer_mArrays_Compile.__default.Elements(json, _775_open, _776_elems);
        }
      }
    }
    public static byte SEPARATOR { get {
      return (byte)(',');
    } }
  }

  public partial class jopen {
    private static readonly JSON_mUtils_mViews_mCore_Compile._IView__ Witness = JSON_mUtils_mViews_mCore_Compile.View__.OfBytes(Dafny.Sequence<byte>.FromElements(JSON_mZeroCopy_mDeserializer_mArrayParams_Compile.__default.OPEN));
    public static JSON_mUtils_mViews_mCore_Compile._IView__ Default() {
      return Witness;
    }
    private static readonly Dafny.TypeDescriptor<JSON_mUtils_mViews_mCore_Compile._IView__> _TYPE = new Dafny.TypeDescriptor<JSON_mUtils_mViews_mCore_Compile._IView__>(JSON_mZeroCopy_mDeserializer_mArrays_Compile.jopen.Default());
    public static Dafny.TypeDescriptor<JSON_mUtils_mViews_mCore_Compile._IView__> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class jclose {
    private static readonly JSON_mUtils_mViews_mCore_Compile._IView__ Witness = JSON_mUtils_mViews_mCore_Compile.View__.OfBytes(Dafny.Sequence<byte>.FromElements(JSON_mZeroCopy_mDeserializer_mArrayParams_Compile.__default.CLOSE));
    public static JSON_mUtils_mViews_mCore_Compile._IView__ Default() {
      return Witness;
    }
    private static readonly Dafny.TypeDescriptor<JSON_mUtils_mViews_mCore_Compile._IView__> _TYPE = new Dafny.TypeDescriptor<JSON_mUtils_mViews_mCore_Compile._IView__>(JSON_mZeroCopy_mDeserializer_mArrays_Compile.jclose.Default());
    public static Dafny.TypeDescriptor<JSON_mUtils_mViews_mCore_Compile._IView__> _TypeDescriptor() {
      return _TYPE;
    }
  }
} // end of namespace JSON_mZeroCopy_mDeserializer_mArrays_Compile
namespace JSON_mZeroCopy_mDeserializer_mConstants_Compile {

  public partial class __default {
    public static Wrappers_Compile._IResult<JSON_mUtils_mCursors_Compile._ISplit<JSON_mUtils_mViews_mCore_Compile._IView__>, JSON_mUtils_mCursors_Compile._ICursorError<JSON_mErrors_Compile._IDeserializationError>> Constant(JSON_mUtils_mCursors_Compile._ICursor__ cs, Dafny.ISequence<byte> expected)
    {
      Wrappers_Compile._IResult<JSON_mUtils_mCursors_Compile._ICursor__, JSON_mUtils_mCursors_Compile._ICursorError<JSON_mErrors_Compile._IDeserializationError>> _779_valueOrError0 = (cs).AssertBytes<JSON_mErrors_Compile._IDeserializationError>(expected, 0U);
      if ((_779_valueOrError0).IsFailure()) {
        return (_779_valueOrError0).PropagateFailure<JSON_mUtils_mCursors_Compile._ISplit<JSON_mUtils_mViews_mCore_Compile._IView__>>();
      } else {
        JSON_mUtils_mCursors_Compile._ICursor__ _780_cs = (_779_valueOrError0).Extract();
        return Wrappers_Compile.Result<JSON_mUtils_mCursors_Compile._ISplit<JSON_mUtils_mViews_mCore_Compile._IView__>, JSON_mUtils_mCursors_Compile._ICursorError<JSON_mErrors_Compile._IDeserializationError>>.create_Success((_780_cs).Split());
      }
    }
  }
} // end of namespace JSON_mZeroCopy_mDeserializer_mConstants_Compile
namespace JSON_mZeroCopy_mDeserializer_mValues_Compile {

  public partial class __default {
    public static Wrappers_Compile._IResult<JSON_mUtils_mCursors_Compile._ISplit<JSON_mGrammar_Compile._IValue>, JSON_mUtils_mCursors_Compile._ICursorError<JSON_mErrors_Compile._IDeserializationError>> Value(JSON_mUtils_mCursors_Compile._ICursor__ cs) {
      short _781_c = (cs).Peek();
      if ((_781_c) == ((short)('{'))) {
        Wrappers_Compile._IResult<JSON_mUtils_mCursors_Compile._ISplit<JSON_mGrammar_Compile._IBracketed<JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mGrammar_Compile._IjKeyValue, JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mUtils_mViews_mCore_Compile._IView__>>, JSON_mUtils_mCursors_Compile._ICursorError<JSON_mErrors_Compile._IDeserializationError>> _782_valueOrError0 = JSON_mZeroCopy_mDeserializer_mObjects_Compile.__default.Object(cs, JSON_mZeroCopy_mDeserializer_mValues_Compile.__default.ValueParser(cs));
        if ((_782_valueOrError0).IsFailure()) {
          return (_782_valueOrError0).PropagateFailure<JSON_mUtils_mCursors_Compile._ISplit<JSON_mGrammar_Compile._IValue>>();
        } else {
          JSON_mUtils_mCursors_Compile._ISplit<JSON_mGrammar_Compile._IBracketed<JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mGrammar_Compile._IjKeyValue, JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mUtils_mViews_mCore_Compile._IView__>> _let_tmp_rhs16 = (_782_valueOrError0).Extract();
          JSON_mGrammar_Compile._IBracketed<JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mGrammar_Compile._IjKeyValue, JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mUtils_mViews_mCore_Compile._IView__> _783_obj = _let_tmp_rhs16.dtor_t;
          JSON_mUtils_mCursors_Compile._ICursor__ _784_cs_k = _let_tmp_rhs16.dtor_cs;
          JSON_mGrammar_Compile._IValue _785_v = JSON_mGrammar_Compile.Value.create_Object(_783_obj);
          JSON_mUtils_mCursors_Compile._ISplit<JSON_mGrammar_Compile._IValue> _786_sp = JSON_mUtils_mCursors_Compile.Split<JSON_mGrammar_Compile._IValue>.create(_785_v, _784_cs_k);
          return Wrappers_Compile.Result<JSON_mUtils_mCursors_Compile._ISplit<JSON_mGrammar_Compile._IValue>, JSON_mUtils_mCursors_Compile._ICursorError<JSON_mErrors_Compile._IDeserializationError>>.create_Success(_786_sp);
        }
      } else if ((_781_c) == ((short)('['))) {
        Wrappers_Compile._IResult<JSON_mUtils_mCursors_Compile._ISplit<JSON_mGrammar_Compile._IBracketed<JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mGrammar_Compile._IValue, JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mUtils_mViews_mCore_Compile._IView__>>, JSON_mUtils_mCursors_Compile._ICursorError<JSON_mErrors_Compile._IDeserializationError>> _787_valueOrError1 = JSON_mZeroCopy_mDeserializer_mArrays_Compile.__default.Array(cs, JSON_mZeroCopy_mDeserializer_mValues_Compile.__default.ValueParser(cs));
        if ((_787_valueOrError1).IsFailure()) {
          return (_787_valueOrError1).PropagateFailure<JSON_mUtils_mCursors_Compile._ISplit<JSON_mGrammar_Compile._IValue>>();
        } else {
          JSON_mUtils_mCursors_Compile._ISplit<JSON_mGrammar_Compile._IBracketed<JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mGrammar_Compile._IValue, JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mUtils_mViews_mCore_Compile._IView__>> _let_tmp_rhs17 = (_787_valueOrError1).Extract();
          JSON_mGrammar_Compile._IBracketed<JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mGrammar_Compile._IValue, JSON_mUtils_mViews_mCore_Compile._IView__, JSON_mUtils_mViews_mCore_Compile._IView__> _788_arr = _let_tmp_rhs17.dtor_t;
          JSON_mUtils_mCursors_Compile._ICursor__ _789_cs_k = _let_tmp_rhs17.dtor_cs;
          JSON_mGrammar_Compile._IValue _790_v = JSON_mGrammar_Compile.Value.create_Array(_788_arr);
          JSON_mUtils_mCursors_Compile._ISplit<JSON_mGrammar_Compile._IValue> _791_sp = JSON_mUtils_mCursors_Compile.Split<JSON_mGrammar_Compile._IValue>.create(_790_v, _789_cs_k);
          return Wrappers_Compile.Result<JSON_mUtils_mCursors_Compile._ISplit<JSON_mGrammar_Compile._IValue>, JSON_mUtils_mCursors_Compile._ICursorError<JSON_mErrors_Compile._IDeserializationError>>.create_Success(_791_sp);
        }
      } else if ((_781_c) == ((short)('\"'))) {
        Wrappers_Compile._IResult<JSON_mUtils_mCursors_Compile._ISplit<JSON_mGrammar_Compile._Ijstring>, JSON_mUtils_mCursors_Compile._ICursorError<JSON_mErrors_Compile._IDeserializationError>> _792_valueOrError2 = JSON_mZeroCopy_mDeserializer_mStrings_Compile.__default.String(cs);
        if ((_792_valueOrError2).IsFailure()) {
          return (_792_valueOrError2).PropagateFailure<JSON_mUtils_mCursors_Compile._ISplit<JSON_mGrammar_Compile._IValue>>();
        } else {
          JSON_mUtils_mCursors_Compile._ISplit<JSON_mGrammar_Compile._Ijstring> _let_tmp_rhs18 = (_792_valueOrError2).Extract();
          JSON_mGrammar_Compile._Ijstring _793_str = _let_tmp_rhs18.dtor_t;
          JSON_mUtils_mCursors_Compile._ICursor__ _794_cs = _let_tmp_rhs18.dtor_cs;
          return Wrappers_Compile.Result<JSON_mUtils_mCursors_Compile._ISplit<JSON_mGrammar_Compile._IValue>, JSON_mUtils_mCursors_Compile._ICursorError<JSON_mErrors_Compile._IDeserializationError>>.create_Success(JSON_mUtils_mCursors_Compile.Split<JSON_mGrammar_Compile._IValue>.create(JSON_mGrammar_Compile.Value.create_String(_793_str), _794_cs));
        }
      } else if ((_781_c) == ((short)('t'))) {
        Wrappers_Compile._IResult<JSON_mUtils_mCursors_Compile._ISplit<JSON_mUtils_mViews_mCore_Compile._IView__>, JSON_mUtils_mCursors_Compile._ICursorError<JSON_mErrors_Compile._IDeserializationError>> _795_valueOrError3 = JSON_mZeroCopy_mDeserializer_mConstants_Compile.__default.Constant(cs, JSON_mGrammar_Compile.__default.TRUE);
        if ((_795_valueOrError3).IsFailure()) {
          return (_795_valueOrError3).PropagateFailure<JSON_mUtils_mCursors_Compile._ISplit<JSON_mGrammar_Compile._IValue>>();
        } else {
          JSON_mUtils_mCursors_Compile._ISplit<JSON_mUtils_mViews_mCore_Compile._IView__> _let_tmp_rhs19 = (_795_valueOrError3).Extract();
          JSON_mUtils_mViews_mCore_Compile._IView__ _796_cst = _let_tmp_rhs19.dtor_t;
          JSON_mUtils_mCursors_Compile._ICursor__ _797_cs = _let_tmp_rhs19.dtor_cs;
          return Wrappers_Compile.Result<JSON_mUtils_mCursors_Compile._ISplit<JSON_mGrammar_Compile._IValue>, JSON_mUtils_mCursors_Compile._ICursorError<JSON_mErrors_Compile._IDeserializationError>>.create_Success(JSON_mUtils_mCursors_Compile.Split<JSON_mGrammar_Compile._IValue>.create(JSON_mGrammar_Compile.Value.create_Bool(_796_cst), _797_cs));
        }
      } else if ((_781_c) == ((short)('f'))) {
        Wrappers_Compile._IResult<JSON_mUtils_mCursors_Compile._ISplit<JSON_mUtils_mViews_mCore_Compile._IView__>, JSON_mUtils_mCursors_Compile._ICursorError<JSON_mErrors_Compile._IDeserializationError>> _798_valueOrError4 = JSON_mZeroCopy_mDeserializer_mConstants_Compile.__default.Constant(cs, JSON_mGrammar_Compile.__default.FALSE);
        if ((_798_valueOrError4).IsFailure()) {
          return (_798_valueOrError4).PropagateFailure<JSON_mUtils_mCursors_Compile._ISplit<JSON_mGrammar_Compile._IValue>>();
        } else {
          JSON_mUtils_mCursors_Compile._ISplit<JSON_mUtils_mViews_mCore_Compile._IView__> _let_tmp_rhs20 = (_798_valueOrError4).Extract();
          JSON_mUtils_mViews_mCore_Compile._IView__ _799_cst = _let_tmp_rhs20.dtor_t;
          JSON_mUtils_mCursors_Compile._ICursor__ _800_cs = _let_tmp_rhs20.dtor_cs;
          return Wrappers_Compile.Result<JSON_mUtils_mCursors_Compile._ISplit<JSON_mGrammar_Compile._IValue>, JSON_mUtils_mCursors_Compile._ICursorError<JSON_mErrors_Compile._IDeserializationError>>.create_Success(JSON_mUtils_mCursors_Compile.Split<JSON_mGrammar_Compile._IValue>.create(JSON_mGrammar_Compile.Value.create_Bool(_799_cst), _800_cs));
        }
      } else if ((_781_c) == ((short)('n'))) {
        Wrappers_Compile._IResult<JSON_mUtils_mCursors_Compile._ISplit<JSON_mUtils_mViews_mCore_Compile._IView__>, JSON_mUtils_mCursors_Compile._ICursorError<JSON_mErrors_Compile._IDeserializationError>> _801_valueOrError5 = JSON_mZeroCopy_mDeserializer_mConstants_Compile.__default.Constant(cs, JSON_mGrammar_Compile.__default.NULL);
        if ((_801_valueOrError5).IsFailure()) {
          return (_801_valueOrError5).PropagateFailure<JSON_mUtils_mCursors_Compile._ISplit<JSON_mGrammar_Compile._IValue>>();
        } else {
          JSON_mUtils_mCursors_Compile._ISplit<JSON_mUtils_mViews_mCore_Compile._IView__> _let_tmp_rhs21 = (_801_valueOrError5).Extract();
          JSON_mUtils_mViews_mCore_Compile._IView__ _802_cst = _let_tmp_rhs21.dtor_t;
          JSON_mUtils_mCursors_Compile._ICursor__ _803_cs = _let_tmp_rhs21.dtor_cs;
          return Wrappers_Compile.Result<JSON_mUtils_mCursors_Compile._ISplit<JSON_mGrammar_Compile._IValue>, JSON_mUtils_mCursors_Compile._ICursorError<JSON_mErrors_Compile._IDeserializationError>>.create_Success(JSON_mUtils_mCursors_Compile.Split<JSON_mGrammar_Compile._IValue>.create(JSON_mGrammar_Compile.Value.create_Null(_802_cst), _803_cs));
        }
      } else {
        Wrappers_Compile._IResult<JSON_mUtils_mCursors_Compile._ISplit<JSON_mGrammar_Compile._Ijnumber>, JSON_mUtils_mCursors_Compile._ICursorError<JSON_mErrors_Compile._IDeserializationError>> _804_valueOrError6 = JSON_mZeroCopy_mDeserializer_mNumbers_Compile.__default.Number(cs);
        if ((_804_valueOrError6).IsFailure()) {
          return (_804_valueOrError6).PropagateFailure<JSON_mUtils_mCursors_Compile._ISplit<JSON_mGrammar_Compile._IValue>>();
        } else {
          JSON_mUtils_mCursors_Compile._ISplit<JSON_mGrammar_Compile._Ijnumber> _let_tmp_rhs22 = (_804_valueOrError6).Extract();
          JSON_mGrammar_Compile._Ijnumber _805_num = _let_tmp_rhs22.dtor_t;
          JSON_mUtils_mCursors_Compile._ICursor__ _806_cs_k = _let_tmp_rhs22.dtor_cs;
          JSON_mGrammar_Compile._IValue _807_v = JSON_mGrammar_Compile.Value.create_Number(_805_num);
          JSON_mUtils_mCursors_Compile._ISplit<JSON_mGrammar_Compile._IValue> _808_sp = JSON_mUtils_mCursors_Compile.Split<JSON_mGrammar_Compile._IValue>.create(_807_v, _806_cs_k);
          return Wrappers_Compile.Result<JSON_mUtils_mCursors_Compile._ISplit<JSON_mGrammar_Compile._IValue>, JSON_mUtils_mCursors_Compile._ICursorError<JSON_mErrors_Compile._IDeserializationError>>.create_Success(_808_sp);
        }
      }
    }
    public static JSON_mUtils_mParsers_Compile._ISubParser__<JSON_mGrammar_Compile._IValue, JSON_mErrors_Compile._IDeserializationError> ValueParser(JSON_mUtils_mCursors_Compile._ICursor__ cs) {
      Func<JSON_mUtils_mCursors_Compile._ICursor__, bool> _809_pre = Dafny.Helpers.Id<Func<JSON_mUtils_mCursors_Compile._ICursor__, Func<JSON_mUtils_mCursors_Compile._ICursor__, bool>>>((_810_cs) => ((System.Func<JSON_mUtils_mCursors_Compile._ICursor__, bool>)((_811_ps_k) => {
        return ((_811_ps_k).Length()) < ((_810_cs).Length());
      })))(cs);
      Func<JSON_mUtils_mCursors_Compile._ICursor__, Wrappers_Compile._IResult<JSON_mUtils_mCursors_Compile._ISplit<JSON_mGrammar_Compile._IValue>, JSON_mUtils_mCursors_Compile._ICursorError<JSON_mErrors_Compile._IDeserializationError>>> _812_fn = Dafny.Helpers.Id<Func<Func<JSON_mUtils_mCursors_Compile._ICursor__, bool>, Func<JSON_mUtils_mCursors_Compile._ICursor__, Wrappers_Compile._IResult<JSON_mUtils_mCursors_Compile._ISplit<JSON_mGrammar_Compile._IValue>, JSON_mUtils_mCursors_Compile._ICursorError<JSON_mErrors_Compile._IDeserializationError>>>>>((_813_pre) => ((System.Func<JSON_mUtils_mCursors_Compile._ICursor__, Wrappers_Compile._IResult<JSON_mUtils_mCursors_Compile._ISplit<JSON_mGrammar_Compile._IValue>, JSON_mUtils_mCursors_Compile._ICursorError<JSON_mErrors_Compile._IDeserializationError>>>)((_814_ps_k) => {
        return JSON_mZeroCopy_mDeserializer_mValues_Compile.__default.Value(_814_ps_k);
      })))(_809_pre);
      return JSON_mUtils_mParsers_Compile.SubParser__<JSON_mGrammar_Compile._IValue, JSON_mErrors_Compile._IDeserializationError>.create(_812_fn);
    }
  }
} // end of namespace JSON_mZeroCopy_mDeserializer_mValues_Compile
namespace JSON_mZeroCopy_mDeserializer_mAPI_Compile {

  public partial class __default {
    public static JSON_mErrors_Compile._IDeserializationError LiftCursorError(JSON_mUtils_mCursors_Compile._ICursorError<JSON_mErrors_Compile._IDeserializationError> err) {
      JSON_mUtils_mCursors_Compile._ICursorError<JSON_mErrors_Compile._IDeserializationError> _source20 = err;
      if (_source20.is_EOF) {
        return JSON_mErrors_Compile.DeserializationError.create_ReachedEOF();
      } else if (_source20.is_ExpectingByte) {
        byte _815___mcc_h0 = _source20.dtor_expected;
        short _816___mcc_h1 = _source20.dtor_b;
        short _817_b = _816___mcc_h1;
        byte _818_expected = _815___mcc_h0;
        return JSON_mErrors_Compile.DeserializationError.create_ExpectingByte(_818_expected, _817_b);
      } else if (_source20.is_ExpectingAnyByte) {
        Dafny.ISequence<byte> _819___mcc_h2 = _source20.dtor_expected__sq;
        short _820___mcc_h3 = _source20.dtor_b;
        short _821_b = _820___mcc_h3;
        Dafny.ISequence<byte> _822_expected__sq = _819___mcc_h2;
        return JSON_mErrors_Compile.DeserializationError.create_ExpectingAnyByte(_822_expected__sq, _821_b);
      } else {
        JSON_mErrors_Compile._IDeserializationError _823___mcc_h4 = _source20.dtor_err;
        JSON_mErrors_Compile._IDeserializationError _824_err = _823___mcc_h4;
        return _824_err;
      }
    }
    public static Wrappers_Compile._IResult<JSON_mUtils_mCursors_Compile._ISplit<JSON_mGrammar_Compile._IStructural<JSON_mGrammar_Compile._IValue>>, JSON_mErrors_Compile._IDeserializationError> JSON(JSON_mUtils_mCursors_Compile._ICursor__ cs) {
      return Wrappers_Compile.Result<JSON_mUtils_mCursors_Compile._ISplit<JSON_mGrammar_Compile._IStructural<JSON_mGrammar_Compile._IValue>>, JSON_mUtils_mCursors_Compile._ICursorError<JSON_mErrors_Compile._IDeserializationError>>.MapFailure<JSON_mErrors_Compile._IDeserializationError>(JSON_mZeroCopy_mDeserializer_mCore_Compile.__default.Structural<JSON_mGrammar_Compile._IValue>(cs, JSON_mUtils_mParsers_Compile.Parser__<JSON_mGrammar_Compile._IValue, JSON_mErrors_Compile._IDeserializationError>.create(JSON_mZeroCopy_mDeserializer_mValues_Compile.__default.Value)), JSON_mZeroCopy_mDeserializer_mAPI_Compile.__default.LiftCursorError);
    }
    public static Wrappers_Compile._IResult<JSON_mGrammar_Compile._IStructural<JSON_mGrammar_Compile._IValue>, JSON_mErrors_Compile._IDeserializationError> Text(JSON_mUtils_mViews_mCore_Compile._IView__ v) {
      Wrappers_Compile._IResult<JSON_mUtils_mCursors_Compile._ISplit<JSON_mGrammar_Compile._IStructural<JSON_mGrammar_Compile._IValue>>, JSON_mErrors_Compile._IDeserializationError> _825_valueOrError0 = JSON_mZeroCopy_mDeserializer_mAPI_Compile.__default.JSON(JSON_mUtils_mCursors_Compile.Cursor__.OfView(v));
      if ((_825_valueOrError0).IsFailure()) {
        return (_825_valueOrError0).PropagateFailure<JSON_mGrammar_Compile._IStructural<JSON_mGrammar_Compile._IValue>>();
      } else {
        JSON_mUtils_mCursors_Compile._ISplit<JSON_mGrammar_Compile._IStructural<JSON_mGrammar_Compile._IValue>> _let_tmp_rhs23 = (_825_valueOrError0).Extract();
        JSON_mGrammar_Compile._IStructural<JSON_mGrammar_Compile._IValue> _826_text = _let_tmp_rhs23.dtor_t;
        JSON_mUtils_mCursors_Compile._ICursor__ _827_cs = _let_tmp_rhs23.dtor_cs;
        Wrappers_Compile._IOutcome<JSON_mErrors_Compile._IDeserializationError> _828_valueOrError1 = Wrappers_Compile.__default.Need<JSON_mErrors_Compile._IDeserializationError>((_827_cs).EOF_q, JSON_mErrors_Compile.DeserializationError.create_ExpectingEOF());
        if ((_828_valueOrError1).IsFailure()) {
          return (_828_valueOrError1).PropagateFailure<JSON_mGrammar_Compile._IStructural<JSON_mGrammar_Compile._IValue>>();
        } else {
          return Wrappers_Compile.Result<JSON_mGrammar_Compile._IStructural<JSON_mGrammar_Compile._IValue>, JSON_mErrors_Compile._IDeserializationError>.create_Success(_826_text);
        }
      }
    }
    public static Wrappers_Compile._IResult<JSON_mGrammar_Compile._IStructural<JSON_mGrammar_Compile._IValue>, JSON_mErrors_Compile._IDeserializationError> OfBytes(Dafny.ISequence<byte> bs) {
      Wrappers_Compile._IOutcome<JSON_mErrors_Compile._IDeserializationError> _829_valueOrError0 = Wrappers_Compile.__default.Need<JSON_mErrors_Compile._IDeserializationError>((new BigInteger((bs).Count)) < (BoundedInts_Compile.__default.TWO__TO__THE__32), JSON_mErrors_Compile.DeserializationError.create_IntOverflow());
      if ((_829_valueOrError0).IsFailure()) {
        return (_829_valueOrError0).PropagateFailure<JSON_mGrammar_Compile._IStructural<JSON_mGrammar_Compile._IValue>>();
      } else {
        return JSON_mZeroCopy_mDeserializer_mAPI_Compile.__default.Text(JSON_mUtils_mViews_mCore_Compile.View__.OfBytes(bs));
      }
    }
  }
} // end of namespace JSON_mZeroCopy_mDeserializer_mAPI_Compile
namespace JSON_mZeroCopy_mDeserializer_Compile {

} // end of namespace JSON_mZeroCopy_mDeserializer_Compile
namespace JSON_mZeroCopy_mAPI_Compile {

  public partial class __default {
    public static Wrappers_Compile._IResult<Dafny.ISequence<byte>, JSON_mErrors_Compile._ISerializationError> Serialize(JSON_mGrammar_Compile._IStructural<JSON_mGrammar_Compile._IValue> js) {
      return Wrappers_Compile.Result<Dafny.ISequence<byte>, JSON_mErrors_Compile._ISerializationError>.create_Success((JSON_mZeroCopy_mSerializer_Compile.__default.Text(js)).Bytes());
    }
    public static Wrappers_Compile._IResult<byte[], JSON_mErrors_Compile._ISerializationError> SerializeAlloc(JSON_mGrammar_Compile._IStructural<JSON_mGrammar_Compile._IValue> js)
    {
      Wrappers_Compile._IResult<byte[], JSON_mErrors_Compile._ISerializationError> bs = Wrappers_Compile.Result<byte[], JSON_mErrors_Compile._ISerializationError>.Default(new byte[0]);
      Wrappers_Compile._IResult<byte[], JSON_mErrors_Compile._ISerializationError> _out27;
      _out27 = JSON_mZeroCopy_mSerializer_Compile.__default.Serialize(js);
      bs = _out27;
      return bs;
    }
    public static Wrappers_Compile._IResult<uint, JSON_mErrors_Compile._ISerializationError> SerializeInto(JSON_mGrammar_Compile._IStructural<JSON_mGrammar_Compile._IValue> js, byte[] bs)
    {
      Wrappers_Compile._IResult<uint, JSON_mErrors_Compile._ISerializationError> len = Wrappers_Compile.Result<uint, JSON_mErrors_Compile._ISerializationError>.Default(0);
      Wrappers_Compile._IResult<uint, JSON_mErrors_Compile._ISerializationError> _out28;
      _out28 = JSON_mZeroCopy_mSerializer_Compile.__default.SerializeTo(js, bs);
      len = _out28;
      return len;
    }
    public static Wrappers_Compile._IResult<JSON_mGrammar_Compile._IStructural<JSON_mGrammar_Compile._IValue>, JSON_mErrors_Compile._IDeserializationError> Deserialize(Dafny.ISequence<byte> bs) {
      return JSON_mZeroCopy_mDeserializer_mAPI_Compile.__default.OfBytes(bs);
    }
  }
} // end of namespace JSON_mZeroCopy_mAPI_Compile
namespace JSON_mZeroCopy_Compile {

} // end of namespace JSON_mZeroCopy_Compile
namespace JSON_mAPI_Compile {

  public partial class __default {
    public static Wrappers_Compile._IResult<Dafny.ISequence<byte>, JSON_mErrors_Compile._ISerializationError> Serialize(JSON_mValues_Compile._IJSON js) {
      Wrappers_Compile._IResult<JSON_mGrammar_Compile._IStructural<JSON_mGrammar_Compile._IValue>, JSON_mErrors_Compile._ISerializationError> _830_valueOrError0 = JSON_mSerializer_Compile.__default.JSON(js);
      if ((_830_valueOrError0).IsFailure()) {
        return (_830_valueOrError0).PropagateFailure<Dafny.ISequence<byte>>();
      } else {
        JSON_mGrammar_Compile._IStructural<JSON_mGrammar_Compile._IValue> _831_js = (_830_valueOrError0).Extract();
        return JSON_mZeroCopy_mAPI_Compile.__default.Serialize(_831_js);
      }
    }
    public static Wrappers_Compile._IResult<byte[], JSON_mErrors_Compile._ISerializationError> SerializeAlloc(JSON_mValues_Compile._IJSON js)
    {
      Wrappers_Compile._IResult<byte[], JSON_mErrors_Compile._ISerializationError> bs = Wrappers_Compile.Result<byte[], JSON_mErrors_Compile._ISerializationError>.Default(new byte[0]);
      JSON_mGrammar_Compile._IStructural<JSON_mGrammar_Compile._IValue> _832_js;
      Wrappers_Compile._IResult<JSON_mGrammar_Compile._IStructural<JSON_mGrammar_Compile._IValue>, JSON_mErrors_Compile._ISerializationError> _833_valueOrError0 = Wrappers_Compile.Result<JSON_mGrammar_Compile._IStructural<JSON_mGrammar_Compile._IValue>, JSON_mErrors_Compile._ISerializationError>.Default(JSON_mGrammar_Compile.Structural<JSON_mGrammar_Compile._IValue>.Default(JSON_mGrammar_Compile.Value.Default()));
      _833_valueOrError0 = JSON_mSerializer_Compile.__default.JSON(js);
      if ((_833_valueOrError0).IsFailure()) {
        bs = (_833_valueOrError0).PropagateFailure<byte[]>();
        return bs;
      }
      _832_js = (_833_valueOrError0).Extract();
      Wrappers_Compile._IResult<byte[], JSON_mErrors_Compile._ISerializationError> _out29;
      _out29 = JSON_mZeroCopy_mAPI_Compile.__default.SerializeAlloc(_832_js);
      bs = _out29;
      return bs;
    }
    public static Wrappers_Compile._IResult<uint, JSON_mErrors_Compile._ISerializationError> SerializeInto(JSON_mValues_Compile._IJSON js, byte[] bs)
    {
      Wrappers_Compile._IResult<uint, JSON_mErrors_Compile._ISerializationError> len = Wrappers_Compile.Result<uint, JSON_mErrors_Compile._ISerializationError>.Default(0);
      JSON_mGrammar_Compile._IStructural<JSON_mGrammar_Compile._IValue> _834_js;
      Wrappers_Compile._IResult<JSON_mGrammar_Compile._IStructural<JSON_mGrammar_Compile._IValue>, JSON_mErrors_Compile._ISerializationError> _835_valueOrError0 = Wrappers_Compile.Result<JSON_mGrammar_Compile._IStructural<JSON_mGrammar_Compile._IValue>, JSON_mErrors_Compile._ISerializationError>.Default(JSON_mGrammar_Compile.Structural<JSON_mGrammar_Compile._IValue>.Default(JSON_mGrammar_Compile.Value.Default()));
      _835_valueOrError0 = JSON_mSerializer_Compile.__default.JSON(js);
      if ((_835_valueOrError0).IsFailure()) {
        len = (_835_valueOrError0).PropagateFailure<uint>();
        return len;
      }
      _834_js = (_835_valueOrError0).Extract();
      Wrappers_Compile._IResult<uint, JSON_mErrors_Compile._ISerializationError> _out30;
      _out30 = JSON_mZeroCopy_mAPI_Compile.__default.SerializeInto(_834_js, bs);
      len = _out30;
      return len;
    }
    public static Wrappers_Compile._IResult<JSON_mValues_Compile._IJSON, JSON_mErrors_Compile._IDeserializationError> Deserialize(Dafny.ISequence<byte> bs) {
      Wrappers_Compile._IResult<JSON_mGrammar_Compile._IStructural<JSON_mGrammar_Compile._IValue>, JSON_mErrors_Compile._IDeserializationError> _836_valueOrError0 = JSON_mZeroCopy_mAPI_Compile.__default.Deserialize(bs);
      if ((_836_valueOrError0).IsFailure()) {
        return (_836_valueOrError0).PropagateFailure<JSON_mValues_Compile._IJSON>();
      } else {
        JSON_mGrammar_Compile._IStructural<JSON_mGrammar_Compile._IValue> _837_js = (_836_valueOrError0).Extract();
        return JSON_mDeserializer_Compile.__default.JSON(_837_js);
      }
    }
  }
} // end of namespace JSON_mAPI_Compile
namespace JSON_Compile {

} // end of namespace JSON_Compile
namespace _module {

} // end of namespace _module
