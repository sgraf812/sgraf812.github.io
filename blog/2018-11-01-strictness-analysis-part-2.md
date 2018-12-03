---
title: All About Strictness Analysis (part 2)
tags: haskell strictness analysis
excerpt: TODO
---

Phew, quite some time passed since [part 1](http://fixpt.de/blog/2017-12-04-strictness-analysis-part-1.html)!
At the end of the last post, I made a promise to implement a strictness
analysis à la GHC with you, so enjoy!

<!--more-->

Since this is a literate Haskell file, we need to get the boring preamble out of the way.

```haskell
module Strictness (Expr (..), analyse) where
```

# Syntax

Compared to GHC's Core IR, we will have a simpler, untyped core calculus with
`let` bindings and if/then/else (instead of full-blown case expressions).

```haskell
data Expr
  = Var Name
  | App Expr Expr
  | Lam Name Expr
  | Let Bind Expr
  | If Expr Expr Expr
  deriving (Eq, Show)

type Name = String -- We assume names are unique!

data Bind
  = NonRec (Name, Expr)
  | Rec [(Name, Expr)]

type Program = [Bind]
```

Like in GHC, a program is just a list of top-level bindings. Also note that we
allow recursive bindings, which means the analysis will need to do
*fixed-point iteration* to reach a sound approximation of program semantics.

Next, we'll define the [lattice](https://en.wikipedia.org/wiki/Lattice_(order))
that will carry analysis information. Specifically, we will denote an
expression by its *strictness type*.

By the way, this blog post is so long because I tried to fit everything in one
literate Haskell file. Morally, this post should be split in two (or even three)
parts:
One discussing lattice ingredients and the other discussing how
to actually implement the analysis, just in case you felt
overwhelmed when looking at the scroll bar after scrolling the first time :).
I'll remind you to take a break later on.

# Lattice

For brevity, we will not include strictness on tuple components
(resp. record fields), because that would blow up this blog post too much.
But know that this approach extends straight-forwardly to records.

## Strictness signatures

Without nested strictness on product types, is there even anything useful
to analyse for? Yes, there is! We can still record if a variable was evaluated
at all. There's `const`, for example:

```haskell
const :: a -> b -> a
const a b = a
```

`const` is strict in its first argument and lazy in its second. That's easy
to see by evaluating `const undefined 5` and `const 5 undefined`.
So, in the language of GHC's demand signatures, we want to summarise `const` by
`<S,_><L,_>` (usage demands elided). GHC will use this strictness signature at
every call site of `const` to approximate the strictness behavior of `const`
without having to repeatedly analyse its right-hand side during analysis.

## Call demands

Fair enough, but what about a function like `twice`?

```haskell
twice :: (a -> a) -> a -> a
twice f x = f (f x)
```

Since we don't know anything about what strictness `f` puts on its argument,
we would summarise `twice` by the same signature as `const`.
But we really want a call like `twice (\x -> x + n) m` to be strict in `n`!
Just knowing that we are *head*-strict in the lambda argument doesn't cut it:
Evaluation will stop immediately since it's already in weak-head normal form.
On the other hand, we can't just interpret `S` as 'strict on the return value'
(what does that even mean?) to unleash strictness on `n` within the lambda
body. Since `const` has the same signature, we would also mark `n` strict in
a call like `const (\x -> x + m) 5`, which is incorrect:
``const (\x -> undefined) 5 `seq` 42 == 42``.

There's an unspoken assumption here: Strictness properties of some language
construct are always relative to an incoming *evaluation demand*, which is
head-strictness (the demand `seq` puts on its first argument) unless stated
otherwise. E.g., under the assumption of head-strictness, a call like
`const a b` is head-strict on `a` and lazy in `b`.

Note that `twice` differs from `const` in that it puts the *result*
of applying `f` to one argument under head-strictness. In GHC's strictness
language, this corresponds to a /call demand/ of `C(S)`. This is a strictly
stronger demand than `S`, the demand `const` puts on its first argument.

This has an important effect on our earlier `twice (\x -> x + n) m` example.
Knowing that the lambda expression is put under strictness demand `C(S)`,
it is suddenly possible for the analysis to look inside the lambda
abstraction, paying with the outer call component to discharge the remaining
`S` demand on the lambda body. In this way, the analysis detects that the
whole expression is strict in `n`.

At the same time, analysing `const (\x -> undefined) 5` assuming
head-strictness will only unleash a non-call demand `S` on the lambda,
which is not enough to meaningfully analyse its body under any other
strictness than `L`. This corresponds to our intuition that, relative
to a single evaluation (to head normal form) of our expression, the
lambda body may or may not be evaluated.

## Free variables

You may have noticed that we didn't really define yet what it means for
a variable to be strict in some expression in which it occurs free.

Traditionally, a function `f` is strict in (one of) its parameter if
it preserves nontermination, i.e. `f undefined = undefined`.
There's no way for the function to decide if its argument will blow up
when evaluated other than actually evaluating it, so it's equivalent
to say that if `f` is strict, then (either `f = const undefined` or) it
evaluates its argument on every possible execution path.

How can we extend this to our intuitive notion of strictness in a variable
that occurs free in some expression? We can just capture that free
variable with a lambda and apply our original definition. So, when we talk
about the strictness of `n` as it demanded in `twice (\x -> x + n) m`, we
are actually talking about strictness properties of the function
`\n -> twice (\x -> x + n) m`.

Our analysis will track free variables in an extra *environment*, mapping
`Name`s to the strictness demand they are put under.

## Putting everything together

Alright, so now we have everything in place to denote Haskell expressions
in terms of their strictness properties.

As discussed above, expressions, most prominently variables, can be put
under a certain `Strictness`, relative to an evaluation demand on their
surrounding expression:

```haskell
-- | Captures lower bounds on evaluation cardinality of some expression.
-- E.g.: Is this expression evaluated at least once? If so, what is the
-- maximum number of arguments it was surely applied to?
data Strictness
  = Lazy        -- ^ Evaluated lazily (possibly not evaluated at all)
  | Strict Int  -- ^ Evaluated strictly (at least once), called with n args
  | HyperStrict -- ^ Fully evaluated, a call with maximum arity

instance Show Strictness where
  show Lazy = "L"
  show (Strict 0) = "S"
  show (Strict n) = "C(" ++ show (Strict (n-1)) ++ ")"
  show HyperStrict = "B"
```haskell

The `Show` instance tries to adhere to GHC's syntax. You can see how call
demands `C(_)` and regular strictness `S` could be elegantly unified in this
formulation. I sneaked in another constructor, `HyperStrict`. You can think of
it as the strongest strictness possible. In our case, that corresponds to a call
with infinite arity.

Earlier, we were informally talking about how `S` is a *stronger* demand than
`L`. We can capture that meaning by providing an instance of `SemiJoinLattice`,
which consists of defining a *least upper bound* operator `\/` (also goes by
*join* or *supremum*):

```haskell
instance JoinSemiLattice Strictness where
  Lazy \/ _ = Lazy
  _ \/ Lazy = Lazy
  HyperStrict \/ s = s
  s \/ HyperStrict = s
  Strict n \/ Strict m = Strict (min n m)
```

On a total `Ord` like `Strictness`, this is just a fancy name for `max`.
"Hold on,", I hear you complain, "I thought `HyperStrict` was the greatest element?!
This is all backwards!".
<details>
  <summary>Answer with a quick detour on denotational semantics and static program analysis</summary>

  Well, it's customary in denotational semantics to
  assume that the bottom element of the abstract lattice corresponds to
  nontermination. So much, that Haskellers typically use the two terms
  'bottom' and 'nontermination' interchangeably.

  Now think of static program analysis, where every program point that
  evaluates some expression will put semantic constraints on its denotation.
  A conservative estimate of program semantics must be an upper bound to
  the all constraints at that program point over every possible program path.

  Consider the contrived example ``if b then f 1 else f `seq` 42``;
  each occurrence of `f` generates a semantic constraint on mutually exclusive
  code paths. While the first occurrence is a call with one argument, i.e.
  denoted by `Strict 1`, the second occurrence just puts `f` under a rather
  weak `Strict 0` (i.e. head-strict) constraint.

  What is the conservative estimate to strive for here? It's the join of
  `Strict 1` and `Strict 0`, so `Strict 0`! Generally speaking, as we
  discover more and more constraints `f` is put under, its denotation will
  climb up in the lattice. So, going up in the lattice means
  'more constrained'.

  Note that there is also precedent of turning the lattice
  upside down and denoting the least constrained element by top. This view is
  adopted in the [dragon book](https://en.wikipedia.org/wiki/Compilers:_Principles,_Techniques,_and_Tools),
  for example.

</details>

Clearly, the least (or, bottom) element of the lattice wrt. to the above
join operator is `HyperStrict`. This justifies the following instance:

```haskell
instance BoundedJoinSemiLattice Strictness where
  bottom = HyperStrict
```

There's some more boilerplate ahead for the dual semi lattice, defining
the *greatest lower bound* or *meet* or *infimum* operator and an
associated top element:

```haskell
instance MeetSemiLattice Strictness where
  HyperStrict /\ _ = HyperStrict
  _ /\ HyperStrict = HyperStrict
  Lazy /\ s = s
  s /\ Lazy = s
  Strict n /\ Strict m = Strict (max n m)

instance BoundedMeetSemiLattice Strictness where
  top = Lazy
```

Where would this be useful? If you squint a little and call the meet
operator 'both', you can denote sequential composition with this.

Consider ``if b `seq` True then b 42 else 1``. What strictness does
this place on `b`? Earlier, we used the join operator to combine
strictness from the `then` and `else` branch, corresponding to
*mutually exclusive* choices. That makes `Strict 1 \/ Lazy = Lazy`
for this example (note that `b` wasn't used at all in the `else`
branch!). Now, there's also an interesting condition to be analysed,
which puts `b` under `Strict 0` strictness. The condition will
certainly execute in the same evaluation as either branch.
Thus, we can pick the *stronger demand* of either the condition or
the join of the branches, which is `Strict 0 /\ Lazy = Strict 0`.

Great! That's the bounded lattice for denoting variables. We can
extend this denotation to expressions by means of an environment
tracking the strictness demands on its free variables upon being
put under a certain (i.e. head-strict) evaluation demand:

```haskell
type StrEnv = String -> Strictness

extendStrEnv :: Name -> Strictness -> StrEnv -> StrEnv
extendStrEnv n s env m
  | n == m    = s
  | otherwise = env m
```

Normally, we'd implement this as a `newtype`d `Map`, but here in
order to keep the post short we just alias to the pointwise
lattice on `String -> l` (i.e. ``(env1 \/ env2) n = env1 n\/ env2 n``).



By the way, the syntactic resemblence to boolean or is no accident: In fact,
the boolean algebra itself
[is a very special kind of lattice](https://en.wikipedia.org/wiki/Boolean_algebra_(structure)).

<sup id="a1"><a href="#f1">1</a></sup>.
<b id="f1">1</b> Note that there is also precedent of turning the lattice
upside down and denoting the least constrained element by top. This view is
adopted in the [dragon book](https://en.wikipedia.org/wiki/Compilers:_Principles,_Techniques,_and_Tools),
for example. <a href="#a1">↩</a>