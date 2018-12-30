---
title: All About Strictness Analysis (part 2)
tags: haskell strictness analysis
---

Welcome back! At the end of [part 1](/blog/2017-12-04-strictness-analysis-part-1.html)
from December 4<sup id="a1"><a href="#f1">1</a></sup>, I made a promise to implement
a strictness analysis à la GHC with you.

Why would this be useful? In the last post, I argued that a rough
understanding of how strictness analysis works helps to debug and identify the
actual causes of missed unboxing opportunities and fix them with minimal effort.

So here it is, enjoy!

<!--more-->

---

Since this is a literate markdown file, we need to get the boring preamble out of the way.

```haskell
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Strictness where

import Prelude hiding (const)
import Algebra.Lattice
import Control.Monad
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import qualified Data.Map.Merge.Strict as Map
import Data.Maybe (fromMaybe, mapMaybe)
import Debug.Trace
```

## Syntax

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
  deriving (Eq, Show)
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

## Lattice

For brevity, we will not include strictness on tuple components
(resp. record fields), because that would blow up this blog post too much.
But know that this approach extends straight-forwardly to records.

### Strictness signatures

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

### Call demands

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
language, this corresponds to a *call demand* of `S(S)`. This is a strictly
stronger demand than `S`, the demand `const` puts on its first argument.

This has an important effect on our earlier `twice (\x -> x + n) m` example.
Knowing that the lambda expression is put under strictness demand `S(S)`,
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

### Free variables

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

Now might be a good time to take a short break (think part 2½). Or just keep
reading while the above discussion is still fresh in your mind.

### Putting the lattice together

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
  deriving Eq

instance Show Strictness where
  show Lazy = "L"
  show (Strict 0) = "S"
  show (Strict n) = "S(" ++ show (Strict (n-1)) ++ ")"
  show HyperStrict = "B"
```

The `Show` instance tries to adhere to GHC's syntax. You can see how call
demands `S(_)` and regular strictness `S` could be elegantly unified in this
formulation. I snuck in another constructor, `HyperStrict`. You can think of
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

There's some more boilerplate ahead for the dual semilattice, defining
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

By the way, the syntactic resemblence to boolean operators is no
accident: In fact, the boolean algebra itself
[is a very special kind of lattice](https://en.wikipedia.org/wiki/Boolean_algebra_(structure)).

Where would this be useful? If you squint a little and call the meet
operator 'both' (for now), you can denote sequential composition with this.

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
-- | A total map (a /function/) from @k@ to @v@ with useful
-- lattice instances.
data TotalMap k v
  = TotalMap
  { def :: !v
  , points :: !(Map k v)
  } deriving (Eq, Show)

lookupTM :: Ord k => k -> TotalMap k v -> v
insertTM :: (Ord k, Eq v) => k -> v -> TotalMap k v -> TotalMap k v
deleteTM :: Ord k => k -> TotalMap k v -> TotalMap k v

type StrEnv = TotalMap Name Strictness
```

Such a `StrEnv` is just a total map from `Name`s to `Strictness`.
We can just use its point-wise lattice instance and be done with it.
<details>
  <summary>Boring implementations and lattice instances</summary>

```haskell
lookupTM n env =
  fromMaybe (def env) (Map.lookup n (points env))

insertTM n s env
  | s == def env = env { points = Map.delete n (points env) }
  | otherwise    = env { points = Map.insert n s (points env) }

deleteTM n env =
  env { points = Map.delete n (points env) }

joinOrMeet :: (Eq v, Ord k) => (v -> v -> v) -> TotalMap k v -> TotalMap k v -> TotalMap k v
joinOrMeet (/\/) (TotalMap def1 ps1) (TotalMap def2 ps2) = TotalMap def ps
  where
    def = def1 /\/ def2
    filterMaybe f a = a <$ guard (f a)
    mmc f = Map.mapMaybeMissing (\_ -> filterMaybe (/= def) . f)
    zmmc f = Map.zipWithMaybeMatched (\_ a -> filterMaybe (/= def) . f a)
    ps = Map.merge (mmc (/\/ def2)) (mmc (def1 /\/)) (zmmc (/\/)) ps1 ps2

instance (Ord k, Eq v, JoinSemiLattice v) => JoinSemiLattice (TotalMap k v) where
  (\/) = joinOrMeet (\/)

instance (Ord k, Eq v, BoundedJoinSemiLattice v) => BoundedJoinSemiLattice (TotalMap k v) where
  bottom = TotalMap bottom Map.empty

instance (Ord k, Eq v, MeetSemiLattice v) => MeetSemiLattice (TotalMap k v) where
  (/\) = joinOrMeet (/\)

instance (Ord k, Eq v, BoundedMeetSemiLattice v) => BoundedMeetSemiLattice (TotalMap k v) where
  top = TotalMap top Map.empty
```

</details>

This is enough vocabulary to analyse simple expressions. But, as
discussed above, we need argument strictness to express how a
function or lambda uses its arguments. So here we go:

```haskell
data ArgStr
  = BottomArgStr
  | TopArgStr
  | ConsArgStr Strictness ArgStr
  deriving Eq

instance Show ArgStr where
  show BottomArgStr = "B,B.."
  show TopArgStr = "L,L.."
  show (ConsArgStr s argStr) = show s ++ "," ++ show argStr

instance JoinSemiLattice ArgStr where
  BottomArgStr \/ s = s
  s \/ BottomArgStr = s
  TopArgStr \/ _ = TopArgStr
  _ \/ TopArgStr = TopArgStr
  (ConsArgStr s1 a1) \/ (ConsArgStr s2 a2) = ConsArgStr (s1 \/ s2) (a1 \/ a2)

instance BoundedJoinSemiLattice ArgStr where
  bottom = BottomArgStr

-- | This instance doesn't make a lot of sense semantically,
-- but it's the dual to the 'JoinSemiLattice' instance.
-- We mostly need this for 'top'.
instance MeetSemiLattice ArgStr where
  BottomArgStr /\ _ = BottomArgStr
  _ /\ BottomArgStr = BottomArgStr
  TopArgStr /\ s = s
  s /\ TopArgStr = s
  (ConsArgStr s1 a1) /\ (ConsArgStr s2 a2) = ConsArgStr (s1 /\ s2) (a1 /\ a2)

instance BoundedMeetSemiLattice ArgStr where
  top = TopArgStr

consArgStr :: Strictness -> ArgStr -> ArgStr
consArgStr Lazy TopArgStr           = TopArgStr
consArgStr HyperStrict BottomArgStr = BottomArgStr
consArgStr s a                      = ConsArgStr s a

unconsArgStr :: ArgStr -> (Strictness, ArgStr)
unconsArgStr BottomArgStr     = (bottom, BottomArgStr)
unconsArgStr TopArgStr        = (top, TopArgStr)
unconsArgStr (ConsArgStr s a) = (s, a)
```

Within this framework, a function like `error` would have strictness signature
`ConsArgStr Lazy BottomArgStr`, expressing the fact that when it's applied to
one argument, it will not necessarily evaluate that argument, but will lead to
an exception (which is the same as divergence, semantically speaking) if the call
expression would be evaluated. On the other hand, a lambda like `\f -> f a` would
be denoted by an argument strictness like `ConsArgStr (Strict 1) TopArgStr`.
What about `a`? That's tracked in the strictness environment, the other major
component of an expression's strictness type:

```haskell
data StrType
  = StrType
  { fvs  :: !StrEnv
  , args :: !ArgStr
  } deriving (Eq, Show)

instance JoinSemiLattice StrType where
  StrType fvs1 args1 \/ StrType fvs2 args2 =
    StrType (fvs1 \/ fvs2) (args1 \/ args2)

instance BoundedJoinSemiLattice StrType where
  bottom = StrType bottom bottom

-- | This instance doesn't make a lot of sense semantically,
-- but it's the dual to the 'JoinSemiLattice' instance.
-- We mostly need this for 'top'.
instance MeetSemiLattice StrType where
  StrType fvs1 args1 /\ StrType fvs2 args2 =
    StrType (fvs1 /\ fvs2) (args1 /\ args2)

instance BoundedMeetSemiLattice StrType where
  top = StrType top top

-- | This will be used instead of '(/\)' for sequential composition.
-- It's right biased, meaning that it will return the
-- argument strictness of the right argument.
bothStrType :: StrType -> StrType -> StrType
bothStrType (StrType fvs1 _) (StrType fvs2 args2) =
  StrType (fvs1 /\ fvs2) args2
  
unitStrType :: Name -> Strictness -> StrType
unitStrType n s = StrType (insertTM n s top) top

overFVs :: (StrEnv -> (a, StrEnv)) -> StrType -> (a, StrType)
overFVs f ty =
  let (a, fvs') = f (fvs ty)
  in (a, ty { fvs = fvs' })

peelFV :: Name -> StrType -> (Strictness, StrType)
peelFV n = overFVs $ \fvs ->
  (lookupTM n fvs, deleteTM n fvs)

modifyFVs :: (StrEnv -> StrEnv) -> StrType -> StrType
modifyFVs f = snd . overFVs (\a -> ((), f a))

deleteFV :: Name -> StrType -> StrType
deleteFV = modifyFVs . deleteTM

overArgs :: (ArgStr -> (a, ArgStr)) -> StrType -> (a, StrType)
overArgs f ty =
  let (a, args') = f (args ty)
  in (a, ty { args = args' })

modifyArgs :: (ArgStr -> ArgStr) -> StrType -> StrType
modifyArgs f = snd . overArgs (\a -> ((), f a))
```

So, strictness environment for free variables, argument strictness for
arguments. A last ingredient is an environment that will carry
strictness signatures for functions we analysed before:

```haskell
type Arity = Int
type SigEnv = Map Name (Arity, StrType)
```

Any strictness signature is only valid when a certain number of incoming
arguments is reached. We store this *arity* (as in unary, binary, etc.)
alongside the strictness signature. Generally, assuming a higher arity can lead
to more precise strictness signatures, but applies to less call sites.
GHC will only analyse each function once and assume an incoming strictness
demand correspond to manifest arity of the function, e.g. the number of
top-level lambdas in the RHS of the function's definition.

```haskell
-- | Counts the number of top-level lambdas.
manifestArity :: Expr -> Arity
manifestArity (Lam _ e) = 1 + manifestArity e
manifestArity _ = 0
```

That's it for the lattice! Have a break and enter part 3...

## Analysis

Let's define the main analysis function for our core calculus:

```haskell
analyse :: Expr -> StrType
```

We analyse an expression to find out what strictness it puts its free
variables under if put under head-demand:

```haskell
analyse = expr Map.empty 0

expr :: SigEnv -> Arity -> Expr -> StrType
expr sigs incomingArity = \case
  If b t e ->
    expr sigs 0 b `bothStrType`
      (expr sigs incomingArity t \/ expr sigs incomingArity e)
```

`analyse` immediately delegates to a more complicated auxiliary function.
We'll first look at the `If` case here: `If` will sequentially combine
('both') the analysis results from analysing the condition under incoming
arity 0 with the result of joining the analysis results of both branches
with the arity that came in from outside. Very much what we would expect
after our reasoning above!

```haskell
  App f a ->
    let
      fTy = expr sigs (incomingArity + 1) f
      (argStr, fTy') = overArgs unconsArgStr fTy
      aTy =
        case argStr of
          -- bottom = unbounded arity, only possibly constrained by the type
          -- of `a`, which we don't look at here.
          HyperStrict -> expr sigs maxBound a
          Strict n -> expr sigs n a
          -- `a` is possibly not evaluated at all, so nothing to see there
          Lazy -> top
    in aTy `bothStrType` fTy'
```

In an application, the head will be analysed with an incremented incoming arity,
while the argument is only evaluated if it was put under a strict context.
This is determined by examining the strictness type of analysing `f`.

The resulting types are sequentially combined ('both').
Note that `bothStrType` is right-biased and will pass on the argument
strictness from `fTy'`, which is exactly what we want. This will get clearer
once we examine the variable case.

```haskell
  Lam n body ->
    let
      bodyTy
        | incomingArity <= 0 = top
        | otherwise = expr sigs (incomingArity - 1) body
      -- normally, we would also store the strictness of n in the syntax tree
      -- or in a separate map, but we are only interested in free variables
      -- here for simplicity.
      (str, bodyTy') = peelFV n bodyTy
    in modifyArgs (consArgStr str) bodyTy'
```

This is somewhat dual to the application case. Lambdas 'eat' arity, so when we run
out of arity to feed it, we are not allowed to use analysis results from the body.
The only sensible thing to assume is a `top` strictness type in that case.

The call to `peelFV` will abstract out the strictness on the argument and we finally
cons that strictness onto the argument strictness of the lambda body's strictness
type. Consider what happens for an expression like `\f -> f a`: The lambda body
puts its free variable `f` under strictness `Strict 1`, so when we abstract over
`f`, we remove it from `fvs` and cons it to the lambdas argument strictness instead.

```haskell
  Var n ->
    let sig = fromMaybe top $ do
          (arity, sig) <- Map.lookup n sigs
          guard (arity <= incomingArity)
          pure sig
    in bothStrType (unitStrType n (Strict incomingArity)) sig
```

The variable case will try to look up a signature in the signature environment,
check for its compatibility with the incoming arity and fall back to `top`
if any of the guards fail. The resulting signature is combined with
a unit strictness type just for this particular call site.

A call to `const` with two arguments (so `arity == 2` when we hit the variable)
would pass the arity check and return the `<S,_><L,_>` (resp. `S,L,..` in our
syntax) signature from above. The application case at any call site would then
unleash the proper argument strictness on the concrete argument expressions.

What remains is handling let-bindings. Let's look at the non-recursive case first:

```haskell
  Let (NonRec (name, rhs)) body ->
    let
      arity = manifestArity rhs
      rhsTy = expr sigs arity rhs
      sigs' = Map.insert name (arity, rhsTy) sigs
      bodyTy = expr sigs' incomingArity body
      -- Normally, we would store how 'name' was used in the body somewhere
      bodyTy' = deleteFV name bodyTy
    in bodyTy'
```

Even without recursion, this is quite involved. First, we analyse the RHS
assuming a call with manifest arity. The resulting strictness type is then inserted
into the signature environment for the appropriate arity. The body is analysed
with this new signature environment. As `rhsTy` is unleashed at call sites through
the `Var` case, there is no need to `bothStrType` the resulting `bodyTy'` with
`rhsTy` (and would even be wrong, consider the case where the binding is not used
strictly).

Fair enough, now onto the recursive case. Typically, this is the case where static
analyses
[have to yield approximate results in order to stay decidable](https://en.wikipedia.org/wiki/Rice%27s_theorem).
Typically, this is achieved through calculating the least fixed-point of the
transfer function wrt. to the analysis lattice. Strictness analysis is no
different in that regard:

```haskell
  Let (Rec binds) body ->
    let
      sigs' = fixBinds sigs binds
      bodyTy = expr sigs' incomingArity body
      bodyTy' = foldr deleteFV bodyTy (map fst binds)
    in bodyTy'
```

That wasn't so hard! It seems that a few more functions were abstracted into
`fixBinds`, which is responsible for finding a set of sound strictness
signatures for the binding group. Let's see what else hides in `fixBinds`:

```haskell
fixBinds :: SigEnv -> [(Name, Expr)] -> SigEnv
fixBinds sigs binds = toSigEnv stableTypes
  where
    names :: [Name]
    names = map fst binds

    toSigEnv :: [(Arity, StrType)] -> SigEnv
    toSigEnv = foldr (\(n, ty) -> Map.insert n ty) sigs . zip names

    fromSigEnv :: SigEnv -> [(Arity, StrType)]
    fromSigEnv sigs = mapMaybe (flip Map.lookup sigs) names
```

We'll convert back and forth between the `SigEnv` representation and the list
of points of the `SigEnv` that are actually subject to change. `toSigEnv`
converts the points of the current binding group into a proper `SigEnv` by
adding them to the incoming `SigEnv`, which contains strictness signatures
for outer bindings.

```haskell
    stableTypes :: [(Arity, StrType)]
    stableTypes =
      fst
      . head
      . filter (uncurry (==))
      $ zip approximations (tail approximations)

    start :: [(Arity, StrType)]
    start = map (const (0, bottom)) binds

    approximations :: [[(Arity, StrType)]]
    approximations = iterate iter start
```

This part is concerned with finding the fixed-point of `iter`, beginning with an
optimistic approximation `start`, where all bindings are approximated by `bottom`.
We have found a fixed-point as soon as `approximations` becomes stable. This is
detected by `stableTypes`, which we converted into the result of `fixBinds` above.

```haskell
    iter :: [(Arity, StrType)] -> [(Arity, StrType)]
    iter tys = fromSigEnv (foldr iterBind (toSigEnv tys) binds)

    iterBind (name, rhs) sigs' =
      let
        arity = manifestArity rhs
        rhsTy = expr sigs' (manifestArity rhs) rhs
        rhsTy' = foldr deleteFV rhsTy names
      in Map.insert name (arity, rhsTy') sigs'
```

Aha, so `iterBind` is where the logic from the non-recursive case ended up!
The other functions were just a big build up to set up fixed-point iteration.
We compute iterated approximations of the signature environment until we hit
the fixed-point, at which point we have a sound approximation of program
semantics.

## Test-drive

Phew! That's it. Let's put our function to work.

```haskell
a, b, c, f :: Expr
(a:b:c:_:_:f:_) = map (Var . (:[])) ['a'..]

exprs :: [Expr]
exprs =
  [ If a b c
  , If a b b
  , If a (App f b) (App f c)
  , App (Lam "b" b) a
  , Let (NonRec ("f", Lam "b" b)) (App f a)
  , Let (Rec [("f", Lam "b" (App f b))]) (App f a)
  , Let (Rec [("f", Lam "b" (If b c (App f b)))]) (App f a)
  ]

main = forM_ exprs $ \e -> do
  print e
  print (analyse e)
  putStrLn ""
```

This is its output:

```unknown
If (Var "a") (Var "b") (Var "c")
StrType {fvs = TotalMap {def = L, points = fromList [("a",S)]}, args = L,L..}

If (Var "a") (Var "b") (Var "b")
StrType {fvs = TotalMap {def = L, points = fromList [("a",S),("b",S)]}, args = L,L..}

If (Var "a") (App (Var "f") (Var "b")) (App (Var "f") (Var "c"))
StrType {fvs = TotalMap {def = L, points = fromList [("a",S),("f",S(S))]}, args = L,L..}

App (Lam "b" (Var "b")) (Var "a")
StrType {fvs = TotalMap {def = L, points = fromList [("a",S)]}, args = L,L..}

Let (NonRec ("f",Lam "b" (Var "b"))) (App (Var "f") (Var "a"))
StrType {fvs = TotalMap {def = L, points = fromList [("a",S)]}, args = L,L..}

Let (Rec [("f",Lam "b" (App (Var "f") (Var "b")))]) (App (Var "f") (Var "a"))
StrType {fvs = TotalMap {def = B, points = fromList []}, args = B,B..}

Let (Rec [("f",Lam "b" (If (Var "b") (Var "c") (App (Var "f") (Var "b"))))]) (App (Var "f") (Var "a"))
StrType {fvs = TotalMap {def = L, points = fromList [("a",S),("c",S)]}, args = L,L..}
```

The first two test-cases are concerned with testing the `If` case.
The next two expressions test `App`lications and `Lam`das, most importantly
correct handling of incoming arity. Note how this correctly infers that `a`
was used strictly in the fourth example. What follows is a non-recursive
let-binding, basically doing the same as the fourth expression.

The last two expressions show-case what this simple analysis is able to infer.
First, there's a nonterminating `let f b = f b in f a` which is correctly
denoted by `bot`tom. This already hints that our analysis is able carry out some
inductive reasoning.
The last example then analyses `let f b = if b then c else f b in f a` to find
out that both `a` and `c` are used strictly. Cool!

## Conclusion

We defined a projection-based strictness analysis in the style of GHC that
actually finds out useful things about our code!

I hope that in doing so, you got a feeling about what GHC can and cannot derive
about the performance critical code you write. Specifically, looking back at
the problem in [part 1](/blog/2017-12-04-strictness-analysis-part-1.html), you
should now be able to see why we needed a bang in `printAverage` and how that
enables GHC to infer that the accumulator can be completely unboxed. This is
just by mechanically following the analysis rules above!

Granted, there are many details in which GHC's demand analyser (which does
strictness analysis) differs from the analysis above:

- Local, non-recursive thunk bindings have a different analysis rule than
  functions
- We ignore product demands like `S(LS(S))` for simplicity, but it's
  straight-forward to extend
- Various hacks and special cases that you can ignore in 95% of all cases

If you want to know more about these details, read the following papers:

- [Complete, but dated report on the demand analyser](https://www.microsoft.com/en-us/research/wp-content/uploads/2016/08/demand.pdf). This is probably the best paper for having an overview of what GHC does today in 95% of all cases.
- [Incomplete, but recent report on the demand analyser](https://www.microsoft.com/en-us/research/wp-content/uploads/2017/03/demand-jfp-draft.pdf)
- [Complete, recent report on usage analysis (dual to strictness) within the demand analyser](https://www.microsoft.com/en-us/research/wp-content/uploads/2014/01/cardinality-popl14.pdf)

I agree if you say that the documentation story is a little insatisfying.
Anyway, the ultimate reference is always the code of
[the demand analyser within GHC itself](https://gitlab.haskell.org/ghc/ghc/blob/master/compiler/stranal/DmdAnal.hs).

If/when I come around to it, I can finally pitch you my
[`datafix` library](https://hackage.haskell.org/package/datafix) for computing
fixed-points like we just did in a more principled way.
So stay stuned for part 4 :)

<b id="f1">1</b> ... 2017<a href="#a1">↩</a>