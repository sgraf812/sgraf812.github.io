---
title: Total Denotational Semantics
tags: semantics
---

Denotational semantics assign meaning to a program (e.g., in untyped lambda
calculus) by mapping the program into a self-contained domain model in some meta
language (e.g., Scott domains).
Traditionally, what is complicated about denotational semantics is not so much
the *function* that defines them; rather it is to find a sound mathematical
definition of the *semantic domain*, and a general methodology of doing so that
scales to recursive types and hence general recursion, global mutable state,
exceptions and concurrency[^1][^2].

In this post, I discuss a related issue: I argue that traditional Scott/Strachey
denotational semantics are *partial* (in a precise sense), which means that

1. It is impossible to give a faithful, executable encoding of such a semantics in a programming language, and
2. Internal details of the semantic domain inhibit high-level, equational reasonining about programs

After exemplifying the problem, I will discuss *total* denotational semantics as
a viable alternative, and how to define one using guarded recursion.

<!--more-->

I do not claim that any of these considerations are novel or indisputable, but I
hope that they are helpful to some people who

* know how to read Haskell
* like playing around with operational semantics and definitional interpreters
* wonder how denotational semantics can be executed in a programming language
* want to get excited about guarded recursion.

I hope that this topic becomes more accessible to people with this background
due to a focus on *computation*.

I also hope that this post finds its way to a few semanticists who might provide
a useful angle or have answers to the conjectures in the later parts of this
post.

If you are in a rush and just want to see how a total denotational semantics
can be defined in Agda, have a look at
[this gist](https://gist.github.com/sgraf812/b9c10d8386a5da7ffe014e9f1dd9bc83).

---

\newcommand{\denot}[1]{\mathcal{I}\llbracket#1\rrbracket}
\newcommand{\denott}[1]{\mathcal{D}\llbracket#1\rrbracket}
\newcommand{\bind}{>\!\!>\!\!=}
\newcommand{\later}{\blacktriangleright}

# Syntax

We start by defining an AST type for lambda calculus:

```hs
type Name = String  -- x ∈ Name
data Exp            -- e
  = Var Name        --   ::= x
  | App Exp Exp     --    |  e1 e2
  | Lam Name Exp    --    |  λx.e
```

I will use the usual short-hand notation (BNF in comments above)

$$(λx.x)~(λy.y)$$

to parse as

```hs
Lam "x" (Var "x") `App` (Lam "y" (Var "y"))
```

and omit the parser that does this transformation.
I refer to `Exp` as the *object language* and to mathematics/Haskell as our
*meta language* in which we implement our semantics.

# Call-by-name Semantics

Let us now define a denotational semantics for this language.
We will first do this in mathematics and later try and turn this definition into Haskell.

A denotational semantics is a function
$\denot{\cdot}_{\cdot} : \mathsf{Exp} \to \mathsf{Map}(\mathsf{Name}, D) \to D$
such that $\denot{e}_ρ$ gives an expression $e$ a meaning, or *denotation*,
in terms of some semantic domain $D$.
I pronounce $\denot{e}_ρ$ as "interpret $e$ in environment $ρ$".
The environment $ρ$ gives meaning to the free variables of $e$,
by mapping each free variable to its denotation in $D$, and
$\mathsf{Map}(\mathsf{Name}, D)$ is the type of finite maps (think: `Data.Map.Map`).
I will write
$[x_1\mapsto d_1,...,x_n \mapsto d_n]$ for a (possibly empty) finite map literal
that maps name $x_i$ to $d_i$,
$ρ[x\mapsto d]$ for inserting the new mapping $x \mapsto d$ into the finite map
$ρ$,
$\mathsf{dom}(ρ)$ for the keys that are present in $ρ$, and
$ρ(x)$ for looking up name $x$ in $ρ$ (provided it is present).

With that disclaimer out of the way, here is the denotational semantics:

\begin{aligned}
\denot{x}_ρ & = \begin{cases}
  ρ(x) & x \in \mathsf{dom}(ρ) \\
  \bot & \text{otherwise}
  \end{cases} \\
\denot{λx.e}_ρ & = \mathsf{Fun}(f) \text{ where }f(d) = \denot{e}_{ρ[x \mapsto d]} \\
\denot{e_1~e_2}_ρ & = \mathit{app}(\denot{e_1}_ρ, \denot{e_2}_ρ) \\
  \mathit{app}(d,a) &= \begin{cases}
  f(a) & \mathsf{Fun}(f) = d \\
  \bot & \text{otherwise} \\
  \end{cases}
\end{aligned}

This is the standard by-name definition, but I have omitted an important detail.
I have not defined the semantic domain $D$ yet, so I shall do that now.

# Scott Domain

To a first approximation, we can think of the Scott domain $D$ as the Haskell
data type

```hs
data D           -- d
  = Fun (D -> D) --   ::= Fun (f ∈ D → D)
  | Bot          --    |  ⊥
```

Alas, this definition is not *well-founded*, and thus does not denote a proper
set (there is no set $D$ such that $D$ contains functions $D \to D$).
To make it well-founded, we need to impose an approximation order $⊑$ on
$D$ in which $\bot ⊏ \mathsf{Fun}(f)$ and restrict the function type $\to$ to
functions that are monotone ($\simeq$ more defined input leads to more defined
output) and even continuous ($\simeq$ the output on infinite input is determined
by the finite prefixes of the input) in $D$.
It is not important what *exactly* continuity means at this point, only that it
is impossible to impose this restriction in the type system of Haskell, let alone
enforce it as an invariant of `D`.

Henceforth, for every function $f$ that we stick into the $\mathsf{Fun}$
constructor, we need to prove that it is continuous, including the function
$f(d) = \denot{e}_{ρ[x \mapsto d]}$ in the lambda case of the semantics.
That in turn means we need to prove that the interpretation function is
continuous as well, otherwise $\denot{\cdot}$ is not a well-defined
mathematical object.
One can see that this is quite tedious to prove by hand and in practice this
obligation is often hand-waved away, endangering the well-definedness of
any concept that builds on $\denot{\cdot}$.

Let me support our understanding of $\denot{\cdot}$ with a few examples:

* $\denot{λx.x}_{[]} = \mathsf{Fun}(d \mapsto d)$.
  Note that I write $d \mapsto d$ for a lambda expression in math, distinct from the *syntax* $(λd.d)$.
* $\denot{(λx.x)~(λy.y)}_{[]} = \mathit{app}(\mathsf{Fun}(d \mapsto d), \denot{λy.y}_{[]}) = \denot{λy.y}_{[]} = \mathsf{Fun}(d \mapsto d)$.
* $\denot{x~(λy.y)}_{[]} = \mathit{app}(\denot{x}_{[]}, \denot{λy.y}_{[]}) = \mathit{app}(\bot, \denot{λy.y}_{[]}) = \bot$.
  The bottom element $\bot$ is used to indicate a stuck program, in this case because variable $x$ is not "in scope" in the empty environment $[]$.

# A *partially-defined* denotational interpreter

Now consider the following attempt to make this semantics executable in Haskell:

```hs
interp :: Map Name D -> Exp -> D
interp env (Var x) = case Map.lookup x env of
  Just d  -> d
  Nothing -> Bot
interp env (Lam x e) = Fun (\d -> interp (Map.insert x d env) e)
interp env (App e1 e2) = case interp env e1 of
  Fun f -> f (interp env e2)
  _     -> Bot
```
I call `interp` a *denotational interpreter*, as suggested by
[Matthew Might](https://web.archive.org/web/20100216131108/https://matt.might.net/articles/writing-an-interpreter-substitution-denotational-big-step-small-step/).
The single most characteristic feature distinguishing it from a big-step style
definitional interpreter is the lambda case.
Note that the denotational interpreter recurses into the lambda body, sticking a
function of type `D -> D` into the semantic `Fun` constructor, whereas a
big-step style interpreter would simply return the syntax `Lam x e`.

Surprisingly, the above translation of $\denot{\cdot}$ is *almost* correct!
It is correct whenever the object program terminates and
provides the same result as the denotational semantics for all three examples above.

However, when the object program does *not* terminate, the denotational
interpreter above does neither.
One example of such a program is $\Omega := (λx.x~x)~(λx.x~x)$.
Running `interp` on the parse of this program simply loops forever, whereas the
denotational semantics $\denot{\cdot}$ assigns the meaning $\bot$ to
$\Omega$, as common wisdom would have it.
Thus, when viewed as a mathematical function, `interp` above is only
partially-defined, or just *partial*.
This is in contrast to $\denot{\cdot}$, which is a *total* mathematical
function, defined on every input.

(Doesn't "$\denot{\cdot}$ is total" contradict the title of this post?
How can a function such as $\denot{\cdot}$ return $\bot$ but still be considered total?
Park these thoughts and read on.)

**It appears we cannot find a faithful executable definition of
$\denot{\cdot}$ in Haskell**, one which encodes a *total* mathematical
function $\denot{\cdot}$.
Which is a pity, because a definition in Haskell greatly helps in prototyping,
exploring and even formalising such semantics.

# Divergence is hard to grasp in Scott domains

Actually, who says that $\denot{\Omega}_{[]} = \bot$?
If we just calculate with the definition of $\Omega$, we get
\begin{aligned}
  \denot{\Omega}_{[]} &= \denot{(λx.x~x)~(λx.x~x)}_{[]} \\
                      &= \mathit{app}(\denot{λx.x~x}_{[]}, \denot{λx. x~x}_{[]}) \\
                      &= \mathit{app}(\mathsf{Fun}(d \mapsto \denot{x~x}_{[x\mapsto d]}), \denot{λx. x~x}_{[]}) \\
                      &= \denot{x~x}_{[x\mapsto \denot{λx. x~x}_{[]}]} \\
                      &= \denot{(λx.x~x)~(λx.x~x)}_{[]} \\
                      &= \denot{\Omega}_{[]} \\
\end{aligned}
A circular rewrite!
This chain of reasoning would hold true regardless of what value we would assign to $\Omega$.
One way to prove that $\denot{\Omega}_{[]} = \bot$ is by generalising this statement to $\mathrm{Y}(\mathit{id})$
and then understanding Example 3.6 of Pitts'
[Relational Properties of Domain](https://www.sciencedirect.com/science/article/pii/S0890540196900528).
Needless to say, even such an "obvious" semantic fact such as "$\Omega$
diverges" does not hold by simple calculation and does not
even appear to be [true in some (inadequate) semantic domain
models](https://homepages.inf.ed.ac.uk/gdp/publications/TIM.pdf).
No wonder that it isn't possible to compute it in Haskell either; after all,
computation is just a directed form of equational reasoning.

# Total denotational interpreter

Haskell is a lazy language.
As a Haskeller, I eat infinite lists for breakfast and enjoy it, because I know when
to stop `take`ing (🥁📀).
Can we somehow use laziness to encode diverging programs?

It turns out that, yes, we can!
We only need to adjust our semantic domain `D` as follows:

```hs
data T a = Ret !a | Step (T a)
data Value = Fun (D -> D) | Stuck
type D = T Value
```

The coinductive `T` data type (for "trace") is a
[classic](https://arxiv.org/abs/cs/0505037). It forms a monad as follows:
```hs
instance Monad T where
  return = Ret
  Ret a  >>= k = k a
  Step d >>= k = Step (d >>= k)
```
Note that `Step` is lazy, so we get diverging program "traces" as follows:

```hs
diverge :: D
diverge = Step diverge
```

It is pretty simple to run a `D` for a finite amount of time:

```hs
takeD :: Int -> T a -> Maybe a
takeD _ (Ret a)  = Just a
takeD 0 _        = Nothing
takeD n (Step d) = takeD (n-1) d
```

The use of `Step` is crucial to stratify diverging computations into an
infinite layering of finite computations, separated by `Step` constructors.
In other words: We use coinduction (well, Löb induction, but close enough) to
encode diverging programs.

It is sufficient to delay in a single place: right before we put a denotation
into the environment.
(A more common alternative in the literature is to delay in the variable case instead.)
The new definition becomes

```hs
denot :: Map Name D -> Exp -> D
denot env (Var x) = case Map.lookup x env of
  Just d  -> d
  Nothing -> Stuck
denot env (Lam x e) = Fun (\d -> denot (Map.insert x (Step d) env) e)
denot env (App e1 e2) = denot env e1 >>= \case
  Fun f -> f (denot env e2)
  _     -> return Stuck
```

(A self-contained Haskell playground for `denot` can be found [here](https://play.haskell.org/saved/haARY9UX).)

We use monadic bind in the application case to sequence computations.
Note that if evaluation of `e1` diverges, the continuation of `>>=`
will never be called.

Using `takeD`, we may now execute a program for any number of `Step`s!
`denot` thus becomes a *total* function, defined by mixed induction (for `denot`)
and Löb induction (to define the lambda constructor).
Here are a two more examples:

```hs
-- |
-- >>> takeD 10000 $ denot Map.empty idid
-- Just (Fun ...)
-- >>> denot Map.empty idid
-- Step (Ret (Fun ...))
idid :: Exp
idid = Lam "x" (Var "x") `App` Lam "y" (Var "y")

-- |
-- >>> takeD 10000 $ denot Map.empty omega
-- Nothing
omega :: Exp
omega = Lam "x" (Var "x" `App` Var "x") `App` Lam "y" (Var "y" `App` Var "y")
```

If you want to see more of these, I encourage you to read Section 4 of
our work on [abstracting denotational interpreters](https://arxiv.org/abs/2403.02778).

### Why explicit `Stuck`?

I renamed `Bot` to `Stuck` in the above definition of `Value` because that is
what its use now encodes: stuck programs terminate with a `Stuck` value that
works like an exception or [Milner's $\textbf{wrong}$
value](https://homepages.inf.ed.ac.uk/wadler/papers/papers-we-love/milner-type-p
olymorphism.pdf) (as in "well-typed programs cannot go wrong").
This is observably distinct from the `diverge` denotation for diverging
programs.
I *could* have used `diverge` instead of `return Stuck`, however that would be
a bit misleading.
(As misleading as in the vanilla denotational semantics, where stuckness and
divergence are confused.)

# Total denotational semantics

We can interpret the above definition of `D` straight as a domain equation of
(flat) Scott domains.
To do so, we need to adjoin a distinct bottom element $\bot$ again, with
the property that $\bot ⊏ \mathsf{Fun}(f)$, $\bot ⊏ \mathsf{Stuck}$ and
$\mathsf{Fun}(f)$ incomparable to $\mathsf{Stuck}$.

Here is the redefinition of $\denot{\cdot}$ in terms of the rejigged $D$
(calling it $\denott{\cdot}$ for lack of a differentiating name):

\begin{aligned}
\denott{x}_ρ & = \begin{cases}
  ρ(x) & x \in \mathsf{dom}(ρ) \\
  \mathsf{Ret}(\mathsf{Stuck}) & \text{otherwise}
  \end{cases} \\
\denott{λx.e}_ρ & = \mathsf{Fun}(f) \text{ where }f(d) = \denott{e}_{ρ[x \mapsto \mathsf{Step}(d)]} \\
\denott{e_1~e_2}_ρ & = \denott{e_1}_ρ \bind v \mapsto \mathit{app}(v, \denott{e_2}_ρ) \\
  \mathit{app}(v,a) &= \begin{cases}
  f(a) & \mathsf{Fun}(f) = v \\
  \mathsf{Ret}(\mathsf{Stuck}) & \text{otherwise} \\
  \end{cases}
\end{aligned}

I omitted the definition of the bind operator $\bind$, which is exactly as in Haskell.

It is reasonably simple to see by equational reasoning that $\Omega$ diverges:

\begin{aligned}
  \denott{\Omega}_{[]} &= \denott{(λx.x~x)~(λx.x~x)}_{[]} \\
                      &= \denott{λx.x~x}_{[]} \bind v \mapsto \mathit{app}(v, \denott{λx. x~x}_{[]}) \\
                      &= \mathsf{Ret}(\mathsf{Fun}(d \mapsto \denott{x~x}_{[x\mapsto \mathsf{Step}(d)]})) \bind v \mapsto \mathit{app}(v, \denott{λx. x~x}_{[]}) \\
                      &= \denott{x~x}_{[x\mapsto \mathsf{Step}(\denott{λx. x~x}_{[]})]} \\
                      &= \denott{x}_{[x\mapsto \mathsf{Step}(\denott{λx. x~x}_{[]})]} \bind v \mapsto \mathit{app}(v, \denott{x}_{[x\mapsto \mathsf{Step}(\denott{λx. x~x}_{[]})]}) \\
                      &= \mathsf{Step}(\denott{λx. x~x}_{[]}) \bind v \mapsto \mathit{app}(v, \mathsf{Step}(\denott{λx. x~x}_{[]})) \\
                      &= \mathsf{Step}(\mathsf{Ret}(\mathsf{Fun}(d \mapsto \denott{x~x}_{[x\mapsto \mathsf{Step}(d)]}))) \bind v \mapsto \mathit{app}(v, \mathsf{Step}(\denott{λx. x~x}_{[]})) \\
                      &= \mathsf{Step}(\denott{x~x}_{[x\mapsto \mathsf{Step}(\mathsf{Step}(\denott{λx. x~x}_{[]}))]}) \\
                      &= ... \\
                      &= \mathsf{Step}^n(\denott{x~x}_{[x\mapsto \mathsf{Step}^m(\denott{λx. x~x}_{[]})]}) \\
                      &= ... \\
                      &= \mathsf{Step}^ω = \mathit{diverge} \\
\end{aligned}

So that's already nicer than with $\denot{\cdot}$.
Another key difference to $\denot{\cdot}$ is that I believe $\denott{\cdot}$
to be total, which implies that it maps total environments to total denotations[^4].
(I'm *very optimistically* omitting a proof here, the novelty of which would
be unlikely. See the footnote.)

An element of a domain $d$ is *total*[^3] (or, *maximal*) if there are no other
elements $d'$ above it, so $d ⊑ d' \implies d = d'$.
An element $d$ is *partial* if there exists an element $d'$ above it, $d ⊏ d'$.

Clearly, the bottom element $\bot$ is as partial as it gets (in a non-trivial
domain such as $D$).
There are other *finite* partial elements such as $\mathsf{Step}(\bot)$, but also
*infinite* partial elements such as $(\bot,(\bot,(\bot,...)))$ (if our $D$ had a
pair constructor).
There are *finite* total elements such as $\mathsf{Ret}(\mathsf{Stuck})$ and *infinite*
total elements such as $\mathsf{Step}^ω$ (corresponding to `diverge`).

*In this precise sense*, the vanilla denotational semantics $\denot{e}$ is a
*partial* element of the monotone function space
$\mathsf{Map}(\mathsf{Name}, D) \to D$ (it returns $\bot$ in a couple of
situations) and $\denott{e}$ is a *total* element of the monotone function space
$\mathsf{Map}(\mathsf{Name}, D) \to D$.
Note how this notion of partiality is different from partially of
a mathematical function: $\denot{e}$ is a partial *element*, but a total *function*.

### Reasoning and computing with total elements

The crucial insight is this: **In programming languages, we can only really
reason equationally about and compute with *total* elements (finite or
infinite), but not so easily with *partial* ones**, because that requires
reasoning in the actual formal *semantics* for the programming language (rather
than reasoning equationally on its *syntax*).

It is tiresome that in order to reason about diverging programs in our object
language `Exp`, we need to know whether a Haskell program diverges.
This means we need to know two formal semantics: a small one for `Exp` and a big
one for Haskell.

### Total elements and guarded recursion abstract away the approximation order

There is another advantage to such total denotational semantics:
Since total elements have no elements above them, the approximation order on
total elements is *discrete*, just like we are used from set theory.
That is, $\mathsf{Ret}(\mathsf{Stuck})$ is incomparable to
$\mathsf{Step}(\mathsf{Ret}(\mathsf{Stuck}))$ because both are total elements.
Thus, one can write total denotational semantics without thinking about
the approximation order, except in one specific case: encodings of recursion.

Our denotational semantics encodes recursion in the seemingly paradoxical
type of the $\mathsf{Fun}$ constructor, the field of which is a function taking
a $D$ as argument.
Such negative recursive occurrences are the bane of semanticists, but they
have developed a remedy: Guarded type systems.

### Guarded types erase to continuous definitions

In a guarded type system, one would declare that $\mathsf{Fun}$ has type
$\later D \to D$, where $\later$ is an applicative functor
called the *later modality*, and the type checker would happily accept such
a type. The later modality can be thought of as a principled way to introduce a
lazy thunk. As such, we may change the type of $\mathsf{Step}$ to $\later D \to
D$, encoding the lazy nature of $\mathsf{Step}$.
Do note that the $d$ introduced in the lambda case of $\denott{\cdot}$ has type
$\later D$, so it is important to give $\mathsf{Step}$ this delaying type in
order for the interpreter to be well-typed and total.

Et voilà, we have just proven that $\denott{\cdot}$ is well-defined and total
without (directly) appealing to any domain theory!

Presently, only few proof assistants have support for guarded types, but
Agda is one of them (albeit with rather rudimentary support).
[You can find an Agda encoding of $\denott{\cdot}$ in
this gist](https://gist.github.com/sgraf812/b9c10d8386a5da7ffe014e9f1dd9bc83).
A self-contained Haskell playground for `denot` can be found [here](https://play.haskell.org/saved/haARY9UX).

# Conclusion

This post was kind of a mixed bag of thoughts I had while working on our paper
[Abstracting Denotational Interpreters](https://arxiv.org/abs/2403.02778),
where I found it frustrating that I was lacking both the space and the words to
phrase this article into a proper motivation for the use of guarded type theory.
The ultimate goal of this post is to lure people who are familiar with
traditional denotational semantics into learning about total denotational
semantics and guarded type theory.

I sincerely believe that guarded type theory is the future for total, executable
reasoning about what today is often branded coinduction, since it is much more
applicable than mere coinduction but also different in subtle ways[^Iris].
(For example, `D` could not be defined by coinduction because of the negative
recursion in `Fun`.)
Furthermore, it comes with decent (yet still incomplete) axiomatisations in
proof assistants.

I have glossed over *a lot* of related work in this post in order not to break the flow.
Apologies for that.
I suggest to have a look at the [PLS lab page on guarded recursion](https://www.pls-lab.org/en/Guarded_recursion_(type_theory)),
and perhaps start by reading Bob Atkey and Conor McBride's classic [Productive
Coprogramming with Guarded Recursion](https://bentnib.org/productive.pdf) (which
does not cover negative recursive occurrences yet).
One of the most exciting recent results in this area is a formal model for
[impredicate guarded dependent type theory](https://arxiv.org/abs/2210.02169)
(phew!), which can serve as the justification for an axiomatisation in Rocq and
Lean, which has [since been used](https://arxiv.org/abs/2308.02906) to define
the equivalent of the Iris higher-order concurrent separation logic framework.
The trace type `T` above is a much simplified version of a
[guarded](https://arxiv.org/abs/2307.08514)
[interaction tree](https://dl.acm.org/doi/10.1145/3371119).
Definitional equality on (guarded or Scott) `D` is also *not* a very useful
program equivalence -- you would still need to appeal to the coarser contextual
equivalence or a custom logical relation for proving interesting properties
about program rewrites.
My interest is in the context of abstract interpretation, where it is sufficient
to view equivalence modulo the abstraction function $α$.

[^1]: The classic text demonstrating these issues is <a href="https://www.sciencedirect.com/science/article/pii/S0890540184710935">A Syntactic Approach to Type Soundness</a>.

[^2]: Incredibly smart semanticists such as Lars Birkedal, Jon Sterling and
      others are continually improving the "internal language" (which I think
      means "domain-specific language" to category theorists) for defining such
      complex semantic domains; the subject of synthetic domain theory.
      This [talk by Jon](https://www.youtube.com/watch?v=lLvweTSmR40)
      (with questions from 90 years old Dana Scott!) provides a lot of historic
      context and can serve as a technical introduction as well.

[^3]: This is at least the terminology used in
      [Cartwright et al.](https://arxiv.org/abs/1605.05858),
      which I very much enjoyed.

[^4]: On the monotone function space $D \to D$, a function $f$ is only total
      when it is also maximally non-strict -- that is, $f(d)$ must be the greatest
      lower bound of its upper set in the range of $f$.
      More formally, $f(d) = ⊓ \{ d' \mid d'∈ \mathsf{rng}(f) \land f(d) ⊑ d' \}$.
      For any function $f$ defined on total inputs, this can easily be achieved by
      extending it to partial inputs via
      $f(d) := ⊓ \{ f(d') \mid d' ∈ D \land d \text{ total} \land d ⊑ d' \}$.
      Note that any $f'$ such that $f ⊏ f'$ must overcommit for one input $d_1$
      (so $f(d_1)⊏f'(d_1)$), but then there must exist another $d_2$ such that
      $d_1 ⊏ d_2$ for which $f(d_2) \not⊑ f'(d_2)$, otherwise $f'(d_1)$ would
      be a greater lower bound than $f(d_1)$; contradiction.

[^Iris]:
      For a comparison of induction, coinduction and guarded
      recursion, have a look at Section 16 of the
      [Iris lecture notes](https://iris-project.org/tutorial-pdfs/iris-lecture-notes.pdf).
