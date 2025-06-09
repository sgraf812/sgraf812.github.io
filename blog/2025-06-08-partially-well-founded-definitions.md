---
title: Partially well-founded definitions in Lean
tags: Lean, semantics, termination
---

This is my first post about Lean on this blog :)
It is meant as a response to [Joachim's post about extrinsic termination proofs](https://www.joachim-breitner.de/blog/816-Extrinsic_termination_proofs_for_well-founded_recursion_in_Lean).
I want to show how a slight modification of his idea can be used to define partial function definitions using well-founded recursion.

<!--more-->

### Background: structural vs. well-founded recursion

Many recursive function definitions terminate on all inputs by an inductive argument.
Such an argument either follows the structure of some inductively-defined input (e.g., `map` and the list it recurses on), in which case we speak of *structural*, or *primitive recursion*.
Or the argument is by some termination measure on the parameters into a well-founded relation and showing that recursive calls decrease modulo this measure, in which case we speak of *well-founded recursion*.
In a dependently-typed language, well-founded recursion can actually be expressed in terms of structural recursion; however the technique is subtle enough to think of it as a separate concept.

In Lean 4, (total) functions can be defined using both structural and well-founded recursion.
For well-founded recursion, the termination measure and the proof that recursive
calls decrease according to some well-founded relation can be specified through
`termination_by` and `decreasing_by` sections.
Check out [the Lean reference
manual](https://lean-lang.org/doc/reference/latest/Definitions/Recursive-Definit
ions/#recursive-definitions) for details.

### `termination_by` requires well-founded relation and call refinement proof upfront

Here is an example from the manual for integer division by iterated subtraction:

```lean
def div (n k : Nat) : Nat :=
  if k = 0 then 0
  else if k > n then 0
  else 1 + div (n - k) k
termination_by n
```

`termination_by` infers the well-founded relation as the lexicographic order on naturals, `Prod.lex Nat.lt_wfRel Nat.lt_wfRel`.
`Prod.lex` is a good choice because the only potential recursive call for an arbitrary `n` and `k` is at `(n-k)` and `k`, and clearly `(n-k) < n`, so `(n-k, k) < (n, k)`.

However, do note that this technique requires `termination_by` to be smart
enough to guess the well-founded relation, *at the definition site*.
If `termination_by` is not smart enough, the programmer has to intermingle their
code with a termination proof, even if that termination proof is only relevant
when trying to prove a property about their code.

This is only a mild annoyance and barely worth complaining about if it wasn't for the next point.

### `termination_by` only works for total functions

There are times when you want to define a function that you know won't terminate for some inputs.
Take the collatz sequence for `n` and the following definition computing its total stopping time:
```lean
partial def collatzLen (n : Nat) : Nat :=
  if n = 1 then 1
  else if n % 2 = 0
  then 1 + collatzLen (n / 2)
  else 1 + collatzLen (3 * n + 1)
```
This definition needs to be marked `partial`, because there is no known proof of termination for all `n`.
While such a definition compiles just fine, its logical interpretation in the
kernel is that of an opaque constant, and the user is required to prove that its
result type `Nat` is inhabited in order not to derive `False`.

Thus it is impossible to reason about this definition of `collatzLen` in the logic, even if we know
that `collatzLen 4 = 3` or `collatzLen 5 = 6` terminates.

One solution to this problem is the `partial_fixpoint` mechanism, but this
requires users to wrap the result in a monad that models a CCPO.

**In this post, I'm proposing an encoding of well-founded recursion that subsumes both total as well as partial functions such as `collatzLen`.**

This solution first gets rid of the requirement of providing a well-founded
relation such as `Nat.lt_wfRel`, which requires that the function terminates on
*all* inputs.
We do so by deriving the recursive call relation of a partial function from its defining F.
For total well-founded definitions, we can then prove that `Nat.lt_wfRel` is a
well-founded relation that *contains* the call relation, thus the [call relation
must be well-founded as well](https://github.com/leanprover/lean4/blob/6741444a63eec253a7eae7a83f1beb3de015023d/src/Init/WF.lean#L145-L150).
This proof may be conducted at the definition site (for maximally convenient reuse of the proof)
or at the call site (for maximal separation of code and proofs).

Secondly, we realize that when the termination proof is provided at the call site, we do not need
to provide it *for all points upfront*; it suffices to prove that the particular
point of the call is accessible wrt. the recursive call relation.

### Call relation of a functional

We can glean the call structure of a recursive function from its defining functional.
For `collatzLen`, this functional would be

```lean
def collatzLen.F (f : Nat → Nat) (n : Nat) : Nat :=
  if n = 1 then 1
  else if n % 2 = 0
  then 1 + f (n / 2)
  else 1 + f (3 * n + 1)
```

The main job of the elaborator will be to elaborate this definition into a definition as follows:

```lean
inductive collatzLen.Calls : Nat → Nat → Prop where
  | even (h : n % 2 = 0) : collatzLen.Calls (n / 2) n
  | odd (h₁ : ¬n = 1) (h₂ : ¬(n % 2 = 0)) : collatzLen.Calls (3 * n + 1) n

def collatzLen.F.refined (n : Nat) (f : (m : Nat) → collatzLen.Calls m n → Nat) : Nat :=
  if hone : n = 1 then 1
  else if hmod : n % 2 = 0
  then 1 + f (n / 2) (.even hmod)
  else 1 + f (3 * n + 1) (.odd hone hmod)
```

That is, every recursive call, represented by calls to the function parameter `f
m`, additionally passes a proof that `m` decreases according to the recursive
call structure of `collatzLen.F` as expressed by the inductive predicate `collatzLen.Calls`.

We say that `collatzLen.F.refined` is a *call refinement* of `collatzLen.F` and capture
this property abstractly in the following predicate:

```lean
/-- If `RecursesVia F R F'`, then `F'` refines calls to `f y` in `F f x` with a proof
that `R y x`, such that `F' x (fun y (_ : R y x) => f y) = F f x`. -/
def RecursesVia (F : (∀ y, β y) → (∀ x, β x)) (R : α → α → Prop) (F' : ∀ x, (∀ y, R y x → β y) → β x) : Prop :=
  ∀ f x, F' x (fun y _ => f y) = F f x
```

Besides coming up with `collatzLen.F.refined`, the elaborator must come up with a proof
of `RecursesVia collatzLen.F collatzLen.Calls collatzLen.F.refined`.
Fortunately, such a proof is essentially `by rfl`:

```lean
theorem collatzLen.F.recursesVia : RecursesVia collatzLen.F collatzLen.Calls collatzLen.F.refined := by
  intro f x
  rfl
```

Let's take a short break to realize that what we have done so far does not presume anything about
the mechanically-derived call relation `collatzLen.Calls`.
In particular, we have made no assumption about termination so far.
At this point we still have a choice:

1. We can elaborate `collatzLen` as a total function. In this case, we need to prove `WellFounded collatzLen.Calls`. (This is pretty hopeless.)
2. We can elaborate `collatzLen` as a partial function. In this case, the termination proof will be shifted to call sites.

We'll do (2) now and later see that (1) is actually a special case of the mechanism discussed next.

### `partial_fix` for partial functions

We define `collatzLen` in terms of a new combinator `partial_fix`:

```lean
-- TODO: `csimp` or `implemented_by`
noncomputable def partial_fix (F : (∀ y, β y) → (∀ x, β x)) (R : α → α → Prop) (href : ∃ F', RecursesVia F R F')
  (x : α) (hne : ¬Acc R x → Nonempty (β x)) : β x :=
  open Classical in
  if hacc : Acc R x
  then WellFounded.fixF href.choose x hacc
  else Classical.choice (hne hacc)

noncomputable def collatzLen (n : Nat) : Nat :=
  open collatzLen in
  partial_fix F Calls ⟨F.refined, F.recursesVia⟩ n (fun _ => inferInstance)
```

Note that this definition has a similar requirement as typical `partial` functions:
the result type `Nat` must be non-empty/inhabited.
However, (1) the result type must only be inhabited when the call won't
terminate, and (2) it suffices to prove `Nonempty` instead of `Inhabited`[^1].
Note that the `Nonempty` obligation is necessary only because we want to
expose `collatzLen.F` to users and hide `collatzLen.F.refined`; for the latter
we could just use `WellFounded.fixF` directly.

Compared to Lean's usual elaboration of `partial` functions to opaque
definitions, there is a huge advantage to this definition of a partial
`collatzLen` function: we can reason about it in our logic via the following
unrolling theorem:

```lean
theorem partial_fix_nonempty_acc_eq (hne : ∀y, ¬Acc R y → Nonempty (β y)) (hacc : Acc R x) :
    partial_fix F R href x (fun h => (h hacc).elim) = F (fun y => partial_fix F R href y (hne y)) x := by
  unfold partial_fix
  simp only [hacc, ↓reduceDIte]
  rw [WellFounded.fixF_eq, ←href.choose_spec]
  simp +contextual [hacc.inv]
```

Given a proof that `collatzLen 5` terminates (expressed by `Acc collatzLen.Calls 5`),
we may reduce `collatzLen 5` to `6`:

```lean
example : collatzLen 5 = 6 := by
  have h12  : collatzLen.Calls 1 2 := .even (n:=2) (by omega)
  have h24  : collatzLen.Calls 2 4 := .even (n:=4) (by omega)
  have h48  : collatzLen.Calls 4 8 := .even (n:=8) (by omega)
  have h816 : collatzLen.Calls 8 16 := .even (n:=16) (by omega)
  have h165 : collatzLen.Calls 16 5 := .odd (n:=5) (by omega) (by omega)
  have hacc : Acc collatzLen.Calls 5 :=
    Acc.intro 5 fun y h => match h with
    | .odd h₁ h₂ => Acc.intro 16 fun y h => match h with
    | .even h => Acc.intro 8 fun y h => match h with
    | .even h => Acc.intro 4 fun y h => match h with
    | .even h => Acc.intro 2 fun y h => match h with
    | .even h => Acc.intro 1 fun y h => match h with
    | .odd h₂ _ => (h₂ rfl).elim
  have hne : ∀y, ¬Acc collatzLen.Calls y → Nonempty Nat := fun _ => inferInstance
  simp [collatzLen, partial_fix_nonempty_acc_eq]
  rw [partial_fix_nonempty_acc_eq hne hacc]
  simp [collatzLen.F]
  have hacc := hacc.inv h165
  rw [partial_fix_nonempty_acc_eq hne hacc]
  simp [collatzLen.F]
  have hacc := hacc.inv h816
  rw [partial_fix_nonempty_acc_eq hne hacc]
  simp [collatzLen.F]
  have hacc := hacc.inv h48
  rw [partial_fix_nonempty_acc_eq hne hacc]
  simp [collatzLen.F]
  have hacc := hacc.inv h24
  rw [partial_fix_nonempty_acc_eq hne hacc]
  simp [collatzLen.F]
  have hacc := hacc.inv h12
  rw [partial_fix_nonempty_acc_eq hne hacc]
  simp [collatzLen.F]
```

This is still a pretty manual experience, but I imagine that it's possible to automate much of this proof with tactics, for example

```lean
theorem collatzLen.Calls5 : Acc collatzLen.Calls 5 := by
  repeat
  constructor
  intro y h
  cases h <;> try contradiction
```

Nice.

Next, we define total functions in terms of `partial_fix` (because we can and
because it shows that total functions just live at the end of a spectrum of
partial functions).

### `total_fix` for total functions

Recall that the most annoying issue we have with `partial_fix` is that it
requires us to pass a proof for `∀y, ¬Acc R y → Nonempty (β y)` (where `R`
is the call relation).
This obligation would annoy users who can prove their function total by
well-founded recursion.
The way users do so is to provide a proof for `WellFounded R`.
It turns out we can use such a proof to discharge the `Nonempty`ness obligation
as well, thus providing a combinator `total_fix` in terms of `partial_fix`:

```lean
theorem not_acc_nonempty_of_wellFounded {R} (wf : WellFounded R) :
    ∀y, ¬Acc R y → Nonempty (β y) := by
  intro y hnacc
  exfalso
  exact hnacc (wf.apply y)

noncomputable def total_fix (F : (∀ y, β y) → (∀ x, β x)) (R : α → α → Prop) (href : ∃ F', RecursesVia F R F')
  (wf : WellFounded R) : ∀ x, β x := fun x =>
  partial_fix F R href x (not_acc_nonempty_of_wellFounded wf x)

theorem total_fix_wf_eq :
    total_fix F R href wf x = F (fun x => total_fix F R href wf x) x :=
  partial_fix_nonempty_acc_eq (not_acc_nonempty_of_wellFounded wf) (wf.apply x)
```

NB: If we were to elaborate a function with a `termination_by`/`decreasing_by` section,
we would be able to hide all arguments to `total_fix` up to the actual
argument `x` inside the definition of, say, `ackermann`:

```lean
def ackermann.F (f : Nat × Nat → Nat) (x : Nat × Nat) : Nat :=
  match x with
  | (0, y) => y + 1
  | (x+1, 0) => f (x, 1)
  | (x+1, y+1) => f (x, f (x+1, y))

inductive ackermann.Calls : Nat × Nat → Nat × Nat → Prop where
  | case1 : ackermann.Calls (x, 1) (x+1, 0)
  | case2 : ackermann.Calls (x+1, y) (x+1, y+1)
  | case3 : ackermann.Calls (x, _) (x+1, y+1)

def ackermann.F.refined (x : Nat × Nat) (f : (y : Nat × Nat) → ackermann.Calls y x → Nat) : Nat :=
  match x with
  | (0, n) => n + 1
  | (x+1, 0) => f (x, 1) .case1
  | (x+1, y+1) => f (x, f (x+1, y) .case2) .case3

theorem ackermann.wf : WellFounded ackermann.Calls := by
  apply Subrelation.wf
  case r => exact Prod.Lex Nat.lt Nat.lt
  case h₂ => exact (Prod.lex Nat.lt_wfRel Nat.lt_wfRel).wf
  case h₁ =>
    intro x y h
    cases h
    case case1 => apply Prod.Lex.left <;> simp
    case case2 => apply Prod.Lex.right <;> simp
    case case3 => apply Prod.Lex.left <;> simp

noncomputable def ackermann (x y : Nat) : Nat := go (x, y)
where
  go := total_fix ackermann.F ackermann.Calls ⟨ackermann.F.refined, by intro f x; fun_cases ackermann.F <;> rfl⟩ ackermann.wf
```

This would allow to retain the same UX for `termination_by` as today.

### Conclusion

I tried to map out an approach to encoding partial functions in Lean's logic
that is compatible with its existing notion of well-founded recursion and
would allow reasoning about calls to partial functions that provably terminate.
I think that this encoding would nicely dovetail with Lean's existing elaborator
support for for well-founded recursion.

[^1]: This is due the use of `Classical`, I suppose. I'm not sure whether
      using a `csimp` rewrite would be safe if we do not strengthen `NonEmpty`
      to `Inhabited`.
