---
title: Prop at the top?
tags: Lean, Agda, Rocq, Haskell, type theory
---

Lean's `Prop` confused me for a long time, but not propositions as types. That
a proposition is a type and a proof a term of it, the Curry-Howard
correspondence, is the whole point of a total language like Agda, and it gave me
no trouble. (In Haskell it is more slogan than tool, scary to newcomers and
pointless to practitioners, since the language is partial and `undefined` proves
anything.) What took me years to place was Lean's separate sort `Prop`.

<!--more-->

*This is a quick story I wanted to tell; I used an AI to tell it in a way I find
coherent.*

Lean has `Prop` because ordinary mathematics needs it. Mathematics is
impredicative (`sup S` is defined by quantifying over a collection that already
contains `sup S`) and classical (it uses choice without a second thought).
Neither fits a predicative, computational `Type`. The first is impredicative;
the second is non-constructive, since a classical existence proof need not yield
a witness and choice does not compute. So Lean keeps propositions as types where
you compute, in `Type`, and confines the classical, impredicative reasoning to
`Prop`. My difficulty was that `Prop` sits at `Sort 0`, the very bottom, yet
behaves like the top. Once I pictured it there, its rules
made sense, and I will end with why the bottom is nonetheless the right place
for it.

## The hierarchy

Lean has one universe hierarchy, `Sort`. `Type u` abbreviates `Sort (u+1)`, and
`Prop` is `Sort 0`:

```
 ...
 Sort 2  =  Type 1
 Sort 1  =  Type 0  =  Type
 Sort 0  =  Prop
```

Each level is typed by the next: `Prop : Type 0`, `Type 0 : Type 1`, and so on.
The type theory is essentially Rocq's, the Calculus of Inductive Constructions,
with two differences that matter here. Lean is not cumulative, so a type reaches
a higher level only by an explicit `ULift`, never on its own. And Lean's `Prop`
is Rocq's `SProp`: its proofs are definitionally equal, which Rocq's `Prop` is
not. Agda has the same `Type` hierarchy but nothing below `Type 0`; the bottom
rung is the whole question.

## What is special about Prop

Four things set `Prop = Sort 0` apart from the rest of the hierarchy.

1. **Impredicativity.** The function type `(x : A) → B`, with `A : Sort u` and
   `B : Sort v`, lives at `Sort (imax u v)`:

   ```
   imax u v = max u v   if v > 0
   imax u 0 = 0
   ```

   The first line is ordinary: the function type sits at the larger of its
   domain and codomain. The second is special: a function into `Prop` is a
   `Prop`, however large its domain. So `(α : Type) → P α` is a `Prop` although
   it ranges over every type.
2. **Proof irrelevance.** Any two proofs of a proposition are definitionally
   equal; the type checker never looks inside a proof.
3. **Restricted elimination.** A proof may be taken apart to prove another
   proposition, but not to produce data in `Type`. `Or`, `Exists` and
   `Nonempty` are sealed in this way.
4. **Smallness.** `Prop : Type 0`. The universe of propositions is itself a
   small type.

They look unrelated. They are one decision, and the way to see it is to imagine
`Prop` at the top of the hierarchy rather than the bottom.

## Move Prop to the top

The second line of `imax` is the oddity. Quantifying over a universe normally
costs a level (in Agda, a function over `Set 0` lands in `Set 1`), and
impredicativity declines to pay. Picture `Prop` not at the bottom but at the
very top, above every finite level; call it `ω`. A function into `Prop` then
lands at `max(level of A, ω) = ω`, plain `max` with no special case, since `ω`
is already above everything. The oddity was an oddity only because `Prop` sat at
the bottom, where quantifying over the levels above is a step up; at the top
there is nothing above to step past.

## Why the bottom is right

If `Prop` behaves like the top, why does Lean put it at the bottom? Because the
bottom is where it costs nothing. A `0` never raises a level where universes
combine (`max u 0 = u`, `imax u 0 = 0`), so anything at `Sort 0` is free.
`∀ (α : Type 5), α = α` is a proposition at `Sort 0`, as small as `2 = 2`,
though it quantifies over a universe far above it. And a proof stored as a field
adds nothing to the level of what stores it: `Subtype p` carries
`property : p val` in `Prop`, so `{ n : Nat // p n }` stays at `Type 0`, the
level of its data.

Put `Prop` at the top instead, and both break: `∀ (α : Type 5), α = α` becomes
too high to use as an ordinary type, and `{ n : Nat // p n }` inherits `ω` from
its proof field. You could patch the inductive case with a `max` that absorbs
`ω`, but the special case has only moved: what `imax` carried for functions, the
patched `max` now carries for inductives. Placement does not remove the special
case, it chooses where it lives. For that trade it is a wash; overall it is not.
The top adds two complications the bottom is spared: `Prop`'s own type must be
stipulated as `Sort ω : Type 0`, where the bottom reads `Prop : Type 0` off the
ordinary successor, and the level language must carry a transfinite `ω` at all.
The bottom is the strictly simpler theory, not merely the conventional one, and
that is why a production language keeps `Prop` there.

## The price of impredicativity

An impredicative universe is dangerous wherever it sits. A universe of real data
that quantifies over a copy of itself rebuilds the classical paradoxes inside
the type theory, Girard's paradox, which is why any relevant universe must be
predicative, as Agda's is. (Haskell takes the dangerous option, `Type :: Type`,
an inconsistency separate from its partiality.) `Prop` escapes only because its
inhabitants are not real data: proof irrelevance leaves a proposition at most
one inhabitant, and restricted elimination keeps that inhabitant from being
taken apart.

Impredicativity and restricted elimination meet on inductives. A proposition
may carry data of any size:
`Nonempty α` holds a value of `α : Type u` and is still a `Prop`, which is
impredicativity once more. But the value cannot be recovered, since
`Nonempty.rec` may only target `Prop`, which is why
`Classical.choice : Nonempty α → α` must be assumed rather than defined.
Carrying the data in is what seals it: a proposition admits recovery into `Type`
precisely when it has at most one constructor and that constructor's fields are
all proofs, so nothing was lost.

| proposition | data recoverable into `Type` |
| --- | --- |
| `False`, `True`, `Eq`, `Acc`, `And` of props | yes, there is nothing to recover |
| `Or`, `Exists`, `Nonempty` | no, recovery would expose erased data |

## Summary

`Prop` is not four exceptions but one decision: an impredicative universe, kept
consistent by restricted elimination, with proofs made irrelevant for erasure,
and made small by sitting at the bottom. It reads as inverted because
everything `Prop` does suggests the top, yet Lean files it at the bottom, where
propositions and proofs cost nothing.

Homotopy type theory avoids the question: it keeps no privileged `Prop`, taking
propositions to be the types with at most one inhabitant, at every level, with
resizing as an explicit axiom and proof irrelevance a property rather than a
definitional rule. That is the more uniform foundation, but the subject here is
a production language, where `Prop` is a sort and proofs irrelevant by
construction. For it the top is the right picture and the bottom the right
implementation, and that the bottom is also the strictly simpler theory, fewer
special cases and no transfinite levels, is a mark of how carefully Lean is
engineered.

## Further reading

- Theorem Proving in Lean 4, for the hierarchy and `Prop` as Lean presents
  them.
- Z. Luo, *Computation and Reasoning* (the Extended Calculus of
  Constructions), for an impredicative `Prop` against a predicative hierarchy.
- T. Coquand, "An analysis of Girard's paradox" (1986), for what fails when the
  top universe is made relevant.
- Gilbert, Cockx, Sozeau, Tabareau, "Definitional Proof-Irrelevance without K"
  (2019), for proof irrelevance and the elimination condition, and for `SProp`.
- On the predicative alternative, where small propositions are recovered by an
  axiom rather than by impredicativity: Voevodsky's resizing rules and the
  Homotopy Type Theory book.
