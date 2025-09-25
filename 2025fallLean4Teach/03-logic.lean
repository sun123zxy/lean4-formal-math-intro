import Mathlib

/-
# Logic (Part II)

## `And` and `Or`

In Lean's dependent type theory, `∧` and `∨` serve as
the *direct product* and the *direct sum* in the universe of `Prop`.

Eagle-eyed readers may notice that `∧` and `∨` act similarly to
Cartesian product and disjoint union in set theory.

They are also constructed as inductive types.
-/

section

variable (p q r : Prop)

/-
## `And` (`∧`)

The only constructor of `And` is `And.intro`, which takes a proof of `p` and a proof of `q`
to produce a proof of `p ∧ q`.

Regard this as the *universal property of the direct product* if you like.

`And.intro hp hq` can be abbreviated as `⟨hp, hq⟩`, called the *anonymous constructor*.

`constructor` tactic applies `And.intro` to split the goal `p ∧ q` into subgoals `p` and `q`.
You may also use the anonymous constructor notation `⟨hp, hq⟩` to mean `And.intro hp hq`.

`split_ands` tactic is like `constructor` but works for nested `And`s.
-/

#print And

/- introducing `And` -/

#check And.intro

/- [IGNORE] these examples, as introduction rules, are self-evidently true -/
example (hp : p) (hq : q) : p ∧ q := And.intro hp hq
example (hp : p) (hq : q) : p ∧ q := ⟨hp, hq⟩
example (hp : p) (hq : q) : p ∧ q := by
  constructor
  · exact hp
  · exact hq

/- [EXR] `→`--`∨` distribution. Universal property of the direct product. -/
example (hrp : r → p) (hrq : r → q) : r → p ∧ q := by
  intro hr
  exact ⟨hrp hr, hrq hr⟩

/-
`And.left` and `And.right` are among the elimination rules of `And`,
which extract the proofs of `p` and `q`.

`rcases hpq with ⟨hp, hq⟩` is a tactic that breaks down the hypothesis
`hpq : p ∧ q` into `hp : p` and `hq : q`.
Equivalently you can use `let ⟨hp, hq⟩ := hpq`.
-/

/- eliminating `And` -/

#check And.left
#check And.right
example (hpq : p ∧ q) : p := hpq.left
example (hpq : p ∧ q) : p := by
  rcases hpq with ⟨hp, _⟩
  exact hp
example : p ∧ q → p := by
  rintro ⟨hp, _⟩ -- `rintro` is a combination of `intro` and `rcases`
  exact hp

/- [EXR] `And` is symmetric -/
example : p ∧ q → q ∧ p := by
  intro hpq
  exact ⟨hpq.right, hpq.left⟩
#check And.comm -- above has a name

/- [EXR] `→`--`∨` distribution, in another direction. -/
example (hrpq : r → p ∧ q) : (r → p) ∧ (r → q) := by
  constructor
  · intro hr
    exact (hrpq hr).left
  · intro hr
    exact (hrpq hr).right

/- nested and -/

example (hpqr : p ∧ q ∧ r) : r := hpqr.right.right
example (hpqr : p ∧ q ∧ r) : r := by
  rcases hpqr with ⟨_, ⟨_, hr⟩⟩ -- anonymous constructor can be nested
  exact hr

example (hp : p) (hq : q) (hr : r) : p ∧ q ∧ r := by
  exact ⟨hp, ⟨hq, hr⟩⟩
example (hp : p) (hq : q) (hr : r) : p ∧ q ∧ r := by
  split_ands
  · exact hp
  · exact hq
  · exact hr

/-
The actual universal elimination rule of `And` is the so-called *decurrification*:
From `(p → q → r)` we may deduce `(p ∧ q → r)`. This is actually a logical equivalence.

Intuitively, requiring both `p` and `q` to deduce `r` is nothing but
requiring `p` to deduce that `q` is sufficient to deduce `r`.

[IGNORE] Decurrification is also self-evidently true in Lean's dependent type theory.

Currification is heavily used in functional programming for its convenience, Lean is no exception.

You are no stranger to decurrification even if you are not a functional programmer:
The *universal property of the tensor product of modules* says exactly the same.
-/

/- [EXR] currification -/
example (h : p ∧ q → r) : (p → q → r) := by
  intro hp hq
  exact h ⟨hp, hq⟩

/- [EXR] decurrification -/
example (h : p → q → r) : (p ∧ q → r) := by
  intro hpq
  exact h hpq.left hpq.right

example (h : p → q → r) : (p ∧ q → r) := by
  intro ⟨hp, hq⟩ -- `intro` is smart enough to destructure `And`
  exact h hp hq

example (h : p → q → r) : (p ∧ q → r) := by
  intro ⟨hp, hq⟩
  apply h -- `apply` is smart enough to auto-decurrify and generate two subgoals
  · exact hp
  · exact hq

/- [IGNORE] decurrification actually originates from `And.rec`, which is self-evident -/
#check And.rec
theorem decurrify (h : p → q → r) : (p ∧ q → r) := And.rec h

/- [EXR] `And.left` is actually a consequence of decurrification -/
example : p ∧ q → p := by
  apply decurrify
  intro hp _
  exact hp

/-
### `Iff` (`↔`), first visit

It's high time to introduce `Iff` here for the first time.

`Iff` (`↔`) contains two side of implications: `Iff.mp` and `Iff.mpr`.

Though it is defined as a distinct inductive type,
`Iff` is very similar to `And` in that you may, somehow, even use it like a `(p → q) ∧ (q → p)`.
The only major difference is the name of the two components.
-/

#check Iff.intro
#check Iff.mp
#check Iff.mpr

example : (p ↔ q) ↔ (p → q) ∧ (q → p) := by
  constructor
  · intro h
    exact ⟨h.mp, h.mpr⟩
  · intro ⟨hpq, hqp⟩
    exact ⟨hpq, hqp⟩

/-
### `Or` (`∨`)

`Or` has two constructors `Or.inl` and `Or.inr`.
Either a proof of `p` or a proof of `q` produces a proof of `p ∨ q`.

[TODO]
-/

#print Or
#check Or.inl
#check Or.inr
#check Or.elim
#check Or.rec

/- introducing `Or` -/

example (hp : p) : p ∨ q := Or.inl hp
example (hq : q) : p ∨ q := by
  right
  exact hq

/- elimination rule of `Or`, universal property of the direct sum -/

example (hpr : p → r) (hqr : q → r) : (p ∨ q → r) := fun hpq ↦ (Or.elim hpq hpr hqr)
example (hpr : p → r) (hqr : q → r) : (p ∨ q → r) := (Or.elim · hpr hqr) -- note the use of `·`
example (hpr : p → r) (hqr : q → r) (hpq : p ∨ q) : r := by
  apply Or.elim hpq
  · exact hpr
  · exact hqr

example (hpr : p → r) (hqr : q → r) : (p ∨ q → r) := fun
  | Or.inl hp => hpr hp
  | Or.inr hq => hqr hq
example (hpr : p → r) (hqr : q → r) (hpq : p ∨ q) : r :=
  match hpq with
  | Or.inl hp => hpr hp
  | Or.inr hq => hqr hq
example (hpr : p → r) (hqr : q → r) (hpq : p ∨ q) : r := by
  match hpq with
  | Or.inl hp => exact hpr hp
  | Or.inr hq => exact hqr hq
example (hpr : p → r) (hqr : q → r) (hpq : p ∨ q) : r := by
  cases hpq with
  | inl hp => exact hpr hp
  | inr hq => exact hqr hq
example (hpr : p → r) (hqr : q → r) (hpq : p ∨ q) : r := by
  rcases hpq with (hp | hq)
  · exact hpr hp
  · exact hqr hq
example (hpr : p → r) (hqr : q → r) : p ∨ q → r := by
  rintro (hp | hq)
  · exact hpr hp
  · exact hqr hq

/-
### Comprehensive exercises for `And` and `Or`

[EXR] distributive laws
-/

example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by sorry
example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := by sorry

/-
### `Decidable`: Do partial classical-logic reasoning in intuitionistic logic

It's high time to introduce `Decidable` here for the first time.

Mathematicians often know the intutionistic logic.
They know classical logic is equipped with `Classical.em`: `p ∨ ¬p` for any proposition `p`.
Though rarely do they know the concept of `Decidable`.

`Decidable p` means just the same as `p ∨ ¬p`.
It means that we know explicitly which one of `p` and `¬p` is true.

Though formally in Lean, `Decidable` is defined as a distinct inductive type,
it is very similar to `Or` in that you may, somehow, even use it like a `p ∨ ¬p`.
The major differences are:

- The constructors of `Decidable` has different names: `isTrue` and `isFalse`
- [IGNORE] `Decidable` lives in `Type` universe instead of `Prop` universe for some reasons [TODO].
- [IGNORE] It is tagged as a typeclass.
  This allows Lean to automatically find a proof of `Decidable p`
  so that you don't have to prove it yourself.

`Decidable` allows you to just assume `p ∨ ¬p` for only some propositions,
which is more flexible than simply working in classical logic.
-/

#check Decidable
#check Decidable.isTrue
#check Decidable.isFalse

#check Classical.byContradiction -- we have done this before

/- proof by contradiction in intuitionistic logic with decidable hypothesis -/
example [dp : Decidable p] : (¬p → False) → p := by
  intro hnpn
  rcases dp with (hnp | hp)
  · exfalso; exact hnpn hnp
  · exact hp
#check Decidable.byContradiction -- the above has a name

/-
### Pushing negations

Some negation can be pushed within intuitionistic logic. Some cannot.
-/

/- Classical logic: case analysis -/

example (hpq : p → q) (hnpq : ¬p → q) : q := Or.elim (Classical.em p) hpq hnpq
#check Classical.byCases -- above has a name

/- We have a corresponding tactic: `by_cases` -/
example (hpq : p → q) (hnpq : ¬p → q) : q := by
  by_cases hp : p
  · exact hpq hp
  · exact hnpq hp

/-
Proof by cases would help us to obtain an equivalent characterization of `Or`.

In intuitionistic logic, we cannot do implications like `¬p → q` implying `p ∨ q`,
because we don't know exactly which one of `p` and `¬p` is true,
and the introduction rules of `Or` are asking us to provide it explicitly.

This is a reason why intuitionistic logic is considered to be computable.

But in classical logic, or when `p` is `Decidable`, we can do it by case analysis on `p`.
-/
example : (p ∨ q) ↔ (¬p → q) := by
  constructor
  · rintro (hp | hq)
    · intro hnp
      exfalso
      exact hnp hp
    · intro _
      exact hq
  · intro hnpq  -- the direction of constructing `Or` needs classical logic
    by_cases h?p : p
    · left; exact h?p
    · right; exact hnpq h?p

/-
We also have an equivalent characterization of `And`.
This is also done in classical logic.
-/
example : (p ∧ q) ↔ ¬(p → ¬q) := by
  constructor
  · intro ⟨hp, hnq⟩ hpnq
    exact hpnq hp hnq
  · intro hnpnq -- the direction of constructing `And` needs classical logic
    contrapose hnpnq
    rw [Classical.not_not]
    intro hp hq
    exact hnpnq ⟨hp, hq⟩

/- [EXR] `→`--`∨` distribution -/
example : (r → p ∨ q) ↔ ((r → p) ∨ (r → q)) := by
  constructor
  · intro hrpq -- this direction needs classical logic
    by_cases h?r : r
    · rcases hrpq h?r with (hp | hq)
      · left; intro _; exact hp
      · right; intro _; exact hq
    · left
      intro hr
      exfalso; exact h?r hr
  · rintro (hrp | hrq)
    · intro hr
      left; exact hrp hr
    · intro hr
      right; exact hrq hr
#check imp_or -- above has a name

/- [EXR] De Morgan's laws -/
example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := by
  constructor
  · intro hnq
    constructor
    · intro hp
      apply hnq
      left; exact hp
    · intro hq
      apply hnq
      right
      exact hq
  · rintro ⟨hnp, hnq⟩ (hp | hq)
    · exact hnp hp
    · exact hnq hq
#check not_or -- above has a name

/- [EXR] De Morgan's laws -/
example : ¬(p ∧ q) ↔ ¬p ∨ ¬q := by
  constructor
  · intro hnpq -- this direction needs classical logic
    by_cases h?p : p
    · right
      intro hq
      apply hnpq
      exact ⟨h?p, hq⟩
    · left
      exact h?p
  · rintro (hnp | hnq) ⟨hp, hq⟩
    · exact hnp hp
    · exact hnq hq
#check not_and -- above has a name

/-
Introducing `push_neg` tactic: automatically proves all the above.
It works in classical logic where *negation normal forms* exist.

`by_contra!`, `contrapose!` are `push_neg`-enhanced version of their non-`!` counterparts.
-/

/-
For more exercises, see
[Propositions and Proofs - TPiL4](https://lean-lang.org/theorem_proving_in_lean4/Propositions-and-Proofs/#classical-logic)
-/

end

/-
# Forall `∀` and `Exists` `∃`

-/

/-
# `Iff` (`↔`), second visit

[TODO] We do it with `Eq`? In the next chapter?
-/
