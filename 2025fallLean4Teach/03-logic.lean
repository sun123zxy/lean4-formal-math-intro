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
example (hp : p) (hq : q) : p ∧ q := And.intro hp hq
example (hp : p) (hq : q) : p ∧ q := ⟨hp, hq⟩
example (hp : p) (hq : q) : p ∧ q := by
  constructor
  · exact hp
  · exact hq

/- [EXR] universal property of the direct product -/
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

/- [EXR] `And` is symmetric -/
example : p ∧ q → q ∧ p := by
  intro hpq
  exact ⟨hpq.right, hpq.left⟩

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
### `Or` (`∨`)

[TODO]
-/

end

/-
# `Iff` (`↔`)

[TODO]
-/
