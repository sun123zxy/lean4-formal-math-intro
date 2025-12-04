/-
You may skip the materials tagged with [IGNORE] for the first runthrough.
They could be not well-explained, or too advanced for now.

Materials tagged with [EXR] are recommended for you to try before looking at the solution.

Materials tagged with [TODO] means that I'm still working on it,
or I'm not sure about the content yet. Feel free to give your suggestions!

## A First Glance

Have a look at the sample Lean code below. Can you understand what it means, without any prior knowledge of Lean?
-/

import Mathlib

theorem FLT (n : ℕ) (hn : n > 2) (a b c : ℕ) :
    a ≠ 0 → b ≠ 0 → c ≠ 0 → a^n + b^n ≠ c^n := by
  sorry

def TendsTo (a : ℕ → ℝ) (t : ℝ) : Prop :=
  ∀ ε > 0, ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → |a n - t| < ε

example : TendsTo (fun _ ↦ 998244353) 998244353 := by
  unfold TendsTo
  intro ε hε
  use 19260817
  intro n hn
  simp [hε]

theorem tendsTo_add {a b : ℕ → ℝ} {A : ℝ} {B : ℝ} (ha : TendsTo a A) (hb : TendsTo b B) :
    TendsTo (fun n => a n + b n) (A + B) := by
  sorry

theorem tendsTo_sandwich {a b c : ℕ → ℝ} {L : ℝ} (ha : TendsTo a L) (hc : TendsTo c L)
    (hab : ∀ n, a n ≤ b n) (hbc : ∀ n, b n ≤ c n) : TendsTo b L := by
  sorry

/-
## At the Very Beginning...

There are some basic notions you should be familiar with: `:` and `:=`.

`3 : ℕ` means that `3` is a term of type `ℕ`.

By the Curry--Howard correspondence, `hp : p` means that `hp` is a proof of the proposition `p`.
-/

#check 3
#check ℕ

#check ∀ x : ℝ, 0 ≤ x ^ 2
#check sq_nonneg
#check (sq_nonneg : ∀ x : ℝ, 0 ≤ x ^ 2)

/-
`:=` is used to define terms.
-/

def myThree : ℕ := 3

#check myThree

/-
`theorem` is just a definition in the `Prop` universe
By the Curry--Howard correspondence, for `theorem`,
behind `:`, the theorem statement follows;
behind `:=`, a proof should be given.
-/
theorem thm_sq_nonneg : ∀ x : ℝ, 0 ≤ x ^ 2 := sq_nonneg

-- `example` is just an anonymous theorem
example : ∀ x : ℝ, 0 ≤ x ^ 2 := thm_sq_nonneg

/-
We shall work out the basic logic in Lean's dependent type theory.

In this part, we cover:

- Implication
  - Syntax for defining functions / theorems
- Tactic Mode

[IGNORE]
You may notice along the way that except `→`,
all other logical connectives are defined as *inductive types*.
And they have their own *self-evident* *introduction rules* and *elimination rules*.
We shall discuss inductive types later in this course.
These logical connectives serve as good examples.
-/
