import Mathlib

/- # Logic -/

variable (p q r : Prop)

/-
## Implication `→`

For propositions `p` and `q`, the implication `p → q` means "if `p` then `q`".
By the Curry--Howard correspondence, `p → q` is also understood as
a function that takes a proof of `p` and produces a proof of `q`.

When we define a theorem `theorem name (h1 : p1) ... (hn : pn) : q := ...`,
we are actually defining a function of type
`name : (h1 : p1) → ... → (hn : pn) → (h : q)`.

`→` is right associative, so `p → q → r` means `p → (q → r)`.
You may notice that this is logically equivalent to `p ∧ q → r`.
This relationship is known as *currification*. We shall discuss this later.
-/

#check p → q
#check fun (hp : p) ↦ hp

/-
tactic: `exact`
If the goal is `p` and we have `hp : p`, then `exact hp` solves the goal.
-/

example (hp : p) : p := by
  exact hp

/- modus ponens -/
theorem mp (hp : p) (hpq : p → q) : q := by
  exact hpq hp

#check mp
#check (mp : (p : Prop) → (q : Prop) → p → (p → q) → q)

/-
tactic: `intro`
Sometimes a hypothesis is hidden in the goal in the form of an implication.
If the goal is `p → q`, then `intro hp` changes the goal to `q` and adds the hypothesis
`hp : p` into the context.
-/

example (hq : q) : p → q := by
  intro hp
  exact hq

/- modus ponens, with hidden hypothesis -/
example : p → (p → q) → q := by
  intro hp hpq -- you can `intro` multiple hypotheses at once
  exact hpq hp

/- transitivity of `→` -/
example (hpq : p → q) (hqr : q → r) : p → r := by
  intro hp
  exact hqr (hpq hp)

/-
tactic: `apply`
If `q` is the goal and we have `hpq : p → q`, then `apply hpq` changes the goal to `p`.
-/

/- modus ponens, with another proof -/
example (hp : p) (hpq : p → q) : q := by
  apply hpq
  exact hp

/- transitivity of `→`, with another proof -/
example (hpq : p → q) (hqr : q → r) : p → r := by
  intro hp
  apply hqr
  apply hpq
  exact hp

/-
# Negation `¬`, `True` and `False`
-/

/-
# And `∧` and or `∨`
-/

/-
# Iff `↔`
-/
