import Mathlib

/- # Logic -/

/-
## Implication `→`

Implication `→` is the most fundamental way of constructing new types
in Lean's dependent type theory. It's one of the first-class citizens in Lean.

In the universe of `Prop`, for propositions `p` and `q`,
the implication `p → q` means "if `p` then `q`".

By the Curry--Howard correspondence, `p → q` is also understood as
a function that takes a proof of `p` and produces a proof of `q`.
-/

section

variable (p q r : Prop) -- this introduces global variables within this section

#check p → q
#check fun (hp : p) ↦ hp -- this is the inline way to define a function

/-
tactic: `exact`
If the goal is `p` and we have `hp : p`, then `exact hp` solves the goal.
-/
example (hp : p) : p := by
  exact hp

/-
In fact in this case we don't need a `by`, since `hp` is just of type `p`
`by` activates the tactic mode, which helps us construct proofs interactively
but you can also construct proofs directly (called term-style proof)
-/
example (hp : p) : p := hp

/-
When we define a theorem `theorem name (h1 : p1) ... (hn : pn) : q := ...`,
we are actually defining a function of type `name : (h1 : p1) → ... → (hn : pn) → (h : q)`.
`example`s are just anonymous `theorem`s.

`→` is right associative, so `p → q → r` means `p → (q → r)`.
You may notice that this is logically equivalent to `p ∧ q → r`.
This relationship is known as *currification*. We shall discuss this later.

Example: Say `hpqr`, `hp`, `hq` are proofs of `p → q → r`, `p`, `q` respectively.
Then `hpqr hp` is a proof of `q → r`, and `hpqr hp hq` is a proof of `r`.
-/

/- *modus ponens* -/
theorem mp (hp : p) (hpq : p → q) : q := by
  exact hpq hp
  -- try `exact?`

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

/- *modus ponens*, with hidden hypothesis -/
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

/- *modus ponens*, with another proof -/
example (hp : p) (hpq : p → q) : q := by
  apply hpq
  exact hp

/- transitivity of `→`, with another proof -/
example (hpq : p → q) (hqr : q → r) : p → r := by
  intro hp
  apply hqr
  apply hpq
  exact hp

end

/-
## `Not` (`¬`), `True` (`⊤`) and `False` (`⊥`)

In Lean's dependent type theory, `True` and `False` are propositions serving as
the initial and terminal objects in the universe of `Prop`.

They are constructed as inductive types, which is another fundamental way of constructing new types.
(We shall discuss inductive types later)
-/

/-
`True` has a single constructor `True.intro`, which produces the unique proof of `True`.
This means that `True` is self-evidently true.

`trivial` is a tactic that solves goals of type `True` using `True.intro`,
though it's power does not stop here.
-/

section

variable (p q : Prop)

#print True
#check True.intro

/- The following examples shows that `True → p` is logically equivalent to `p`. -/

example (hp : p) : True → p := by
  intro _ -- use `_` as a placeholder if the hypothesis is not needed
  exact hp

/- Above is actually the elimination law of `True`. Ignore this if you don't understand it now. -/
example (hp : p) : True → p := True.rec hp

example (htp : True → p) : p := htp True.intro

example (htp : True → p) : p := by
  apply htp
  trivial

/-
`False` has no constructors, meaning that there is no way to construct a proof of `False`.
This means that `False` is always false.

`False.elim` is the eliminator of `False`, serve as the "principle of explosion",
which allows us to derive anything from a falsehood.
Note that this principle is true *by definition* in Lean's dependent type theory.
You will understand this better after learning about inductive types.

`exfalso` is a tactic that applys `False.elim` to the current goal, changing it to `False`.
`contradiction` is a tactic that proves the current goal
by finding a trivial contradiction in the context.
-/

#print False
#check False.elim
#check False.rec -- ignore this if you don't understand it now

example (hf : False) : p := False.elim hf

example (hf : False) : p := by
  exfalso
  exact hf

example (hf : False) : p := by
  contradiction

example (h : 1 + 1 = 3) : RiemannHypothesis := by
  contradiction

/-
On how to actually obtain a proof of `False` from a trivially false hypothesis via term-style proof
TODO, see [here](https://lean-lang.org/doc/reference/latest//The-Type-System/Inductive-Types/#recursor-elaboration-helpers)
-/

/-
In Lean's dependent type theory, negation `¬p` is realized as `p → False`

You may understand `¬p` as "if `p` then absurd", indicating that `p` cannot be true.
-/

#print Not

/- this has a name `absurd` in Lean -/
#check absurd
example (hp : p) (hnp : ¬p) : False := hnp hp

/- contraposition -/
example : (p → q) → (¬q → ¬p) := by
  intro hpq hnq hp
  exact hnq (hpq hp)
/- `contrapose!` is a tactic that does exactly this. We shall discuss this later. -/

example : ¬True → False := by
  intro h
  exact h True.intro

example : ¬False := by
  intro h
  exact h

example : p → ¬¬p := by
  intro hp hnp
  exact hnp hp

/-
*Double negation elimination* is not valid in intuitionistic logic.
You'll need *proof by contradiction* `Classical.byContradiction` to prove it.
The tactic `by_contra` is created for this purpose.
If the goal is `p`, then `by_contra hnp` changes the goal to `False`,
and adds the hypothesis `hnp : ¬p` into the context.
-/
#check Classical.byContradiction

/- double negation elimination -/
theorem not_not_cancel : ¬¬p → p := by
  intro hnnp
  by_contra hnp
  exact hnnp hnp

/- You can use the following command to check what axioms are used in the proof -/
#print axioms not_not_cancel

/- For logical lunatics:

In Lean, `Classical.byContradiction` is proved by the fact that
all propositions are `Decidable` in classical logic, which is a result of
- *the axiom of choice* `Classical.choice`
- *the law of excluded middle* `Classical.em`, which is a result of
  - *the axiom of choice* `Classical.choice`
  - *function extensionality* `funext`, which is a result of
    - the quotient axiom `Quot.sound`
  - *propositional extensionality* `propext`

You can always trace back like this in Lean, by ctrl-clicking the names.
This is a reason why Lean is awesome for learning logic and mathematics.
-/

/- another side of contraposition -/
example : (¬q → ¬p) → (p → q) := by
  intro hnqnp hp
  by_contra hnq
  exact hnqnp hnq hp

end

/-
In fact above is equivalent to double negation elimination.
This one use the `have` tactic, which allows us to state and prove a lemma in the middle of a proof.
You don't have to digest the proof. Just see how `have` is used.
-/
example (hctp : (p q : Prop) → (¬q → ¬p) → (p → q)) : (p : Prop) → (¬¬p → p) := by
  intro p hnnp
  have h : (¬p → ¬True) := by
    intro hnp _
    exact hnnp hnp
  apply hctp True p h
  trivial

/-
# `And` (`∧`) and `Or` (`∨`)
-/

/-
# `Iff` (`↔`)
-/
