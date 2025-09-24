import Mathlib

/-
You may skip the materials tagged with [IGNORE] for the first runthrough.
Most of them are here to illustrate the nature of inductive types,
which may be too advanced for beginners.

# At the Very Beginning...

There are some basic notions you should be familiar with.

## `:` and `:=`

`3 : ℕ` means that `3` is a term of type `ℕ`.

By the Curry--Howard correspondence, `hp : p` means that `hp` is a proof of the proposition `p`.
-/

#check 3
#check ℕ
#check ∀ x : ℝ, 0 ≤ x ^ 2
#check sq_nonneg

/-
`:=` is used to define terms..
-/

def myThree : ℕ := 3

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
# Logic (Part I)

We shall work out the basic logic in Lean's dependent type theory.

[IGNORE]
You may notice along the way that except `→`,
all other logical connectives are defined as *inductive types*.
And they have their own *self-evident* *introduction rules* and *elimination rules*.
We shall discuss inductive types later in this course.
These logical connectives serve as good examples.

## Implication `→`

Implication `→` is the most fundamental way of constructing new types
in Lean's dependent type theory. It's one of the first-class citizens in Lean.

In the universe of `Prop`, for propositions `p` and `q`,
the implication `p → q` means "if `p` then `q`".
-/

section

variable (p q r : Prop) -- this introduces global variables within this section

#check p
#check q
#check p → q

/-
`→` is right-associative. In general, hover the mouse over the operators to see how they associate.
so `p → q → r` means `p → (q → r)`. You may notice that this is logically equivalent to `p ∧ q → r`.
This relationship is known as *currification*. We shall discuss this later.
-/

/- modus ponens -/
theorem mp : p → (p → q) → q := by sorry -- `sorry` is a placeholder for unfinished proofs

/-
By the Curry--Howard correspondence, `p → q` is also understood as
a function that takes a proof of `p` and produces a proof of `q`.

We introduce an important syntax to define functions / theorems:
When we define a theorem `theorem name (h1 : p1) ... (hn : pn) : q := ...`,
we are actually defining a function `name` of type `(h1 : p1) → ... → (hn : pn) → q`.
Programmingly, `h1`, ..., `hn` are the parameters of the function and `q` is the return type.

The significance of this syntax, compared to `theorem name : p1 → ... → pn → q := ...`, is that now
`h1`, ..., `hn`, proofs of `p1`, ..., `pn`, are now introduced as hypotheses into the context,
available for you along the way to prove `q`.
-/

/- this proves a theorem of type `p → p` -/
example (hp : p) : p := hp

/- modus ponens, with a proof -/
example (hp : p) (hpq : p → q) : q := hpq hp

/-
A function can also be defined inline, using `fun` (lambda syntax):
`fun (h1 : p1) ... (hn : pn) ↦ (hq : q)` defines a function of type
`(h1 : p1) → ... → (hn : pn) → q`

Some of the type specifications may be omitted, as Lean can infer them.
-/

example : p → p := fun (hp : p) ↦ (hp : p)
example : p → p := fun (hp : p) ↦ hp
example : p → (p → q) → q := fun (hp : p) (hpq : p → q) ↦ hpq hp
example : p → (p → q) → q := fun hp hpq ↦ hpq hp

/-
Construct proofs using explicit terms is called *term-style proof*.
This can be tedious for complicated proofs.

Fortunately, Lean provides the *tactic mode* to help us construct proofs interactively.

`by` activates the tactic mode.

The tactic mode captures the way mathematicians actually think:
There is a goal `q` to prove, and we have several hypotheses
`h1 : p1`, ..., `hn : pn` in the context to use.
We apply tactics to change the goal and the context until the goal is solved.
This produces a proof of `p1 → ... → pn → q`.
-/

example (hp : p) : p := by exact hp

/-
tactic: `exact`
If the goal is `p` and we have `hp : p`, then `exact hp` solves the goal.
-/

/- `exact?` may help to close some trivial goals -/
example (hp : p) (hpq : p → q) : q := by exact?

/-
tactic: `intro`
Sometimes a hypothesis is hidden in the goal in the form of an implication.
If the goal is `p → q`, then `intro hp` changes the goal to `q` and adds the hypothesis
`hp : p` into the context.
-/

/- modus ponens, with a hidden hypothesis -/
example (hp : p) : (p → q) → q := by
  intro hpq
  exact hpq hp

example (hq : q) : p → q := by
  intro _  -- use `_` as a placeholder if the introduced hypothesis is not needed
  exact hq

/- modus ponens, with two hidden hypothesis -/
example : p → (p → q) → q := by
  intro hp hpq -- you can `intro` multiple hypotheses at once
  exact hpq hp

/- [EXR] transitivity of `→` -/
example : (p → q) → (q → r) → (p → r) := by
  intro hpq hqr hp
  exact hqr (hpq hp)

/-
tactic: `apply`
If `q` is the goal and we have `hpq : p → q`, then `apply hpq` changes the goal to `p`.
-/

/- modus ponens, with another proof -/
example (hp : p) (hpq : p → q) : q := by
  apply hpq
  exact hp

/- [EXR] transitivity of `→`, with another proof -/
example (hpq : p → q) (hqr : q → r) : p → r := by
  intro hp
  apply hqr
  apply hpq
  exact hp

/-
tactic: `specialize`
If we have `hpq : p → q` and `hp : p`,
then `specialize hpq hp` reassigns `hpq` to `hpq hp`, a proof of `q`.
-/

/- modus ponens, with another proof -/
example (hp : p) (hpq : p → q) : q := by
  specialize hpq hp
  exact hpq

/- transitivity of `→`, with another proof -/
example (hpq : p → q) (hqr : q → r) : p → r := by
  intro hp
  specialize hpq hp
  specialize hqr hpq
  exact hqr

end

/-
## `True`, `False` and `Not`

In Lean's dependent type theory, `True` and `False` are propositions serving as
the *terminal and initial objects* in the universe of `Prop`.

Eagle-eyed readers may notice that `True` and `False` act similarly to
singleton sets and empty sets in set theory.

They are constructed as *inductive types*.
-/

/-
### `True` (`⊤`)

`True` has a single constructor `True.intro`, which produces the unique proof of `True`.
[IGNORE] Thus `True` is self-evidently true by `True.intro`.

`trivial` is a tactic that solves goals of type `True` using `True.intro`,
though it's power does not stop here.
-/

section

variable (p q : Prop)

#print True
#check True.intro

/- `True` as the terminal object -/
example : p → True := by
  intro _
  exact True.intro

/- The following examples shows that `True → p` is logically equivalent to `p`. -/

example (hp : p) : True → p := by
  intro _
  exact hp

/- [IGNORE] Above is actually the elimination law of `True`. -/
example (hp : p) : True → p := True.rec hp

example (htp : True → p) : p := htp True.intro

example (htp : True → p) : p := by
  apply htp
  trivial

/-
### `False` (`⊥`)

`False` has no constructors, meaning that there is no way to construct a proof of `False`.
This means that `False` is always false.

`False.elim` is the eliminator of `False`, serve as the "principle of explosion",
which allows us to derive anything from a falsehood.
[IGNORE] `False.elim` self-evidently true in Lean's dependent type theory.

`exfalso` is a tactic that applys `False.elim` to the current goal, changing it to `False`.
`contradiction` is a tactic that proves the current goal
by finding a trivial contradiction in the context.
-/

#print False
#check False.elim
#check False.rec -- [IGNORE] `False.elim` is actually defined as `False.rec`

/- eliminating `False` -/

example (hf : False) : p := False.elim hf

example (hf : False) : p := by
  exfalso
  exact hf

example (hf : False) : p := by
  contradiction

/- [EXR] -/
example (h : 1 + 1 = 3) : RiemannHypothesis := by
  contradiction

/-
On how to actually obtain a proof of `False` from a trivially false hypothesis via term-style proof
[TODO], see [here](https://lean-lang.org/doc/reference/latest//The-Type-System/Inductive-Types/#recursor-elaboration-helpers)
-/

/-
### `Not` (`¬`)

In Lean's dependent type theory, negation `¬p` is realized as `p → False`

You may understand `¬p` as "if `p` then absurd", indicating that `p` cannot be true.
-/

#print Not

/- this has a name `absurd` in Lean -/
#check absurd
example (hp : p) (hnp : ¬p) : False := hnp hp

/- [EXR] contraposition -/
example : (p → q) → (¬q → ¬p) := by
  intro hpq hnq hp
  exact hnq (hpq hp)
/- `contrapose!` is a tactic that does exactly this. We shall discuss this later. -/

/- [EXR] -/
example : ¬True → False := by
  intro h
  exact h True.intro

/- [EXR] -/
example : ¬False := by
  intro h
  exact h

/- [EXR] double negation introduction -/
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
- the *axiom of choice* `Classical.choice`
- the *law of excluded middle* `Classical.em`, which is a result of
  - the axiom of choice `Classical.choice`
  - *function extensionality* `funext`, which is a result of
    - the quotient axiom `Quot.sound`
  - *propositional extensionality* `propext`

You can always trace back like this in Lean, by ctrl-clicking the names.
This is a reason why Lean is awesome for learning logic and mathematics.
-/

/- [EXR] another side of contraposition -/
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
