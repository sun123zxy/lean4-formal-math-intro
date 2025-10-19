import Mathlib

/-
# From `Prop` to `Type`

In the previous chapter, we have seen that propositions are types in the `Prop` universe.
In this chapter, we shall move up to the `Type` universe.
-/

/-
## Numbers

Lean and Mathlib have many built-in types for numbers, including
-/
#check ℕ
#check ℤ
#check ℚ
#check ℝ
#check ℂ

/-
There are some built-in ways to represent numbers.
Lean interprets their types accordingly, like every programming language does.
-/
#check 3
#check 3.14
#check (22 / 7 : ℚ)
#check Real.pi
#check Complex.log (-1) / Complex.I

/-
Do note that numbers in different types work differently. Sometimes you need to explicitly
specify the type you want.
-/
#eval 22 / 7
#eval (22 : ℚ) / 7
#eval (22 / 7 : ℚ)

/-
You may not `#eval (22 : ℝ) / 7` because `ℝ` is not computable.
It's defined using Cauchy sequences of rational numbers.
For `Float` computation you may use `Float` type.
-/
#eval (22 : Float) / 7

/-
## Defining terms and functions

Recall that you may use `def` to define your own terms.
-/
def myNTTNumber : ℕ := 998244353
#check myNTTNumber

-- Functions [TODO]

-- `intro` for functions

/-
## Universe Hierarchy

If everything has a type, what is the type of a type?
-/

#check 3
#check Nat
#check Type
#check Type 1
#check Type 2

#check 1 + 2 = 3
#check Prop

/-
Lean has a hierarchy of universes:

```default
  ...
   ↓
Type 3            = Sort 4
   ↓
Type 2            = Sort 3
   ↓
Type 1            = Sort 2
   ↓
 Type   = Type 0  = Sort 1
   ↓
 Prop   =  Sort   = Sort 0
```

- `Prop` is the universe of logical propositions.
- `Type` is the universe of most of the mathematical objects.

At most times, you don't need to care about universe levels above `Type`.
But do recall the critical difference between `Prop` and `Type`:

Terms in `Prop`, i.e. proofs, are *proof-irrelevant*,
i.e. all proofs of the same proposition are considered equal,
while terms in `Type` are distinguishable in general.
This allows classical reasoning in `Prop`, and computation in `Type`.

You may explore more on this in the previous logic chapters.
-/

/-
## Equality `Eq` (`=`) (first visit)

Equality is a fundamental notation in mathematics, but also a major victim of *abuse of notation*.
Though trained experts can usually tell from context what kind of equality is meant,
it is still hopelessly confusing.

- In set theory, by axiom of extensionality, two sets are equal if and only if
they have the same elements.
- In Lean's type theory, equality is defined as an inductive type,
with `propext` and `Quot.sound` as extra axioms (`funext` is an corollary of `propext`).

We postpone the full discussion of equality to later chapters.
We show here only the basic usage of `=` in Lean, mostly in tactic mode.
-/

section

/-
`Eq` takes two terms of the same type, and produces a proposition in `Prop`.
For terms `a b : α`, the proposition `a = b` means that `a` and `b` are equal.
Do note that types of `a` and `b` must be the same, i.e. definitionally equal.
-/
#check Eq
#check 1 + 1 = 3
-- #check 1 + 1 = Nat -- this won't compile
#check (Real.sqrt 2) ^ 2 = (5 / 2 : ℕ)
/-
Note how the type of a number is interpreted and *implicitly coerced* in the last example.

*Coercions* are automatic conversions between types. It somewhat allows us to abuse notations
like mathematicians always do.
Detailing coercions would be another ocean of knowledge. We shall stop here for now.
-/

/-
### Handling equality
-/

variable (a b c : ℝ)

/-
The most basic way to show an equality is by tactic `rfl`:
LHS is definitionally equal to RHS.
-/
example : a = a := by rfl

/- `rw` is a tactic that rewrites a goal by a given equality. -/
example (f : ℝ → ℝ) (hab : a = b) : f a = f b := by
  rw [hab]

/- sometimes you need to apply the equality in the reverse direction -/
example (f : ℝ → ℝ) (hab : b = a) : f a = f b := by
  rw [← hab]

/- You may also use `symm` tactic to swap an equality -/
example (f : ℝ → ℝ) (hab : b = a) : f a = f b := by
  symm at hab
  rw [hab]

/- or swap at the goal -/
example (f : ℝ → ℝ) (hab : b = a) : f a = f b := by
  symm
  rw [hab]

/- You may also rewrite at a hypothesis. -/
example (hab : a = b) (hbc : b = c) : a = c := by
  rw [hbc] at hab
  exact hab

/-
### Work in `CommRing`

Let's do some basic rewrites in commutative rings, e.g. `ℝ`.
-/

/-
#### Commutativity and associativity
-/

#check add_comm
example : a + b = b + a := by rw [add_comm]

#check add_assoc
example : (a + b) + c = a + (b + c) := by rw [add_assoc]

#check mul_comm
example : a * b = b * a := by rw [mul_comm]

#check mul_assoc
example : (a * b) * c = a * (b * c) := by rw [mul_assoc]

/- Sometimes you need to specify the arguments to narrow down possible targets for `rw`. -/
example : (a + b) + c = (b + a) + c := by
  rw [add_comm a b]

/- [EXR] You may chain multiple rewrites in one `rw`. -/
example : (a + b) + c = a + (c + b) := by
  rw [add_assoc, add_comm b c]

#check mul_add
example : (a + b) * c = c * a + c * b := by
  rw [mul_comm, mul_add]

-- [EXR]
example : (a + b) * (c + b) = a * c + a * b + b * c + b * b := by
  rw [add_mul, mul_add, mul_add, ← add_assoc]

/-
#### Zero and one
-/

#check add_zero
example : a + 0 = a := by rw [add_zero]
#check zero_add
example : 0 + a = a := by rw [zero_add]

#check mul_one
example : a * 1 = a := by rw [mul_one]
#check one_mul
example : 1 * a = a := by rw [one_mul]

-- [EXR]
example : 1 * a + (0 + b) * 1 = a + b := by
   rw [one_mul, zero_add, mul_one]

/-
#### Subtraction
-/

-- [TODO]

/-
#### Automation

Feel dumb to do these trivial rewrites by hand?

`simp (at h)` tactic eliminates `0` and `1` automatically.
-/
example : c + a * (b + 0) = a * b + c := by
  simp
  rw [add_comm]

/-
`ring` tactic is even stronger: it reduces LHS and RHS to a canonical form
(it exists in any commutative ring) to solve equalities automatically.
`ring_nf (at h)` reduces the expression `h` to its canonical form.
-/
example : (a + 1) * (b + 2) = a * b + 2 * a + b + 2 := by
  ring

/-
#### A remark on type classes

Wondering how Lean knows that commutativity, associativity, distributivity, etc. hold for `ℝ`?
Wondering how Lean knows `a * 1 = a` and has relevant lemmas for that?
This is because Lean knows that `ℝ` is an commutative ring.
This is because in Mathlib, `ℝ` has been registered as an instance of the typeclass `CommRing`.
So that once you `import Mathlib`, Lean automatically knows about the `CommRing` structure of `ℝ`.
We might learn about typeclasses later in this course.
-/

#synth CommRing ℝ -- Checkout the `CommRing` instance that Mathlib provides for `ℝ`

end

/-
## Inequality (first visit)
-/

-- [TODO]
