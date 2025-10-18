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
 Prop   = Sort    = Sort 0
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
We show here only the basic usage of `=` in Lean.
-/

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

-- Handling equality and inequality [TODO]

-- Basic exercises [TODO]
