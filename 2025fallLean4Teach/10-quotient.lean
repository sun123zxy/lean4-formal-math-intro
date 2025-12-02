/-
# Quotients

After building up the theory of groups, homorphisms, and subgroups,
we are now ready to define quotient groups.

In fact, quotients are so fundamental that
Lean makes them a primitive way of constructing new types.
[IGNORE] Other reasons including the foundation of `funext`, see [The Lean Language Manual](https://lean-lang.org/doc/reference/latest/The-Type-System/Quotients/#quotient-funext).

We shall first illustrate the general quotient construction in Lean,
and then specialize it to quotient groups.

At the end of the journey, we show the first isomorphism theorem for groups as promised.
-/
import Mathlib

/-
## Quotient Sets

We still build up the theory from sets.
First, we need to define equivalence relations on a type `α`.
As you can guess, a binary relation `r` is just a `α → α → Prop`.
-/
section

variable {α : Type*} {r : α → α → Prop} (a b c : α)

/-
`Equivalence r` is a bundled structure that packages the three properties:

- reflexivity of `r`
- symmetry of `r`
- transitivity of `r`
-/
variable (r_equiv : Equivalence r)

example : r a a := by exact r_equiv.refl _
example : r a b → r b a := by exact r_equiv.symm
example : r a b → r b c → r a c := by exact r_equiv.trans
end

/-
As a running example, we can define an equivalence relation on `ℕ × ℕ`,
which ultimately gives us the construction of integers from natural numbers.
-/
section

-- tag as `simp` lemma for auto decomposition
@[simp] def NN_r (z w : ℕ × ℕ) : Prop := z.1 + w.2 = z.2 + w.1
def NN_equiv : Equivalence NN_r where
  refl := by intro _; rw [NN_r, add_comm]
  symm := by
    intro ⟨z1, z2⟩ ⟨w1, w2⟩ h
    simp at *
    linarith only [h]
  trans := by
    intro ⟨z1, z2⟩ ⟨w1, w2⟩ ⟨u1, u2⟩ h1 h2
    simp at *
    linarith only [h1, h2]

/-
In mathmatics we often denote equivalence relations by `~`.
In Lean, we can also use `≈` as notation for equivalence relations,
once we register the `Setoid` instance for `α`.

The `Setoid` typeclass is a bundle of

- an equivalence relation `r` on `α`
- the proof that `r` is an equivalence relation.
-/
#check Setoid

instance NN_setoid : Setoid (ℕ × ℕ) where
  r := NN_r
  iseqv := NN_equiv

@[simp] lemma NN0_r_of_equiv {z w : ℕ × ℕ} : z ≈ w ↔ NN_r z w := by rfl

example : (1, 2) ≈ (2, 3) := by simp
example (n m p : ℕ) : (n, m) ≈ (n + p, m + p) := by
  simp; ring

/-
From a `Setoid α` instance `s`, we can define the quotient type `Quotient s`.
The elements of `Quotient s`, are mathematically viewed as equivalence classes of `α`.
-/
#check Quotient

/-
For example, the following defines the type `Z` of integers as the quotient of `ℕ × ℕ`
by the equivalence relation `NN_r`.
-/
def Z := Quotient NN_setoid

/-
Inductive types have their introduction rules and elimination rules.
Similar self-evident rules exist for quotient types.

The introduction rule is given by `Quotient.mk`, essentially a map from `α → Quotient s`.
-/
example : Z := Quotient.mk NN_setoid (3, 5)
example : Z := Quotient.mk' (3, 5) -- this version detects the `Setoid` instance in the context
example : Z := ⟦(3, 5)⟧ -- anonymous "constructor" for `Quotient`

/-
Two elements of an inductive type are equal,
iff they are constructed from the same data using the same constructor.

This is different in the case of quotient types, since the same equivalence class
can be represented by different elements of `α`.

So quotient types need an additional "soundness" axiom to clarify when two quotient elements,
coming from two possibly different representatives in `α`, are equal.
-/
#check Quotient.sound

#check Quotient.lift
#check Quotient.ind
#check Quotient.mk



end
