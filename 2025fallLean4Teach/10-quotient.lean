/-
# Quotients

After building up the theory of groups, homorphisms, and subgroups,
we are now ready to define quotient groups.

In fact, quotients are so fundamental that
Lean makes them a primitive way of constructing new types.
[IGNORE] Other reasons including the foundation of `funext`,
see [The Lean Language Manual](https://lean-lang.org/doc/reference/latest/The-Type-System/Quotients/#quotient-funext).

We shall first illustrate the general quotient construction in Lean,
and then specialize it to quotient groups.

At the end of the journey, we show the first isomorphism theorem for groups as promised.
-/
import Mathlib

/-
## Quotient types

We still build up the theory from sets.

### `Equivalence`, `Setoid`, quotient types

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

-- tag as `simp` lemma for auto decomposition
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
### The universal properties

Quotient types behave similarly to inductive types.
But there is a key difference:
Inductive types have their internal data directly accessible
(via pattern matching and its elimination rules),
while the internal data of a quotient type is hidden behind the equivalence relation.

The introduction rule of a Quotient type is given by `Quotient.mk`,
essentially a map from `α → Quotient s`.
-/
#check Quotient.mk

example : Z := Quotient.mk NN_setoid (3, 5)
example : Z := Quotient.mk' (3, 5) -- this version detects the `Setoid` instance in the context
example : Z := ⟦(3, 5)⟧ -- anonymous "constructor" for `Quotient`

/-
Two elements of an inductive type are equal,
iff they are constructed from the same data using the same constructor.

This is different in the case of quotient types,
since the same equivalence class
can be represented by different elements of `α`.

So quotient types need an additional "soundness" axiom
to clarify when two quotient elements,
coming from two possibly different representatives in `α`, are equal.
It is an axiom in Lean, hence the equality is not definitional.
-/
#check Quotient.sound

example : (⟦(3, 5)⟧ : Z) = ⟦(4, 6)⟧ := by
  apply Quotient.sound
  simp

/-
The following two self-evident rules are the elimination rules
for quotient types in `Sort*` and `Prop` respectively.

`Quotient.lift` is essentially the universal property of quotients:
It allows us to define functions out of a quotient type `Quotient s`
by defining them on representatives in `α`, once we verify that the function
respects the equivalence relation `s.r`.

[IGNORE]
Note that `Quotient.lift` does not allow a motive depending on the input,
since the well-definedness needs to be verified in the same type.
Quotient types do have a dependent recursor, called `Quotient.rec`.
With a more complicated type signature,
it is more "tricky" to use and not often needed in practice.
-/
#check Quotient.lift

/- The universal property, true by definition -/
#check Quotient.lift_mk

/- As an example, we define the negation function on integers. -/
def Z_neg : Z → Z := by
  apply Quotient.lift (fun ⟨z1, z2⟩ ↦ ⟦(z2, z1)⟧ : ℕ × ℕ → Z)
  intro ⟨z1, z2⟩ ⟨w1, w2⟩ h
  dsimp
  apply Quotient.sound
  simp at *
  linarith only [h]

/- Activate the `-` notation for `Z`. -/
instance : Neg Z := ⟨Z_neg⟩

/-
Define the multiplication on `Z`.
It uses `Quotient.lift₂`, which is for binary operations on quotient types.
Challenge: Define Quotient.lift₂ by yourself!
-/
#check Quotient.lift₂
def Z_mul : Z → Z → Z := by
  apply Quotient.lift₂
    (fun ⟨z1, z2⟩ ⟨w1, w2⟩ ↦ ⟦(z1 * w1 + z2 * w2, z1 * w2 + z2 * w1)⟧ : ℕ × ℕ → ℕ × ℕ → Z)
  intro ⟨z1, z2⟩ ⟨w1, w2⟩ ⟨u1, u2⟩ ⟨v1, v2⟩ h1 h2
  dsimp
  apply Quotient.sound
  simp at *
  nlinarith only [h1, h2]

/- Activate the `*` notation for `Z`. -/
instance : Mul Z := ⟨Z_mul⟩

/-
`Quotient.ind` is also an elimination rule for quotient types,
but it focuses on proving propositions about quotient types.
As `Prop` is proof-irrelevant,
a different proof for different representatives does not matter.
Hence, the equivalence relation does not need to be verified here.
([IGNORE] and a motive depending on the input is allowed here)

In effect, `Quotient.ind` states that we may assume any quotient element
is constructed from a representative in `α`
when proving propositions about quotient types.
Or, the canonical map `α → Quotient s` is surjective when used in `Prop`.
-/
#check Quotient.ind

/- As an example, we prove that `(-z) * (-z) = z * z` for any integer `z`. -/
example : (z : Z) → (-z) * (-z) = z * z := by
  apply Quotient.ind
  intro ⟨z1, z2⟩
  apply Quotient.sound
  simp; ring

/-
In tactic mode, `induction' ... using Quotient.ind with ...` is often used.

You should convince yourself that this in effect act like
an `rcases ... with ...` decomposition,
and `using Quotient.ind` emphasizes that
we are using the elimination rule for quotients.
The full use of `induction'` can be touched only
when inductive types are fully covered.
-/
#help tactic induction'
example (z : Z) : (-z) * (-z) = z * z := by
  induction' z using Quotient.ind with z
  rcases z with ⟨z1, z2⟩
  apply Quotient.sound
  simp; ring

/-
There is also `Quotient.ind₂` for proving propositions about two quotient elements.
Many other variations for `Quotient.ind` and `Quotient.lift` exist as well.
-/
#check Quotient.ind₂
#check Quotient.ind'
#check Quotient.liftOn
#check Quotient.liftOn'
#check Quotient.inductionOn
#check Quotient.inductionOn'

end

/-
### Quotient types under morphisms
-/

section

/- Lifting functions does not change its range. [TODO] -/
#check Set.range_quotient_lift

end

/-
## Quotient groups

We are now ready to define quotient groups.
-/
section
variable (G : Type*) [Group G] (H : Subgroup G)

/-
### Left coset relation

The notation `G ⧸ H` is, mathematically, the left cosets of `H` in `G`.
In Lean, it is defined as the quotient type of `G`
by the left coset equivalence relation induced by `H`.
-/
#check QuotientGroup.leftRel H

/-
The definition of `QuotientGroup.leftRel H` is
hidden deep inside Mathlib for general usability.
Practically, we only need to know its meaning (up to logical equivalence).
[IGNORE] See the appendix at the end of this file for the definitional one.
-/
example (a b : G) : (QuotientGroup.leftRel H) a b ↔ a⁻¹ * b ∈ H :=
  QuotientGroup.leftRel_apply

/-
This in turn allows us to define the left coset type `G ⧸ H`
via quotient types.
-/
#synth HasQuotient G (Subgroup G)
#check G ⧸ H

/-
### The group structure

With the normality of `H`, the group structure on `G ⧸ H`
is induced from that of `G`.
-/
variable [H.Normal]

/-
We illustrate how to define the group structure on `G ⧸ H` manually here,
from `Semigroup` to `Monoid` to `Group`.

Note that it is just an illustration; in practice, you may wish to use the
`Group.ofLeftAxioms` constructor from Mathlib instead.
-/

def mySemigroup : Semigroup (G ⧸ H) where

  mul := by
    apply Quotient.lift₂ (fun (a b : G) ↦ ⟦a * b⟧)
    intro a1 a2 b1 b2 h1 h2
    apply Quotient.sound
    change QuotientGroup.leftRel H a1 b1 at h1
    change QuotientGroup.leftRel H a2 b2 at h2
    change QuotientGroup.leftRel H (a1 * a2) (b1 * b2)
    rw [QuotientGroup.leftRel_apply] at h1 h2 ⊢

    have hn : H.Normal := inferInstance; rcases hn with ⟨hn⟩
    specialize hn (a1⁻¹ * b1) h1 a2⁻¹
    simp only [inv_inv] at hn

    haveI : (a1 * a2)⁻¹ * (b1 * b2) =
        a2⁻¹ * (a1⁻¹ * b1) * a2 * (a2⁻¹ * b2) := by group
    rw [this]

    apply mul_mem hn h2

  mul_assoc := by
    intro a b c
    induction' a using Quotient.ind with a
    induction' b using Quotient.ind with b
    induction' c using Quotient.ind with c
    apply Quotient.sound
    rw [mul_assoc]
    apply refl

#synth Semigroup (G ⧸ H)
example : (QuotientGroup.Quotient.group H).toSemigroup = mySemigroup G H := by rfl

def myMonoid : Monoid (G ⧸ H) where
  one := ⟦1⟧
  one_mul := by
    intro a
    induction' a using Quotient.ind with a
    apply Quotient.sound; dsimp
    rw [one_mul]
    apply refl
  mul_one := by
    intro a
    induction' a using Quotient.ind with a
    apply Quotient.sound; dsimp
    rw [mul_one]
    apply refl

/- [TODO] For unknown reason we can't show a definitional equality here. -/
#synth Monoid (G ⧸ H)
example : (QuotientGroup.Quotient.group H).toMonoid = myMonoid G H := by ext; rfl

def myGroup : Group (G ⧸ H) where
  inv := by
    apply Quotient.lift (fun a ↦ ⟦a⁻¹⟧)
    intro a1 a2 h
    apply Quotient.sound
    change QuotientGroup.leftRel H a1 a2 at h
    change QuotientGroup.leftRel H a1⁻¹ a2⁻¹
    rw [QuotientGroup.leftRel_apply] at h ⊢
    simp only [inv_inv]

    replace h := inv_mem h
    simp at h ⊢

    have hn : H.Normal := inferInstance; rcases hn with ⟨hn⟩
    specialize hn (a2⁻¹ * a1) h a2
    simp at hn; exact hn

  div a b := a * b⁻¹

  inv_mul_cancel := by
    intro a
    induction' a using Quotient.ind with a
    apply Quotient.sound; simp

/- [TODO] For unknown reason we can't show a definitional equality here. -/
#synth Group (G ⧸ H)
example : QuotientGroup.Quotient.group H = myGroup G H := by ext; rfl

/- the Mathlib instance for `Group (G ⧸ H)` -/
#synth Group (G ⧸ H)

/- the canonical group epimorphism from `G` to `G ⧸ H` -/
#check QuotientGroup.mk'

end

/-
### Lifting a group homomorphism

We now need to upgrade `Quotient.lift` to respect the group structure,
so that we can define morphisms between quotient groups via universal properties.
-/

section

variable {G M: Type*} [Group G] [Group M] (N : Subgroup G) [N.Normal]

/-
Now we upgrade `Quotient.lift` to respect the group structure.
-/
variable (ϕ : G →* M)

example (HN : N ≤ ϕ.ker) : (G ⧸ N) →* M where
  toFun := by
    apply Quotient.lift ϕ
    intro a b h
    change QuotientGroup.leftRel N a b at h
    rw [QuotientGroup.leftRel_apply] at h
    haveI := HN h; simp at this
    exact eq_of_inv_mul_eq_one this
  map_mul' := by
    intro a b
    induction' a using Quotient.ind with a
    induction' b using Quotient.ind with b
    repeat rw [Quotient.lift_mk]
    apply map_mul
  map_one' := by
    conv => lhs; rhs; change ⟦1⟧
    rw [Quotient.lift_mk]
    apply map_one

#check QuotientGroup.lift

/-
### Quotient groups under morphisms
-/

/- [TODO] Upgrade `Set.range_quotient_lift` to groups. -/
example (HN : N ≤ ϕ.ker) : (QuotientGroup.lift N ϕ HN).range = ϕ.range := by sorry

/-
### The first isomorphism theorem

Finally, we come to our grand finale.
-/

/- Now we can lift the group homomorphisms `ϕ : G →* M` to `G ⧸ ker ϕ →* M`. -/
example : G ⧸ ϕ.ker →* M := QuotientGroup.lift ϕ.ker ϕ (by simp)

/- The first isomorphism theorem: `G ⧸ ker ϕ ≃* range ϕ`. -/
#check QuotientGroup.quotientKerEquivRange

end

/-
## Appendix: tracing down the definition of coset relations
-/

section

variable {G : Type*} [Group G] (H : Subgroup G)

example (a b : G) : QuotientGroup.leftRel H a b = (∃ (h : H.op), b * (h : Gᵐᵒᵖ).unop = a) := calc
  QuotientGroup.leftRel H a b
    = (QuotientGroup.leftRel H).r a b := rfl
  _ = (MulAction.orbitRel H.op G).r a b := rfl
  _ = (a ∈ MulAction.orbit H.op b) := rfl
  _ = (∃ (h : H.op), h • b = a) := rfl
  _ = (∃ (h : H.op), b * (h : Gᵐᵒᵖ).unop = a) := rfl

example (a b : G) : QuotientGroup.rightRel H a b = (∃ (h : H), h * b = a) := calc
  QuotientGroup.rightRel H a b
    = (QuotientGroup.rightRel H).r a b := rfl
  _ = (MulAction.orbitRel H G).r a b := rfl
  _ = (a ∈ MulAction.orbit H b) := rfl
  _ = (∃ (h : H), h • b = a) := rfl
  _ = (∃ (h : H), h * b = a) := rfl

end
