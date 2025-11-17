import Mathlib

/-

## Abstract Algebra

In this section, we illustrate the usage of
some basic algebraic structures predefined in Mathlib.
-/

/-
### Groups

#### Objects
-/

section
/-
A `Semigroup` is a type with an associative binary operation `*`.
-/
variable (G : Type*) [Semigroup G] (a b c : G)
example : a * (b * c) = (a * b) * c := by rw [mul_assoc]

/-
An `AddSemigroup` is exactly the same as `Semigroup`, only with additive `+` notation.
-/
variable (A : Type*) [AddSemigroup A] (a b c : A)
example : a + (b + c) = (a + b) + c := by rw [add_assoc]

/-
Note that using the notation of `+` does not necessarily mean that the operation is commutative.
To this end, we have `CommSemigroup` and `AddCommSemigroup`.
-/
#check CommSemigroup
#check mul_comm

#check AddCommSemigroup
#check add_comm

end

section
/-
A `Monoid` is a `Semigroup` with an identity element `1`.
-/
variable (G : Type*) [Monoid G] (a b c : G)

example : a * 1 = a := by rw [mul_one]
example : 1 * a = a := by rw [one_mul]

/- `Monoid` additionaly enables power notation `a ^ n` for natural number `n`. -/
#check Monoid.npow
example : a ^ 0 = 1 := by rw [pow_zero]
example (n : ℕ) : a ^ (n + 1) = a ^ n * a := by rw [pow_succ]

/- We are not prepared to prove this until we talk about induction. -/
#check one_pow

/- `AddMonoid` is the additive version of `Monoid`. -/
variable (A : Type*) [AddMonoid A] (a b c : A)
example : a + 0 = a := by rw [add_zero]
example : 0 + a = a := by rw [zero_add]
example : 0 • a = 0 := by rw [zero_smul]
example (n : ℕ) : (n + 1) • a = n • a + a := by rw [succ_nsmul]

end

/-
For commutative monoids, we have `CommMonoid` and `AddCommMonoid`.
-/
#check CommMonoid
#check AddCommMonoid

section
/-
A `Group` is a `Monoid` where every element has an inverse.
-/
variable (G : Type*) [Group G] (a b c : G)
#check a⁻¹
example : a⁻¹ * a = 1 := by rw [inv_mul_cancel]
example : a * a⁻¹ = 1 := by rw [mul_inv_cancel]

example : (a * b)⁻¹ = b⁻¹ * a⁻¹ := by rw [mul_inv_rev]

/- wheelchair tactic for groups -/
#help tactic group
example : (a^3 * b⁻¹)⁻¹ = b * a⁻¹ * (a^2)⁻¹  := by
  group

end
