import Mathlib

/--
Fermat's Last Theorem: if n > 2,
then there are no positive integer solutions to a^n + b^n = c^n.
-/
theorem FLT (n : ℕ) (hn : n > 2) (a b c : ℕ) : a ≠ 0 → b ≠ 0 → c ≠ 0 → a^n + b^n ≠ c^n := by
  sorry

def TendsTo (a : ℕ → ℝ) (t : ℝ) : Prop :=
  ∀ ε > 0, ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → |a n - t| < ε

example : TendsTo (fun _ ↦ 998244353) 998244353 := by
  unfold TendsTo
  intro ε hε
  use 19260817
  intro n hn
  simp [hε]
