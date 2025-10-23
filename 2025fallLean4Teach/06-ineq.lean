import Mathlib

#check Eq

#check PartialOrder

/-
## Inequality (first visit)

[TODO] `calc`
-/

section

variable (a b c : ℝ)

#check a < b
#check a ≤ b
#check b ≥ a
#check b > a

#check LE

/- `≥`, `>` are just aliases -/
example : (a < b) = (b > a) := by rfl
example : (a ≤ b) = (b ≥ a) := by rfl

end
