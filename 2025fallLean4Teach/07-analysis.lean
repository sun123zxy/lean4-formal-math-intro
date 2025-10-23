import Mathlib

def TendsTo (a : ℕ → ℝ) (t : ℝ) : Prop :=
  ∀ ε > 0, ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → |a n - t| < ε

/-- The limit of the constant sequence with value `c` is `c`. -/
theorem tendsTo_const (c : ℝ) : TendsTo (fun _ ↦ c) c := by
  unfold TendsTo
  intro ε hε
  use 1
  intro n hn
  simp [hε]

/-- If `a(n)` tends to `t` then `-a(n)` tends to `-t`. -/
theorem tendsTo_neg {a : ℕ → ℝ} {t : ℝ} (ha : TendsTo a t) : TendsTo (fun n ↦ -a n) (-t) := by
  unfold TendsTo
  intro ε hε
  specialize ha ε hε
  rcases ha with ⟨n₀, hn₀⟩
  use n₀
  intro n hn
  specialize hn₀ n hn
  simp
  -- what theorems should I use?
  rw [← abs_neg, add_comm]
  simp
  -- what theorems should I use?
  rw [← sub_eq_add_neg]
  exact hn₀

theorem tendsTo_add {a b : ℕ → ℝ} {A : ℝ} {B : ℝ} (ha : TendsTo a A) (hb : TendsTo b B) :
    TendsTo (fun n => a n + b n) (A + B) := by
  intro ε hε
  specialize ha (ε / 2) (by linarith)
  specialize hb (ε / 2) (by linarith)
  rcases ha with ⟨n₀, ha⟩
  rcases hb with ⟨m₀, hb⟩
  use max n₀ m₀
  intro n hn
  rw [max_le_iff] at hn
  specialize ha n (by linarith)
  specialize hb n (by linarith)
  simp
  -- common tactic: eliminate abs to make use of `linarith`
  -- what theorems should I use?
  rw [abs_lt] at ha hb ⊢
  constructor
  · linarith
  · linarith

theorem tendsTo_sub {a b : ℕ → ℝ} {A : ℝ} {B : ℝ} (ha : TendsTo a A) (hb : TendsTo b B) :
    TendsTo (fun n => a n - b n) (A - B) := by
  haveI := tendsTo_add ha (tendsTo_neg hb)
  -- figure out what happened here
  congr

theorem tendsTo_mul (a b : ℕ → ℝ) (A B : ℝ) (ha : TendsTo a A) (hb : TendsTo b B) :
    TendsTo (fun n ↦ a n * b n) (A * B) := by
  sorry

theorem tendsTo_sandwich {a b c : ℕ → ℝ} {L : ℝ} (ha : TendsTo a L) (hc : TendsTo c L)
    (hab : ∀ n, a n ≤ b n) (hbc : ∀ n, b n ≤ c n) : TendsTo b L := by
  unfold TendsTo
  intro ε hε
  specialize ha ε hε
  specialize hc ε hε
  rcases ha with ⟨n₀, hn₀⟩
  rcases hc with ⟨m₀, hm₀⟩
  use max n₀ m₀
  intro n hn
  rw [max_le_iff] at hn
  specialize hab n
  specialize hn₀ n (by linarith)
  specialize hm₀ n (by linarith)
  specialize hbc n
  rw [abs_lt] at hn₀ hm₀ ⊢
  constructor
  · linarith
  · linarith

theorem tendsTo_unique (a : ℕ → ℝ) (s t : ℝ) (hs : TendsTo a s) (ht : TendsTo a t) : s = t := by
  have hst := tendsTo_sub hs ht
  unfold TendsTo at hst
  simp at hst
  by_contra! hneq
  have hstp : 0 < |t - s| := by
    rw [abs_pos]
    contrapose! hneq
    apply_fun fun x ↦ x + s at hneq
    simp at hneq
    symm
    exact hneq
  specialize hst |t - s| hstp
  rcases hst with ⟨n₀, hn₀⟩
  specialize hn₀ n₀ (by linarith)
  linarith

def contAt (f : ℝ → ℝ) (x₀ : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x, |x - x₀| < δ → |f x - f x₀| < ε

def contAt_seq (f : ℝ → ℝ) (x₀ : ℝ) : Prop :=
  ∀ a : ℕ → ℝ, TendsTo a x₀ → TendsTo (f ∘ a) (f x₀)

/- sequential definition equivialence -/
theorem contAt_iff_seq (f : ℝ → ℝ) (x₀ : ℝ) :
    contAt f x₀ ↔ contAt_seq f x₀ := by
  constructor
  · intro hf a ha
    intro ε hε
    rcases hf ε hε with ⟨δ, hδ, hδf⟩
    rcases ha δ hδ with ⟨n₀, hn₀⟩
    use n₀
    intro n hn
    specialize hn₀ n hn
    specialize hδf (a n) hn₀
    exact hδf
  · contrapose
    intro hnfcont hnfseq
    unfold contAt at hnfcont
    push_neg at hnfcont
    rcases hnfcont with ⟨ε, hε, hnf⟩

    sorry

def cont (f : ℝ → ℝ) : Prop := ∀ x₀ : ℝ, contAt f x₀

def uconv (f : ℕ → ℝ → ℝ) (f₀ : ℝ → ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ x : ℝ, |f n x - f₀ x| < ε

/-
The uniform limit of a sequence of continuous functions is continuous.
-/
theorem cont_of_cont_of_uconv
    (f : ℕ → ℝ → ℝ) (f_cont : ∀ n : ℕ, cont (f n))
    (f₀ : ℝ → ℝ) (h_uconv : uconv f f₀) : cont f₀ := by
  intro x₀ ε hε
  rcases h_uconv (ε / 3) (by linarith [hε]) with ⟨N, hN⟩
  specialize hN N (by linarith)
  rcases f_cont N x₀ (ε / 3) (by linarith [hε]) with ⟨δ, hδ, hδf⟩
  use δ, hδ
  intro x hx
  specialize hδf x hx
  have hNx := hN x
  have hNx₀ := hN x₀
  rw [abs_lt] at hNx hNx₀ hδf ⊢
  constructor
  all_goals linarith [hNx, hNx₀, hδf]
