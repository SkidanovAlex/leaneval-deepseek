import Mathlib

namespace Work.LinnikAreas

/-- The natural logarithm is unbounded above along the natural numbers:
for every real `M` there is a threshold `q₀` beyond which `log q ≥ M`. -/
theorem log_unbounded_nat (M : ℝ) : ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → M ≤ Real.log (q : ℝ) := by
  refine ⟨Nat.ceil (Real.exp M) + 1, fun q hq => ?_⟩
  have hpos : 0 < (q : ℝ) := by
    have : (0 : ℝ) < Real.exp M := Real.exp_pos M
    have h1 : Real.exp M ≤ (Nat.ceil (Real.exp M) : ℝ) := Nat.le_ceil _
    have h2 : ((Nat.ceil (Real.exp M) + 1 : ℕ) : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
    push_cast at h2
    linarith
  rw [Real.le_log_iff_exp_le hpos]
  have h1 : Real.exp M ≤ (Nat.ceil (Real.exp M) : ℝ) := Nat.le_ceil _
  have h2 : ((Nat.ceil (Real.exp M) + 1 : ℕ) : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  push_cast at h2
  linarith

end Work.LinnikAreas
