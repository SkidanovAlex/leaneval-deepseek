import Mathlib

namespace Work.ZeroDensity.Montgomery

/-- Splitting the complex power of a positive integer: for `n ≥ 1` and real `σ`, `t`,
`n^{-(σ+it)} = n^{-σ} · n^{-it}`. -/
theorem cpow_neg_sigma_add_it (n : ℕ) (hn : 1 ≤ n) (σ t : ℝ) :
    (n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I))
      = (n : ℂ) ^ (-(σ : ℂ)) * (n : ℂ) ^ (-((t : ℂ) * Complex.I)) := by
  have hn0 : (n : ℂ) ≠ 0 := by
    exact_mod_cast (by omega : n ≠ 0)
  have h : -((σ : ℂ) + (t : ℂ) * Complex.I)
      = -(σ : ℂ) + -((t : ℂ) * Complex.I) := by ring
  rw [h, Complex.cpow_add _ _ hn0]

end Work.ZeroDensity.Montgomery
