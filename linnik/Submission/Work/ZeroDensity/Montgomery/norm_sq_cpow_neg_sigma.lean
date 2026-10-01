import Mathlib

namespace Work.ZeroDensity.Montgomery

/-- The squared norm of the complex power `n^{-σ}` of a positive integer is the real power
`n^{-2σ}` (so that `‖b n · n^{-σ}‖² = ‖b n‖² n^{-2σ}`). -/
theorem norm_sq_cpow_neg_sigma (n : ℕ) (hn : 1 ≤ n) (σ : ℝ) :
    ‖(n : ℂ) ^ (-(σ : ℂ))‖ ^ 2 = (n : ℝ) ^ (-(2 * σ)) := by
  rw [Complex.norm_natCast_cpow_of_pos (by omega : 0 < n)]
  simp only [Complex.neg_re, Complex.ofReal_re]
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ n)]
  congr 1
  ring

end Work.ZeroDensity.Montgomery
