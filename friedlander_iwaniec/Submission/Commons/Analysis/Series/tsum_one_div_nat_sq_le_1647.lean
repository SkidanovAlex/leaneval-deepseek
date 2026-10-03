import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.PSeries
import Submission.Commons.Analysis.Series.tail_inv_sq_le

namespace Commons.Analysis.Series

/-- Mathlib's closed form `∑_{n} 1/n² = π²/6` gives the explicit numerical bound.
The bound follows from `π < 3.141593`, so that `π²/6 < 1647/1000`. -/
theorem tsum_one_div_nat_sq_le_1647 :
    (∑' n : ℕ, (1 : ℝ) / (n : ℝ)^2) ≤ 1647 / 1000 := by
  rw [hasSum_zeta_two.tsum_eq]
  nlinarith [Real.pi_lt_d6, Real.pi_pos]

end Commons.Analysis.Series