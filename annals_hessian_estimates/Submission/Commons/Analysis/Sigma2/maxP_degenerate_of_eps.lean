import Mathlib.Algebra.Order.Archimedean.Real.Basic

namespace Commons.Analysis.Sigma2

theorem maxP_degenerate_of_eps {eps b D A : ℝ} (hb : 0 < b) (hD : 0 ≤ D) (heps : 0 ≤ eps)
    (h : A + (eps / b) * D - (1 / b ^ 2) * D ≤ 0) : A - (1 / b ^ 2) * D ≤ 0 := by
  have hb2 : (0:ℝ) < b ^ 2 := pow_pos hb 2
  have h1 : 0 ≤ (eps / b) * D := mul_nonneg (div_nonneg heps (le_of_lt hb)) hD
  linarith

end Commons.Analysis.Sigma2