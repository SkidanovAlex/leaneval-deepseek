import Mathlib
import Submission.Work.BMF.halasz_series_aux

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF

/-- `Kser f s = Σ_n f n · log n · n^{-s}` is the Dirichlet series with coefficients
`n ↦ log n · f n`, i.e. it is `LSeries (LSeries.logMul f) s` (the negative logarithmic
derivative series of `LSeries f`). -/
theorem Kser_eq_LSeries_logMul (f : ℕ → ℂ) (s : ℂ) :
    Work.BMF.Kser f s = LSeries (LSeries.logMul f) s := by
  simp only [Work.BMF.Kser]
  rw [show LSeries (LSeries.logMul f) s = ∑' n, LSeries.term (LSeries.logMul f) s n from rfl]
  refine tsum_congr (fun n => ?_)
  rcases eq_or_ne n 0 with rfl | hn
  · rw [LSeries.term_zero]
    simp
  · rw [LSeries.term_of_ne_zero hn, LSeries.logMul, Complex.cpow_neg, ← Complex.natCast_log]
    ring

end Work.BMF
