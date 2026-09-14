import Mathlib
import Submission.Commons.Analysis.Calculus.exists_holder_parametrisation

open MeasureTheory Set

namespace Commons.Analysis.Integral

/-- For `a ≤ b` and `s > -1`, the function `v ↦ |v - c| ^ s` is integrable on `[a, b]`
with respect to Lebesgue measure on `ℝ`.  (Indeed the only possible singular point is
`v = c`, where the integrand behaves like `|v - c| ^ s` with `s > -1`.) -/
theorem integrableOn_abs_sub_rpow_Icc {a b c s : ℝ} (hab : a ≤ b) (hs : -1 < s) :
    MeasureTheory.IntegrableOn (fun v : ℝ => |v - c| ^ s) (Set.Icc a b) MeasureTheory.volume := by
  -- `IntervalIntegrable` over `a..b` with `a ≤ b` is exactly `IntegrableOn` over `Icc a b`.
  refine (intervalIntegrable_iff_integrableOn_Icc_of_le hab (by simp)).mp ?_
  exact Commons.Analysis.Calculus.intervalIntegrable_abs_sub_rpow_of_le hs hab

end Commons.Analysis.Integral
