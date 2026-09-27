import Mathlib
import Submission.Work.PL.Approx.Defs

namespace Work.PL.Approx.Continuous

open Metric

/-- The point `x + t • (y - x)` on the segment from `x` to `y` is no farther from `x` than `y` is,
for `t ∈ [0,1]`. -/
lemma dist_add_smul_sub_le {n : ℕ} (x y : PL.E n) {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    dist (x + t • (y - x)) x ≤ dist y x := by
  have hsub : x + t • (y - x) - x = t • (y - x) := by abel
  rw [dist_eq_norm, dist_eq_norm, hsub, norm_smul, Real.norm_eq_abs, abs_of_nonneg h0]
  nlinarith [norm_nonneg (y - x)]

end Work.PL.Approx.Continuous
