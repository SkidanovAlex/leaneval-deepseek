import Mathlib
import Submission.Commons.Analysis.Asymptotics.geom_sum_range_le

namespace Commons.Analysis.Real

theorem sum_Ico_pow_mul_le {C r : ℝ} (hC : 0 ≤ C) (hr0 : 0 ≤ r) (hr1 : r < 1) (n m : ℕ) :
    ∑ j ∈ Finset.Ico n m, C * r ^ j ≤ C * r ^ n / (1 - r) := by
  have hgeom : ∑ k ∈ Finset.range (m - n), r ^ k ≤ 1 / (1 - r) :=
    Commons.Analysis.Asymptotics.geom_sum_range_le hr0 hr1 (m - n)
  have hnn : 0 ≤ C * r ^ n := mul_nonneg hC (pow_nonneg hr0 n)
  have hsum : ∑ j ∈ Finset.Ico n m, C * r ^ j
      = C * r ^ n * ∑ k ∈ Finset.range (m - n), r ^ k := by
    rw [Finset.sum_Ico_eq_sum_range]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [pow_add]
    ring
  rw [hsum]
  calc C * r ^ n * ∑ k ∈ Finset.range (m - n), r ^ k
      ≤ C * r ^ n * (1 / (1 - r)) := mul_le_mul_of_nonneg_left hgeom hnn
    _ = C * r ^ n / (1 - r) := by ring

end Commons.Analysis.Real
