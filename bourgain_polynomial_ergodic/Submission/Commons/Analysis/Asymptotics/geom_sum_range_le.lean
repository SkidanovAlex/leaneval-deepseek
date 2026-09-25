import Mathlib
import Submission.Commons.Analysis.Asymptotics.geom_finset_le

namespace Commons.Analysis.Asymptotics

theorem geom_sum_range_le {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (n : ℕ) :
    (∑ i ∈ Finset.range n, r ^ i) ≤ 1 / (1 - r) := by
  exact geom_finset_le hr0 hr1 (Finset.range n)

end Commons.Analysis.Asymptotics
