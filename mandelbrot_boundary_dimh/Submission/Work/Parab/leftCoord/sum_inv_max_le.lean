import Mathlib
import Submission.Work.Parab.sumInv.sum_inv_max_le

/-!
# Harmonic bound for `∑ 1 / max R (c m)`

Re-export of `Work.Parab.sumInv.sum_inv_max_le` under the name used by
`Work.Parab.leftCoord.sum_inv_norm_le_log`.
-/

namespace Work.Parab.leftCoord

theorem sum_inv_max_le {c R : ℝ} (hc : 0 < c) (hR : 0 < R) (k : ℕ) :
    ∑ m ∈ Finset.range k, 1 / max R (c * (m : ℝ)) ≤ 1 / R + (1 / c) * (1 + Real.log k) :=
  Work.Parab.sumInv.sum_inv_max_le hc hR k

end Work.Parab.leftCoord
