import Mathlib

namespace Commons.Analysis.Real

theorem div_le_pow_of_le_div {v w t ε : ℝ} {m : ℕ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hv : 1 ≤ v) (hm : 1 ≤ m) (hw : 0 ≤ w) (hvw : w ≤ v ^ m) (ht : v / ε ≤ t) : w / ε ≤ t ^ m := by
  have hε_nonneg : 0 ≤ ε := le_of_lt hε
  have hv_nonneg : 0 ≤ v := by linarith
  have hεm_pos : 0 < ε ^ m := pow_pos hε m
  have hvm_nonneg : 0 ≤ v ^ m := pow_nonneg hv_nonneg m
  have hεm_le : ε ^ m ≤ ε := by
    simpa using pow_le_pow_of_le_one hε_nonneg hε1 hm
  have hve_nonneg : 0 ≤ v / ε := div_nonneg hv_nonneg hε_nonneg
  calc w / ε ≤ v ^ m / ε := div_le_div_of_nonneg_right hvw hε_nonneg
    _ ≤ v ^ m / ε ^ m := div_le_div_of_nonneg_left hvm_nonneg hεm_pos hεm_le
    _ = (v / ε) ^ m := by rw [div_pow]
    _ ≤ t ^ m := pow_le_pow_left₀ hve_nonneg ht m

end Commons.Analysis.Real
