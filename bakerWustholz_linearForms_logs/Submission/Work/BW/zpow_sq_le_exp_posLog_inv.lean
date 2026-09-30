import Mathlib
import Submission.Work.BW.zpow_sq_le_exp_posLog

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

theorem zpow_sq_le_exp_posLog_inv {a b : ℝ} (hb : 0 < b) (hba : b ^ 2 = a) (N : ℤ) (t : ℝ)
    (hN : N ≤ 0) (ht : -(N : ℝ) / 2 ≤ t) :
    b ^ N ≤ Real.exp (t * a⁻¹.posLog) := by
  have hbpos : 0 < b⁻¹ := inv_pos.mpr hb
  rw [← hba, (inv_pow b 2).symm, posLog_sq_eq hbpos]
  set m := max b⁻¹ 1 with hm
  have hm1 : 1 ≤ m := le_max_right _ _
  have hbm : b⁻¹ ≤ m := le_max_left _ _
  have hmpos : 0 < m := lt_of_lt_of_le one_pos hm1
  rw [show t * (2 * Real.log m) = Real.log m * (2 * t) by ring]
  rw [← Real.rpow_def_of_pos hmpos (2 * t)]
  have hbN : b ^ N = (b⁻¹) ^ (-N) := by rw [inv_zpow' b (-N), neg_neg]
  rw [hbN]
  calc (b⁻¹) ^ (-N) ≤ m ^ (-N) := zpow_le_zpow_left₀ (by omega) (inv_nonneg.mpr hb.le) hbm
    _ = m ^ ((-N : ℤ) : ℝ) := (Real.rpow_intCast m (-N)).symm
    _ ≤ m ^ (2 * t) := Real.rpow_le_rpow_of_exponent_le hm1 (by push_cast; linarith)

end Work.BW
