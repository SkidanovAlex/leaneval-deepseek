import Mathlib

namespace Work.LinnikAreas.RpowGeom

theorem two_rpow_neg_half_le : (2:ℝ) ^ (-(1/2:ℝ)) ≤ 3/4 := by
  have h2 : (0:ℝ) ≤ 2 := by norm_num
  -- Square both sides: (2^(-1/2))^2 = 1/2 ≤ 9/16 = (3/4)^2.
  have hsq : ((2:ℝ) ^ (-(1/2:ℝ)))^(2:ℝ) = 1/2 := by
    rw [← Real.rpow_mul h2]
    rw [show (-(1/2:ℝ)) * 2 = -1 by norm_num, Real.rpow_neg_one]
    norm_num
  rw [Real.rpow_two] at hsq
  have hle : ((2:ℝ) ^ (-(1/2:ℝ)))^2 ≤ (3/4)^2 := by
    rw [hsq]; norm_num
  exact (abs_le_of_sq_le_sq' hle (by norm_num)).2

end Work.LinnikAreas.RpowGeom
