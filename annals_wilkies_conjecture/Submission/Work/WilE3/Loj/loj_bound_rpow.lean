import Mathlib

namespace Work.WilE3.Loj

theorem loj_bound_rpow {c κ u r : ℝ} (hc : 0 < c) (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) (hu : 0 ≤ u)
    (hr : 0 ≤ r) (h : r ≤ u ^ (1 - κ) / (c * (1 - κ))) :
    (c * (1 - κ)) ^ (1 / (1 - κ)) * r ^ (1 / (1 - κ)) ≤ u := by
  have _ := hκ0
  have hs : 0 < 1 - κ := by linarith
  have hA : 0 < c * (1 - κ) := mul_pos hc hs
  -- multiply the hypothesis by the positive factor c * (1 - κ)
  have hprod : c * (1 - κ) * r ≤ u ^ (1 - κ) := by
    have hm := mul_le_mul_of_nonneg_left h (le_of_lt hA)
    rwa [mul_div_cancel₀ _ (ne_of_gt hA)] at hm
  calc (c * (1 - κ)) ^ (1 / (1 - κ)) * r ^ (1 / (1 - κ))
      = (c * (1 - κ) * r) ^ (1 / (1 - κ)) := (Real.mul_rpow (le_of_lt hA) hr).symm
    _ ≤ (u ^ (1 - κ)) ^ (1 / (1 - κ)) := by
        apply Real.rpow_le_rpow (mul_nonneg (le_of_lt hA) hr) hprod
        exact div_nonneg zero_le_one (le_of_lt hs)
    _ = u ^ ((1 - κ) * (1 / (1 - κ))) := (Real.rpow_mul hu _ _).symm
    _ = u ^ (1 : ℝ) := by rw [mul_one_div_cancel (ne_of_gt hs)]
    _ = u := Real.rpow_one u

end Work.WilE3.Loj
