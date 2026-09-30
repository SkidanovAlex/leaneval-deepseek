import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

theorem final_combine {r : ℕ} {dr C P vL : ℝ} (hdr : 1 ≤ dr) (hC : 2 ≤ C)
    (hP : dr⁻¹ ≤ P) (hL : 0 ≤ vL) :
    C + 2*P ≤ vL + 2*dr*C*P := by
  have hdrpos : 0 < dr := lt_of_lt_of_le zero_lt_one hdr
  have h1 : 1 ≤ dr * P := by
    have h := mul_le_mul_of_nonneg_left hP (le_of_lt hdrpos)
    rwa [mul_inv_cancel₀ (ne_of_gt hdrpos)] at h
  have hCn : 0 ≤ C := by linarith
  have hPn : 0 ≤ P := by
    have : 0 < dr⁻¹ := inv_pos.mpr hdrpos
    linarith
  have h2 : C ≤ dr * C * P := by
    have h := mul_le_mul_of_nonneg_left h1 hCn
    nlinarith [h]
  have h3 : 2 * P ≤ dr * C * P := by
    have hdrC : 2 ≤ dr * C := by nlinarith
    have h := mul_le_mul_of_nonneg_right hdrC hPn
    nlinarith [h]
  linarith [hL]

end Work.BW
