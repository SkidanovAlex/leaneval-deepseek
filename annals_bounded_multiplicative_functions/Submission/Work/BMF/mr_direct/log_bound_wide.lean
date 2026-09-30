import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.mr_direct

theorem log_bound_wide {x Y : ℝ} (hx : 16 ≤ x) (hxY : x ≤ Y)
    (hlog : Real.log Y ≤ 8 * Real.log x) :
    Real.log 4 + Real.log 4 / Real.log x + Real.log 4 * Real.log (Real.log Y / Real.log x) ≤ 16 := by
  have hx0 : (0:ℝ) < x := by linarith
  -- log x ≥ 4 log 2 > 2
  have hlogx_ge2 : 2 ≤ Real.log x := by
    have h16 : Real.log 16 ≤ Real.log x := Real.log_le_log (by norm_num) hx
    have h16eq : Real.log 16 = 4 * Real.log 2 := by
      rw [show (16:ℝ) = 2^4 by norm_num, Real.log_pow]; norm_num
    linarith [Real.log_two_gt_d9]
  have hlogx_pos : 0 < Real.log x := by linarith
  -- log 4 ≤ 2
  have hlog4_le : Real.log 4 ≤ 2 := by
    have heq : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]; norm_num
    have h2 : Real.log 2 ≤ (2:ℝ) - 1 := Real.log_le_sub_one_of_pos (by norm_num)
    linarith
  have hlog4_nonneg : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  -- 1 ≤ log Y / log x ≤ 8
  have hratio_le : Real.log Y / Real.log x ≤ 8 := by
    rw [div_le_iff₀ hlogx_pos]; exact hlog
  have hlogx_le_logY : Real.log x ≤ Real.log Y := Real.log_le_log hx0 hxY
  have hratio_ge1 : 1 ≤ Real.log Y / Real.log x := by
    rw [le_div_iff₀ hlogx_pos]; simpa using hlogx_le_logY
  have hratio_pos : 0 < Real.log Y / Real.log x := by linarith
  -- log (log Y / log x) ≤ log 8 ≤ 3
  have hlog_ratio_le : Real.log (Real.log Y / Real.log x) ≤ 3 := by
    have h1 : Real.log (Real.log Y / Real.log x) ≤ Real.log 8 := Real.log_le_log hratio_pos hratio_le
    have h2 : Real.log 8 ≤ 3 := by
      have heq : Real.log 8 = 3 * Real.log 2 := by
        rw [show (8:ℝ) = 2^3 by norm_num, Real.log_pow]; norm_num
      have h3 : Real.log 2 ≤ (2:ℝ) - 1 := Real.log_le_sub_one_of_pos (by norm_num)
      linarith
    linarith
  have hlog_ratio_nonneg : 0 ≤ Real.log (Real.log Y / Real.log x) := Real.log_nonneg hratio_ge1
  have hterm : Real.log 4 * Real.log (Real.log Y / Real.log x) ≤ 6 := by
    have hm := mul_le_mul hlog4_le hlog_ratio_le hlog_ratio_nonneg (by norm_num : (0:ℝ) ≤ 2)
    linarith
  have hdiv_le : Real.log 4 / Real.log x ≤ 1 := by
    rw [div_le_one hlogx_pos]; linarith
  linarith

end Work.BMF.mr_direct
