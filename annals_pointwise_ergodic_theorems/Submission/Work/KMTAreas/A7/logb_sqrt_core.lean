import Mathlib

namespace Work.KMTAreas.A7

/-- For `u ≥ 2` one has `Real.logb 2 u ≤ u - 1`.

Since `log 2 ≥ 1/2`, writing `log u = log (u/2) + log 2` and using `log (u/2) ≤ u/2 - 1`
gives `logb 2 u ≤ 2 (u/2 - 1) + 1 = u - 1`. -/
lemma logb_two_le_sub_one {u : ℝ} (hu : 2 ≤ u) : Real.logb 2 u ≤ u - 1 := by
  have hlog2pos : 0 < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hlog2half : (1 : ℝ) / 2 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hu2 : 0 < u / 2 := by linarith
  have hlogu : Real.log u = Real.log (u / 2) + Real.log 2 := by
    have h : u / 2 * 2 = u := by ring
    conv_lhs => rw [← h]
    rw [Real.log_mul (ne_of_gt hu2) (by norm_num : (2 : ℝ) ≠ 0)]
  have hlog_le : Real.log (u / 2) ≤ u / 2 - 1 := Real.log_le_sub_one_of_pos hu2
  have hmain : Real.logb 2 u = Real.log (u / 2) / Real.log 2 + 1 := by
    rw [Real.logb, hlogu, add_div, div_self (ne_of_gt hlog2pos)]
  have hstep : Real.log (u / 2) / Real.log 2 ≤ 2 * (u / 2 - 1) := by
    have h1 : Real.log (u / 2) / Real.log 2 ≤ (u / 2 - 1) / Real.log 2 :=
      div_le_div_of_nonneg_right hlog_le hlog2pos.le
    have h2 : (u / 2 - 1) / Real.log 2 ≤ 2 * (u / 2 - 1) := by
      rw [div_le_iff₀ hlog2pos]
      nlinarith [hlog2half, (by linarith : (0 : ℝ) ≤ u / 2 - 1)]
    linarith
  calc Real.logb 2 u = Real.log (u / 2) / Real.log 2 + 1 := hmain
    _ ≤ 2 * (u / 2 - 1) + 1 := by linarith
    _ = u - 1 := by ring

theorem logb_sqrt_core {c t : ℝ} (hc : 1 ≤ c) (ht : 2 ≤ t)
    (h : t - 1 ≤ c * Real.logb 2 t + 2 * t ^ ((1 : ℝ) / 2)) : t < (2 * c + 3) ^ 2 := by
  by_contra hcon
  rw [not_lt] at hcon
  have ht0 : 0 < t := by linarith
  set u : ℝ := Real.sqrt t with hu
  have hu_sq : u ^ 2 = t := by rw [hu]; exact Real.sq_sqrt ht0.le
  have hc0 : 0 ≤ 2 * c + 3 := by linarith
  have hu_ge : 2 * c + 3 ≤ u := by
    rw [hu]
    exact (Real.le_sqrt hc0 ht0.le).mpr hcon
  have hu2 : 2 < u := by linarith
  have hu_ge1 : 1 ≤ u := by linarith
  have hrpow : t ^ ((1 : ℝ) / 2) = u := by rw [← Real.sqrt_eq_rpow, hu]
  have hlogb : Real.logb 2 t = 2 * Real.logb 2 u := by
    rw [← hu_sq, Real.logb_pow]; ring
  have hkey : u ^ 2 - 2 * u - 1 ≤ 2 * c * Real.logb 2 u := by
    rw [hlogb, hrpow, ← hu_sq] at h
    nlinarith [h]
  have hlogb_nonneg : 0 ≤ Real.logb 2 u := Real.logb_nonneg (by norm_num) hu_ge1
  have hlogb_le : Real.logb 2 u ≤ u - 1 := logb_two_le_sub_one hu2.le
  have hc_le : 2 * c ≤ u - 3 := by linarith
  have hA : 2 * c * Real.logb 2 u ≤ (u - 3) * Real.logb 2 u :=
    mul_le_mul_of_nonneg_right hc_le hlogb_nonneg
  have hB : (u - 3) * Real.logb 2 u ≤ (u - 3) * (u - 1) :=
    mul_le_mul_of_nonneg_left hlogb_le (by linarith)
  have h2 : (u - 3) * (u - 1) < u ^ 2 - 2 * u - 1 := by nlinarith [hu2]
  have hlt : 2 * c * Real.logb 2 u < u ^ 2 - 2 * u - 1 :=
    lt_of_le_of_lt (le_trans hA hB) h2
  linarith [hkey, hlt]

end Work.KMTAreas.A7
