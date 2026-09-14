import Mathlib

namespace Commons.Analysis.Integral

/-- Auxiliary: `|v - 1| ^ (-(1:ℝ)/2) = (Real.sqrt |v - 1|)⁻¹` for `v ≠ 1`. -/
theorem abs_sub_one_rpow_neg_half_eq_inv_sqrt {v : ℝ} (hne : v ≠ 1) :
    |v - 1| ^ (-(1:ℝ)/2) = (Real.sqrt |v - 1|)⁻¹ := by
  have hpos : 0 < |v - 1| := by
    rw [abs_pos]; exact sub_ne_zero.mpr hne
  have h0 : (0:ℝ) ≤ |v - 1| := le_of_lt hpos
  rw [show (-(1:ℝ)/2 : ℝ) = -(1/2) by norm_num, Real.rpow_neg h0]
  rw [← Real.sqrt_eq_rpow]

/-- Auxiliary: for `t > 0`, `t ^ (-(1:ℝ)/2) = (Real.sqrt t)⁻¹`. -/
theorem rpow_neg_half_eq_inv_sqrt {t : ℝ} (ht : 0 < t) :
    t ^ (-(1:ℝ)/2) = (Real.sqrt t)⁻¹ := by
  have h0 : (0:ℝ) ≤ t := le_of_lt ht
  rw [show (-(1:ℝ)/2 : ℝ) = -(1/2) by norm_num, Real.rpow_neg h0]
  rw [← Real.sqrt_eq_rpow]

/-- Elementary logarithmic estimate: `log t ≥ -2 / sqrt t` for `t > 0`. -/
theorem neg_two_inv_sqrt_le_log {t : ℝ} (ht : 0 < t) :
    -2 * (Real.sqrt t)⁻¹ ≤ Real.log t := by
  set s : ℝ := Real.sqrt t with hs
  have hspos : 0 < s := by rw [hs]; exact Real.sqrt_pos.mpr ht
  have hsq : t = s ^ 2 := by
    rw [hs]
    exact (Real.sq_sqrt (le_of_lt ht)).symm
  rw [hsq, Real.log_pow]
  have h1 : Real.log s⁻¹ ≤ s⁻¹ - 1 := Real.log_le_sub_one_of_pos (by positivity)
  rw [Real.log_inv] at h1
  push_cast
  linarith

theorem pi_sqrt_log_bound {v : ℝ} (hv1 : (1:ℝ)/2 ≤ v) (hv2 : v ≤ 2) (hne : v ≠ 1) :
    (Real.pi / Real.sqrt v) * (1 + Real.log (2 * Real.sqrt v / |v - 1|))
      ≤ 100 * |v - 1| ^ (-(1:ℝ)/2) := by
  have hvpos : (0:ℝ) < v := by linarith
  have hspos_v : 0 < Real.sqrt v := Real.sqrt_pos.mpr hvpos
  have hsqrtv_nonneg : 0 ≤ Real.sqrt v := le_of_lt hspos_v
  -- t := |v - 1|
  have htpos : 0 < |v - 1| := by
    rw [abs_pos]; exact sub_ne_zero.mpr hne
  have htle1 : |v - 1| ≤ 1 := by
    rw [abs_le]; exact ⟨by linarith, by linarith⟩
  -- s := sqrt |v-1|
  set s : ℝ := Real.sqrt |v - 1| with hs
  have hspos : 0 < s := by rw [hs]; exact Real.sqrt_pos.mpr htpos
  have hsinv_nonneg : 0 ≤ s⁻¹ := inv_nonneg.mpr (le_of_lt hspos)
  have hsle1 : s ≤ 1 := by rw [hs]; exact Real.sqrt_le_one.mpr htle1
  have hone_le_inv : 1 ≤ s⁻¹ := (one_le_inv₀ hspos).mpr hsle1
  -- rewrite the right-hand side
  have hrhs : |v - 1| ^ (-(1:ℝ)/2) = s⁻¹ := by
    have h0 : (0:ℝ) ≤ |v - 1| := abs_nonneg _
    rw [show (-(1:ℝ)/2 : ℝ) = -(1/2) by norm_num, Real.rpow_neg h0]
    rw [← Real.sqrt_eq_rpow, ← hs]
  -- bounds on sqrt v
  have hsqrtv_le2 : Real.sqrt v ≤ 2 := by
    rw [Real.sqrt_le_iff]
    exact ⟨by norm_num, by nlinarith⟩
  have hsqrtv_ge : (1/2 : ℝ) ≤ Real.sqrt v := by
    rw [Real.le_sqrt (x := (1/2:ℝ)) (y := v) (by norm_num) (le_of_lt hvpos)]
    nlinarith
  -- pi / sqrt v <= 8
  have hpiv : Real.pi / Real.sqrt v ≤ 8 := by
    rw [div_le_iff₀ hspos_v]
    nlinarith [Real.pi_le_four, hsqrtv_ge]
  have hpiv_nonneg : 0 ≤ Real.pi / Real.sqrt v := div_nonneg Real.pi_pos.le hsqrtv_nonneg
  -- log bounds
  have hlog_num : Real.log (2 * Real.sqrt v) ≤ 4 := by
    have h1 : Real.log (2 * Real.sqrt v) ≤ 2 * Real.sqrt v := Real.log_le_self (by positivity)
    nlinarith [hsqrtv_le2]
  have hlog_den : -2 * s⁻¹ ≤ Real.log |v - 1| := by
    have hsq : |v - 1| = s ^ 2 := by
      rw [hs]
      exact (Real.sq_sqrt (abs_nonneg _)).symm
    rw [hsq, Real.log_pow]
    have h1 : Real.log s⁻¹ ≤ s⁻¹ - 1 := Real.log_le_sub_one_of_pos (by positivity)
    rw [Real.log_inv] at h1
    push_cast
    linarith
  have hlogA : Real.log (2 * Real.sqrt v / |v - 1|) ≤ 4 + 2 * s⁻¹ := by
    rw [Real.log_div (by positivity) (ne_of_gt htpos)]
    linarith
  have hmain : 1 + Real.log (2 * Real.sqrt v / |v - 1|) ≤ 7 * s⁻¹ := by
    linarith [hlogA, hone_le_inv]
  rw [hrhs]
  calc (Real.pi / Real.sqrt v) * (1 + Real.log (2 * Real.sqrt v / |v - 1|))
      ≤ (Real.pi / Real.sqrt v) * (7 * s⁻¹) := mul_le_mul_of_nonneg_left hmain hpiv_nonneg
    _ ≤ 8 * (7 * s⁻¹) := mul_le_mul_of_nonneg_right hpiv (by nlinarith [hsinv_nonneg])
    _ ≤ 100 * s⁻¹ := by nlinarith [hsinv_nonneg]

end Commons.Analysis.Integral
