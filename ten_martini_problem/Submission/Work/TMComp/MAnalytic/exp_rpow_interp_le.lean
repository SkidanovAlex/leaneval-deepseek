import Mathlib

namespace Work.TMComp.MAnalytic

theorem exp_rpow_interp_le {R ρ δ : ℝ} (hR : 0 < R) (hρ : 0 < ρ)
    (hρle : ρ ≤ R * Real.sqrt 2) (hδ : 0 ≤ δ) :
    (Real.exp (-δ)) ^ (1 - (Real.log ρ - Real.log R) / (Real.log (2 * R) - Real.log R))
      ≤ Real.exp (-(δ / 2)) := by
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hden : Real.log (2 * R) - Real.log R = Real.log 2 := by
    rw [Real.log_mul (by norm_num : (2:ℝ) ≠ 0) (ne_of_gt hR)]; ring
  have hsqrt2pos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hlogle : Real.log ρ ≤ Real.log R + Real.log 2 / 2 := by
    have h1 : Real.log ρ ≤ Real.log (R * Real.sqrt 2) := Real.log_le_log hρ hρle
    rw [Real.log_mul (ne_of_gt hR) (ne_of_gt hsqrt2pos),
        Real.log_sqrt (by norm_num : (0:ℝ) ≤ 2)] at h1
    linarith
  set t := 1 - (Real.log ρ - Real.log R) / (Real.log (2 * R) - Real.log R) with ht
  have ht_ge : (1:ℝ)/2 ≤ t := by
    rw [ht, hden]
    have hb : (Real.log ρ - Real.log R) / Real.log 2 ≤ 1/2 := by
      rw [div_le_iff₀ hlog2pos]
      linarith
    linarith
  rw [Real.rpow_def_of_pos (Real.exp_pos (-δ)), Real.log_exp]
  apply Real.exp_le_exp.mpr
  have hmul : δ * (1/2) ≤ δ * t := mul_le_mul_of_nonneg_left ht_ge hδ
  nlinarith [hmul]

end Work.TMComp.MAnalytic
