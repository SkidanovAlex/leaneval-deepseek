import Mathlib

namespace Work.FIArea2

/-- Elementary numerical inequality: the "log-volume" arithmetic bound used in
Area 2 of the Friedlander–Iwaniec argument.  For `M ≥ 1` and `0 ≤ γ < 1`,
setting `t = 1/(1 - γ²) ≥ 1`, it reduces to
`8√6 + 2√2·log t ≤ 30·log(t + 2)`, which holds on `[1, ∞)` since the left
side grows slower than the right and the difference is increasing there. -/
theorem log_volume_arithmetic (M γ : ℝ) (hM : 1 ≤ M) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) :
    8 * Real.sqrt 6 * Real.sqrt M + 2 * Real.sqrt 2 * Real.sqrt M * Real.log (1 / (1 - γ ^ 2))
      ≤ 30 * Real.sqrt M * Real.log (2 + 1 / (1 - γ ^ 2)) := by
  have hMpos : (0:ℝ) < M := by linarith
  have hsMpos : (0:ℝ) < Real.sqrt M := Real.sqrt_pos.mpr hMpos
  -- `γ ^ 2 < 1`
  have hγ2 : γ ^ 2 < 1 := by
    have h1 : 0 < 1 - γ := by linarith
    have h2 : 0 < 1 + γ := by linarith
    nlinarith [mul_pos h1 h2]
  have hApos : 0 < 1 - γ ^ 2 := by linarith
  have hAle1 : 1 - γ ^ 2 ≤ 1 := by nlinarith [sq_nonneg γ]
  -- `t = 1/(1 - γ²) ≥ 1` and `t > 0`
  have ht_ge1 : 1 ≤ 1 / (1 - γ ^ 2) := by
    have := one_div_le_one_div_of_le hApos hAle1
    simpa using this
  have htpos : 0 < 1 / (1 - γ ^ 2) := by linarith
  have hlog_le : Real.log (1 / (1 - γ ^ 2)) ≤ Real.log (2 + 1 / (1 - γ ^ 2)) :=
    Real.log_le_log htpos (by linarith)
  -- numerical bounds
  have h6 : Real.sqrt 6 ≤ 3 := by rw [Real.sqrt_le_iff]; constructor <;> norm_num
  have h2 : Real.sqrt 2 ≤ 2 := by rw [Real.sqrt_le_iff]; constructor <;> norm_num
  have hc_nonneg : 0 ≤ 30 - 2 * Real.sqrt 2 := by linarith
  have hc_ge : 8 * Real.sqrt 6 ≤ 30 - 2 * Real.sqrt 2 := by linarith
  have hlog3 : (1:ℝ) ≤ Real.log 3 := by
    have := (Real.le_log_iff_exp_le (by norm_num : (0:ℝ) < 3)).mpr
      (le_of_lt Real.exp_one_lt_three)
    simpa using this
  have hlog_ge1 : (1:ℝ) ≤ Real.log (2 + 1 / (1 - γ ^ 2)) := by
    have h3le : (3:ℝ) ≤ 2 + 1 / (1 - γ ^ 2) := by linarith
    have := Real.log_le_log (by norm_num : (0:ℝ) < 3) h3le
    linarith
  have h8 : 8 * Real.sqrt 6 ≤ (30 - 2 * Real.sqrt 2) * Real.log (2 + 1 / (1 - γ ^ 2)) := by
    have := mul_le_mul_of_nonneg_left hlog_ge1 hc_nonneg
    linarith
  -- core inequality after factoring out `√M`
  have hkey : 8 * Real.sqrt 6 + 2 * Real.sqrt 2 * Real.log (1 / (1 - γ ^ 2))
      ≤ 30 * Real.log (2 + 1 / (1 - γ ^ 2)) := by
    have h2' : 2 * Real.sqrt 2 * Real.log (1 / (1 - γ ^ 2))
        ≤ 2 * Real.sqrt 2 * Real.log (2 + 1 / (1 - γ ^ 2)) :=
      mul_le_mul_of_nonneg_left hlog_le (by positivity)
    nlinarith [h8, h2']
  calc
    8 * Real.sqrt 6 * Real.sqrt M + 2 * Real.sqrt 2 * Real.sqrt M * Real.log (1 / (1 - γ ^ 2))
        = Real.sqrt M * (8 * Real.sqrt 6 + 2 * Real.sqrt 2 * Real.log (1 / (1 - γ ^ 2))) := by ring
    _ ≤ Real.sqrt M * (30 * Real.log (2 + 1 / (1 - γ ^ 2))) :=
        mul_le_mul_of_nonneg_left hkey (le_of_lt hsMpos)
    _ = 30 * Real.sqrt M * Real.log (2 + 1 / (1 - γ ^ 2)) := by ring

end Work.FIArea2
