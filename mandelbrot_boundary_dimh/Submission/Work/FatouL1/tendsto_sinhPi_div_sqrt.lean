import Mathlib

namespace Work.FatouL1

/-- As `z → +∞`, `sinh (π z) / sqrt (A + sinh (π z)^2)` tends to `1` for every `A > 0`:
the numerator dominates the constant `A`, so the quotient is the reciprocal of
`sqrt (1 + A / sinh (π z)^2)`. -/
theorem tendsto_sinhPi_div_sqrt (A : ℝ) (hA : 0 < A) :
    Filter.Tendsto (fun z : ℝ => Real.sinh (Real.pi * z) /
      Real.sqrt (A + Real.sinh (Real.pi * z) ^ 2)) Filter.atTop (nhds 1) := by
  have _ := hA
  -- `sinh` tends to `+∞` at `+∞` (it dominates the identity there).
  have hsinh_atTop : Filter.Tendsto Real.sinh Filter.atTop Filter.atTop := by
    refine Filter.tendsto_atTop_mono' _ ?_ Filter.tendsto_id
    filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with x hx
    exact Real.self_le_sinh_iff.mpr hx
  have hπ : Filter.Tendsto (fun z : ℝ => Real.pi * z) Filter.atTop Filter.atTop :=
    Filter.tendsto_id.const_mul_atTop Real.pi_pos
  have hsinh : Filter.Tendsto (fun z : ℝ => Real.sinh (Real.pi * z)) Filter.atTop Filter.atTop :=
    hsinh_atTop.comp hπ
  -- The quotient, as a function of `s = sinh (π z)`, tends to `1`.
  have hmain : Filter.Tendsto (fun s : ℝ => s / Real.sqrt (A + s ^ 2)) Filter.atTop (nhds 1) := by
    have hAsq : Filter.Tendsto (fun s : ℝ => s ^ 2) Filter.atTop Filter.atTop := by
      refine Filter.tendsto_atTop_mono' _ ?_ Filter.tendsto_id
      filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with x hx
      simpa using pow_le_pow_right₀ hx (show (1 : ℕ) ≤ 2 by norm_num)
    have hA_inv : Filter.Tendsto (fun s : ℝ => A / s ^ 2) Filter.atTop (nhds 0) := by
      have h : Filter.Tendsto (fun s : ℝ => A * (s ^ 2)⁻¹) Filter.atTop (nhds (A * 0)) :=
        tendsto_const_nhds.mul (tendsto_inv_atTop_zero.comp hAsq)
      rw [mul_zero] at h
      simpa only [div_eq_mul_inv] using h
    have h1 : Filter.Tendsto (fun s : ℝ => 1 + A / s ^ 2) Filter.atTop (nhds 1) := by
      have h := hA_inv.const_add 1
      simpa using h
    have hF : Filter.Tendsto (fun s : ℝ => Real.sqrt (1 + A / s ^ 2)) Filter.atTop (nhds 1) := by
      have h := h1.sqrt
      simpa using h
    have hFinv : Filter.Tendsto (fun s : ℝ => (Real.sqrt (1 + A / s ^ 2))⁻¹) Filter.atTop (nhds 1) := by
      have h := hF.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
      simpa using h
    have heq : (fun s : ℝ => s / Real.sqrt (A + s ^ 2)) =ᶠ[Filter.atTop]
        (fun s : ℝ => (Real.sqrt (1 + A / s ^ 2))⁻¹) := by
      filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with s hs
      have hs0 : s ≠ 0 := hs.ne'
      rw [show A + s ^ 2 = s ^ 2 * (1 + A / s ^ 2) by field_simp; ring]
      rw [Real.sqrt_mul (sq_nonneg s), Real.sqrt_sq hs.le]
      rw [div_mul_eq_div_div, div_self hs0, one_div]
    exact Filter.Tendsto.congr' heq.symm hFinv
  exact hmain.comp hsinh

end Work.FatouL1
