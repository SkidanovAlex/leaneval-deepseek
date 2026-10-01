import Mathlib

namespace Work.LinnikAreas.Zeta1Aux

/-- **Elementary vanishing.** For positive `M`, `Cd`, `c`,
`t ↦ (M / (1 + t^2)) * (Cd * (1 + 1/c) * (log (t + 3))^2)` tends to `0` as `t → +∞`.

(The polynomial decay `1/t^2` beats any power of the logarithm.) -/
theorem tendsto_inv_sq_mul_log_sq {M Cd c : ℝ} (hM : 0 < M) (hCd : 0 < Cd) (hc : 0 < c) :
    Filter.Tendsto (fun t : ℝ =>
        (M / (1 + t ^ 2)) * (Cd * (1 + 1 / c) * (Real.log (t + 3)) ^ 2))
      Filter.atTop (nhds 0) := by
  -- Squeeze the target between `0` and a constant multiple of `(log (t+3)/(t+3))^2`,
  -- which tends to `0` by the classical `log x / x → 0`.
  refine squeeze_zero' (f := fun t : ℝ =>
      (M / (1 + t ^ 2)) * (Cd * (1 + 1 / c) * (Real.log (t + 3)) ^ 2))
    (g := fun t : ℝ => (M * Cd * (1 + 1 / c)) * 2 * (Real.log (t + 3) / (t + 3)) ^ 2) ?_ ?_ ?_
  · -- nonnegativity of the target
    filter_upwards with t
    positivity
  · -- the eventual comparison, valid for `t ≥ 7`
    filter_upwards [Filter.eventually_ge_atTop (7 : ℝ)] with t ht
    have hden : (0 : ℝ) < 1 + t ^ 2 := by positivity
    have hquad : (0 : ℝ) ≤ (t - 7) * (t + 1) := mul_nonneg (by linarith) (by linarith)
    -- `1/(1+t^2) ≤ 2/(t+3)^2` for `t ≥ 7`
    have key : (1 : ℝ) / (1 + t ^ 2) ≤ 2 / (t + 3) ^ 2 := by
      rw [div_le_div_iff₀ hden (by positivity)]
      nlinarith [hquad]
    have hL : (0 : ℝ) ≤ (Real.log (t + 3)) ^ 2 := sq_nonneg _
    have hK : (0 : ℝ) ≤ M * Cd * (1 + 1 / c) := by positivity
    have h1 : (Real.log (t + 3)) ^ 2 * ((1 : ℝ) / (1 + t ^ 2))
        ≤ (Real.log (t + 3)) ^ 2 * (2 / (t + 3) ^ 2) := mul_le_mul_of_nonneg_left key hL
    have h2 := mul_le_mul_of_nonneg_left h1 hK
    have e1 : M * Cd * (1 + 1 / c) * ((Real.log (t + 3)) ^ 2 * (1 / (1 + t ^ 2)))
        = (M / (1 + t ^ 2)) * (Cd * (1 + 1 / c) * (Real.log (t + 3)) ^ 2) := by
      field_simp
    have e2 : M * Cd * (1 + 1 / c) * ((Real.log (t + 3)) ^ 2 * (2 / (t + 3) ^ 2))
        = (M * Cd * (1 + 1 / c)) * 2 * (Real.log (t + 3) / (t + 3)) ^ 2 := by
      field_simp
    linarith [h2, e1.le, e1.ge, e2.le, e2.ge]
  · -- `(log (t+3)/(t+3))^2 → 0`, then multiply by the constant
    have hX : Filter.Tendsto (fun t : ℝ => (Real.log (t + 3) / (t + 3)) ^ 2)
        Filter.atTop (nhds 0) := by
      have h0 : Filter.Tendsto (fun x : ℝ => Real.log x / x) Filter.atTop (nhds 0) := by
        simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
      have h1 : Filter.Tendsto (fun x : ℝ => (Real.log x / x) ^ 2) Filter.atTop (nhds 0) := by
        simpa using h0.pow 2
      have hc' : Filter.Tendsto (fun t : ℝ => t + 3) Filter.atTop Filter.atTop :=
        Filter.tendsto_atTop_add_const_right Filter.atTop (3 : ℝ) Filter.tendsto_id
      simpa [Function.comp_def] using h1.comp hc'
    have h2 : Filter.Tendsto (fun t : ℝ =>
        (2 * (M * Cd * (1 + 1 / c))) * (Real.log (t + 3) / (t + 3)) ^ 2)
        Filter.atTop (nhds 0) := by
      have := hX.const_mul (2 * (M * Cd * (1 + 1 / c)))
      simpa using this
    refine h2.congr' ?_
    filter_upwards with t
    ring

end Work.LinnikAreas.Zeta1Aux
