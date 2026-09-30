import Mathlib.Analysis.SpecialFunctions.Log.Basic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open Filter
open scoped Topology

namespace Commons.NumberTheory.Linnik

/-- For any fixed real `C` and any fixed exponent `k : ℕ`,
`(log (R + 2) + C) ^ k / R` tends to zero as `R → ∞`. -/
private theorem ell_pow_div_self_tendsto_zero_of_real (C : ℝ) (k : ℕ) :
    Tendsto (fun R : ℝ => (Real.log (R + 2) + C) ^ k / R) atTop (𝓝 0) := by
  have hS : Tendsto (fun u : ℝ => (Real.log u + C) ^ k / (u - 2)) atTop (𝓝 0) := by
    have hrest : Tendsto (fun u : ℝ => Real.log u ^ k / (u - 2)) atTop (𝓝 0) := by
      have h0 := Real.tendsto_pow_log_div_mul_add_atTop (1 : ℝ) (-2) k (by norm_num)
      refine h0.congr' ?_
      filter_upwards with x
      ring
    have hU : Tendsto (fun u : ℝ => ((2 : ℝ) ^ k * Real.log u ^ k) / (u - 2)) atTop (𝓝 0) := by
      have hmul : Tendsto
          (fun u : ℝ => (2 : ℝ) ^ k * (Real.log u ^ k / (u - 2))) atTop (𝓝 0) := by
        simpa using ((tendsto_const_nhds (x := (2 : ℝ) ^ k)).mul hrest)
      refine hmul.congr' ?_
      filter_upwards with x
      ring
    -- squeeze: 0 ≤ (log u + C)^k/(u-2) ≤ (2^k * log u^k)/(u-2) eventually
    have hlogTop : Tendsto Real.log atTop atTop := Real.tendsto_log_atTop
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
      (tendsto_const_nhds (x := (0 : ℝ))) hU ?hlow ?hup
    · filter_upwards [hlogTop.eventually (eventually_ge_atTop (max 1 |C|)),
        eventually_gt_atTop (2 : ℝ)] with u hbig hu2
      have hC_abs : |C| ≤ Real.log u := le_trans (le_max_right (1 : ℝ) |C|) hbig
      have hneg_le : -C ≤ Real.log u := (neg_le_abs C).trans hC_abs
      have hpos : 0 ≤ Real.log u + C := by linarith
      exact div_nonneg (pow_nonneg hpos k) (by linarith)
    · filter_upwards [hlogTop.eventually (eventually_ge_atTop (max 1 |C|)),
        eventually_gt_atTop (2 : ℝ)] with u hbig hu2
      have hC_abs : |C| ≤ Real.log u := le_trans (le_max_right (1 : ℝ) |C|) hbig
      have hC_le : C ≤ |C| := le_abs_self C
      have hpos : 0 ≤ Real.log u + C := by
        have hneg_le : -C ≤ Real.log u := (neg_le_abs C).trans hC_abs
        linarith
      have hle1 : Real.log u + C ≤ Real.log u + |C| := by linarith
      have hle2 : Real.log u + |C| ≤ 2 * Real.log u := by linarith
      have hle : Real.log u + C ≤ 2 * Real.log u := le_trans hle1 hle2
      have hpow : (Real.log u + C) ^ k ≤ (2 * Real.log u) ^ k :=
        pow_le_pow_left₀ hpos hle k
      have hpow' : (Real.log u + C) ^ k ≤ (2 : ℝ) ^ k * Real.log u ^ k := by
        rwa [mul_pow] at hpow
      exact div_le_div_of_nonneg_right hpow' (by linarith)
  have hRadd : Tendsto (fun R : ℝ => R + 2) atTop atTop := by
    exact Filter.Tendsto.atTop_add (C := (2 : ℝ))
      (tendsto_id : Tendsto (fun R : ℝ => R) atTop atTop)
      (tendsto_const_nhds (x := (2 : ℝ)))
  refine (hS.comp hRadd).congr' ?_
  filter_upwards with R
  dsimp
  ring

theorem ell_pow_div_self_tendsto_zero {N : ℕ} [NeZero N] (k : ℕ) :
    Tendsto (fun R : ℝ => (Real.log (R + 2) + Real.log (N : ℝ) + 2) ^ k / R) atTop (𝓝 0) := by
  simpa [add_assoc] using ell_pow_div_self_tendsto_zero_of_real (Real.log (N : ℝ) + 2) k

end Commons.NumberTheory.Linnik