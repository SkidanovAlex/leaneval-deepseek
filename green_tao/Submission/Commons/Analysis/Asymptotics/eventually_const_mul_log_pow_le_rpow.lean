import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace Commons.Analysis.Asymptotics

/-- For `r > 0`, `K : ℕ` and constants `c > 0`, `ε > 0`, the quantity `c (log R)^K` is
eventually dominated by `ε R^r` as `R → ∞`.

Suggested proof: Mathlib's `isLittleO_log_rpow_atTop` (`(fun x => Real.log x) =o[atTop]
(fun x => x ^ r)` for `r > 0`) together with `Asymptotics.IsLittleO` bookkeeping
(`IsLittleO.const_mul_left`, `IsLittleO.pow`, `IsLittleO.tendsto_div_nhds_zero`,
`Filter.Tendsto.eventually`) and `Real.rpow_natCast`, the fact `(fun x => x^r)^K = fun x => x^(r*K)`.
A further ingredient: `Tendsto (fun R : ℝ => Real.log R) atTop atTop` and `Filter.eventually_atTop`. -/
theorem eventually_const_mul_log_pow_le_rpow {c ε r : ℝ} (hc : 0 < c) (hε : 0 < ε) (hr : 0 < r)
    (K : ℕ) :
    ∀ᶠ R : ℝ in Filter.atTop, c * (Real.log R) ^ K ≤ ε * R ^ r := by
  -- `(log x)^K` is little-o of `x^r` for `r > 0`.
  have hlit : (fun x : ℝ => (Real.log x) ^ K) =o[Filter.atTop] fun x : ℝ => x ^ r := by
    refine (isLittleO_log_rpow_rpow_atTop (K : ℝ) hr).congr' ?_ Filter.EventuallyEq.rfl
    filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with x _
    rw [Real.rpow_natCast]
  -- Extract the quantitative bound with constant `ε / c`.
  have h1 : ∀ᶠ R : ℝ in Filter.atTop, (Real.log R) ^ K ≤ (ε / c) * R ^ r := by
    filter_upwards [hlit.bound (div_pos hε hc), Filter.eventually_ge_atTop (1 : ℝ)] with R hR hR1
    have hlog0 : 0 ≤ (Real.log R) ^ K := pow_nonneg (Real.log_nonneg hR1) K
    have hrp0 : 0 ≤ R ^ r := Real.rpow_nonneg (by linarith) r
    rwa [Real.norm_of_nonneg hlog0, Real.norm_of_nonneg hrp0] at hR
  filter_upwards [h1] with R hR
  calc c * (Real.log R) ^ K ≤ c * ((ε / c) * R ^ r) := mul_le_mul_of_nonneg_left hR (le_of_lt hc)
    _ = ε * R ^ r := by field_simp

end Commons.Analysis.Asymptotics