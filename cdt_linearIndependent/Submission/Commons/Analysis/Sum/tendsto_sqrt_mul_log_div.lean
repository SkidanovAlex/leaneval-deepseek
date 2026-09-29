import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace Commons.Analysis.Sum

/-- `√n · log n / n → 0` as `n → ∞` along the natural numbers.

Since `√n · log n / n = log n / √n = log n / n ^ (1/2)`, this is the
`log = o(x ^ r)` (for `r > 0`) asymptotic at `+∞`, restricted to `ℕ`. -/
theorem tendsto_sqrt_mul_log_div :
    Filter.Tendsto (fun n : ℕ => Real.sqrt (n : ℝ) * Real.log (n : ℝ) / (n : ℝ))
      Filter.atTop (nhds 0) := by
  -- `log x / x ^ (1/2) → 0` along `atTop` on `ℝ`, from `log = o(x ^ (1/2))`.
  have h1 : Filter.Tendsto (fun x : ℝ => Real.log x / x ^ (1 / 2 : ℝ))
      Filter.atTop (nhds 0) :=
    (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero
  -- Restrict to the naturals.
  have h2 : Filter.Tendsto (fun n : ℕ => Real.log (n : ℝ) / (n : ℝ) ^ (1 / 2 : ℝ))
      Filter.atTop (nhds 0) :=
    h1.comp tendsto_natCast_atTop_atTop
  -- The two functions agree for `n ≥ 1`.
  refine h2.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  have hpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hpos
  have hs0 : (n : ℝ) ^ (1 / 2 : ℝ) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hpos _)
  have hsq : (n : ℝ) ^ (1 / 2 : ℝ) * (n : ℝ) ^ (1 / 2 : ℝ) = (n : ℝ) := by
    rw [← Real.rpow_add hpos, show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num, Real.rpow_one]
  rw [Real.sqrt_eq_rpow]
  rw [div_eq_div_iff hs0 hn0]
  have hrw : (n : ℝ) ^ (1 / 2 : ℝ) * Real.log (n : ℝ) * (n : ℝ) ^ (1 / 2 : ℝ)
      = ((n : ℝ) ^ (1 / 2 : ℝ) * (n : ℝ) ^ (1 / 2 : ℝ)) * Real.log (n : ℝ) := by ring
  rw [hrw, hsq]
  ring

end Commons.Analysis.Sum