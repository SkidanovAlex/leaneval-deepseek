import Mathlib

namespace Work.TMC16Core.Basic

/-- The tail of the series `∑ 3/(N+m)^2`, viewed in `ℝ≥0∞`, tends to `0` as `N → ∞`. -/
theorem tsum_ofReal_inv_sq_tail :
    Filter.Tendsto
      (fun N : ℕ => ∑' m : ℕ, ENNReal.ofReal (3 * (((N + m : ℕ) : ℝ))⁻¹ ^ 2))
      Filter.atTop (nhds 0) := by
  -- `∑ 3/n^2` is summable over `ℕ`.
  have hs : Summable (fun n : ℕ => 3 * ((n : ℝ)⁻¹) ^ 2) := by
    have h1 : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 2) :=
      (Real.summable_one_div_nat_pow (p := 2)).mpr (by norm_num)
    simpa [one_div, inv_pow] using h1.mul_left 3
  -- hence the `ℝ≥0∞`-valued series has finite total sum.
  have hsum : (∑' (i : ℕ), ENNReal.ofReal (3 * ((i : ℝ)⁻¹) ^ 2))
      = ENNReal.ofReal (∑' (n : ℕ), 3 * ((n : ℝ)⁻¹) ^ 2) :=
    (ENNReal.ofReal_tsum_of_nonneg (f := fun n : ℕ => 3 * ((n : ℝ)⁻¹) ^ 2)
      (fun n => by positivity) hs).symm
  have hf : ∑' (i : ℕ), ENNReal.ofReal (3 * ((i : ℝ)⁻¹) ^ 2) ≠ ⊤ := by
    rw [hsum]; exact ENNReal.ofReal_ne_top
  -- tails of a summable `ℝ≥0∞`-series tend to `0`.
  refine (ENNReal.tendsto_sum_nat_add
    (fun n : ℕ => ENNReal.ofReal (3 * ((n : ℝ)⁻¹) ^ 2)) hf).congr' ?_
  filter_upwards with N
  exact tsum_congr (fun m => by rw [Nat.add_comm N m])

end Work.TMC16Core.Basic
