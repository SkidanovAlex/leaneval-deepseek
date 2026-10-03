import Mathlib.Analysis.SpecificLimits.Normed

namespace Commons.Analysis.Sum

/-- The geometric moment series `∑ (n+1) / Λ^n` converges for `Λ > 1`.  This bounds the
    cut-off error terms `∑_N (log₂ N + 1)/N` that arise in the dyadic telescoping decomposition of
    Cesàro averages (a lacunary sequence grows at least geometrically). -/
theorem summable_succ_mul_inv_pow {Λ : NNReal} (hΛ : 1 < Λ) :
    Summable (fun n : ℕ => ((n : ℝ) + 1) * ((Λ : ℝ) ^ n)⁻¹) := by
  have hΛR : (1 : ℝ) < (Λ : ℝ) := by exact_mod_cast hΛ
  have hΛpos : (0 : ℝ) < (Λ : ℝ) := lt_trans zero_lt_one hΛR
  -- The reciprocal of `Λ` is the geometric ratio, and it lies in the unit ball.
  have hrnorm : ‖((Λ : ℝ))⁻¹‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hΛpos)]
    exact inv_lt_one_of_one_lt₀ hΛR
  -- `∑ n * r^n` and `∑ r^n` both converge, where `r = Λ⁻¹`.
  have h1 : Summable (fun n : ℕ => (n : ℝ) ^ 1 * ((Λ : ℝ))⁻¹ ^ n) :=
    summable_pow_mul_geometric_of_norm_lt_one 1 hrnorm
  have h0 : Summable (fun n : ℕ => (n : ℝ) ^ 0 * ((Λ : ℝ))⁻¹ ^ n) :=
    summable_pow_mul_geometric_of_norm_lt_one 0 hrnorm
  -- Their sum is the requested series.
  refine (h1.add h0).congr (fun n => ?_)
  simp only [pow_one, pow_zero, one_mul]
  rw [inv_pow]
  ring

end Commons.Analysis.Sum