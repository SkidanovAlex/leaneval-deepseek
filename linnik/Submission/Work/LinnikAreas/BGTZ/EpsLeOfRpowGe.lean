import Mathlib

namespace Work.LinnikAreas.BGTZ

/-- If `4 * CS ^ 2 ≤ C` and `C * A ^ 2 * Q ^ 2 * E ^ 2 * δ ^ (-2) ≤ R` with all parameters
positive and `δ < 1`, then `CS * A * E * Q / √R ≤ δ / (1 + δ)`.

In fact the stronger bound `CS * A * E * Q / √R ≤ δ / 2` holds, since the hypothesis gives
`(2 * CS * A * Q * E / δ) ^ 2 ≤ R`. -/
theorem EpsLeOfRpowGe {CS A E Q δ R C : ℝ} (hCS : 0 < CS) (hA : 0 < A) (hE : 0 < E)
    (hQ : 0 < Q) (hδ : 0 < δ) (hδ1 : δ < 1) (hR : 0 < R) (hC : 4 * CS ^ 2 ≤ C)
    (hRlo : C * A ^ 2 * Q ^ 2 * E ^ 2 * δ ^ (-2 : ℝ) ≤ R) :
    CS * A * E * Q / R ^ (1 / 2 : ℝ) ≤ δ / (1 + δ) := by
  have hδ2pos : 0 < δ ^ 2 := by positivity
  have hd2 : δ ^ (-2 : ℝ) = (δ ^ 2)⁻¹ := by
    rw [Real.rpow_neg (le_of_lt hδ), Real.rpow_two]
  -- Multiply the hypothesis by `δ ^ 2`.
  have hkey : C * A ^ 2 * Q ^ 2 * E ^ 2 ≤ R * δ ^ 2 := by
    have hRlo' : C * A ^ 2 * Q ^ 2 * E ^ 2 / δ ^ 2 ≤ R := by
      rw [div_eq_mul_inv, ← hd2]; exact hRlo
    rwa [div_le_iff₀ hδ2pos] at hRlo'
  -- Hence `4 * (CS * A * E * Q) ^ 2 ≤ R * δ ^ 2`.
  have hstep : 4 * (CS * A * E * Q) ^ 2 ≤ R * δ ^ 2 := by
    have h2 : 4 * CS ^ 2 * A ^ 2 * Q ^ 2 * E ^ 2 ≤ R * δ ^ 2 := by
      have hmul := mul_le_mul_of_nonneg_right hC (by positivity : (0:ℝ) ≤ A ^ 2 * Q ^ 2 * E ^ 2)
      nlinarith [hmul, hkey]
    nlinarith [h2]
  have hsqR : (R ^ (1 / 2 : ℝ)) ^ 2 = R := by
    rw [← Real.sqrt_eq_rpow]; exact Real.sq_sqrt (le_of_lt hR)
  -- Square the goal and compare.
  have hs : (CS * A * E * Q / R ^ (1 / 2 : ℝ)) ^ 2 ≤ (δ / 2) ^ 2 := by
    rw [div_pow, div_pow, hsqR, div_le_div_iff₀ hR (by norm_num : (0:ℝ) < 2 ^ 2)]
    nlinarith [hstep]
  have hmain : CS * A * E * Q / R ^ (1 / 2 : ℝ) ≤ δ / 2 := by
    have hx : (0:ℝ) ≤ CS * A * E * Q / R ^ (1 / 2 : ℝ) := by positivity
    have hy : (0:ℝ) ≤ δ / 2 := by positivity
    have := sq_le_sq.mp hs
    rwa [abs_of_nonneg hx, abs_of_nonneg hy] at this
  have hfin : δ / 2 ≤ δ / (1 + δ) := by
    rw [div_le_div_iff₀ (by norm_num : (0:ℝ) < 2) (by positivity : (0:ℝ) < 1 + δ)]
    nlinarith [hδ, hδ1]
  exact hmain.trans hfin

end Work.LinnikAreas.BGTZ
