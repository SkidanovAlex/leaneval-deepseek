import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseKinLoc.Momentum

theorem cubFT_one_dim_cos_bound (a : ℝ) :
    |∫ t in Set.Icc (-(1:ℝ) / 2) ((1:ℝ) / 2), Real.cos (a * t)| ≤ 2 / max 1 |a| := by
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (-(1:ℝ)/2) ≤ (1:ℝ)/2)]
  rcases le_or_gt |a| 1 with h | h
  · -- small frequencies: the integrand is globally bounded by `1` on a unit interval
    rw [max_eq_left h, div_one]
    have h1 : ‖∫ t in (-(1:ℝ)/2)..((1:ℝ)/2), Real.cos (a*t)‖ ≤ 1 * |(1:ℝ)/2 - (-(1:ℝ)/2)| :=
      intervalIntegral.norm_integral_le_of_norm_le_const
        (fun x hx => by rw [Real.norm_eq_abs]; exact Real.abs_cos_le_one _)
    rw [Real.norm_eq_abs] at h1
    have h2 : (1:ℝ) * |(1:ℝ)/2 - (-(1:ℝ)/2)| = 1 := by norm_num
    linarith
  · -- large frequencies: evaluate the integral and use `|sin| ≤ 1`
    rw [max_eq_right (le_of_lt h)]
    have hane : a ≠ 0 := by
      intro h0; rw [h0] at h; exact absurd h (by norm_num)
    have key : ∀ x y : ℝ, |a⁻¹ * (Real.sin x - Real.sin y)| ≤ 2/|a| := by
      intro x y
      calc |a⁻¹ * (Real.sin x - Real.sin y)| = |a⁻¹| * |Real.sin x - Real.sin y| := abs_mul _ _
        _ ≤ |a⁻¹| * 2 := by
            apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
            calc |Real.sin x - Real.sin y| ≤ |Real.sin x| + |Real.sin y| := abs_sub _ _
              _ ≤ 1 + 1 := add_le_add (Real.abs_sin_le_one _) (Real.abs_sin_le_one _)
              _ = 2 := by norm_num
        _ = 2/|a| := by rw [abs_inv, div_eq_mul_inv]; ring
    rw [intervalIntegral.integral_comp_mul_left (fun x => Real.cos x) hane, integral_cos, smul_eq_mul]
    exact key _ _

end Work.BoseKinLoc.Momentum
