import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Commons.Analysis.Integral

theorem integral_Ioi_four_pi_rpow {t₀ : ℝ} (ht₀ : 0 < t₀) :
    (∫ t in Set.Ioi t₀, (4 * Real.pi * t) ^ (-(3 / 2 : ℝ)))
      = (4 * Real.pi) ^ (-(3 / 2 : ℝ)) * 2 / Real.sqrt t₀ := by
  have h4π : (0 : ℝ) < 4 * Real.pi := by positivity
  have hstep : (∫ t in Set.Ioi t₀, (4 * Real.pi * t) ^ (-(3 / 2 : ℝ)))
      = (4 * Real.pi) ^ (-(3 / 2 : ℝ)) * ∫ t in Set.Ioi t₀, t ^ (-(3 / 2 : ℝ)) :=
    calc (∫ t in Set.Ioi t₀, (4 * Real.pi * t) ^ (-(3 / 2 : ℝ)))
        = ∫ t in Set.Ioi t₀, (4 * Real.pi) ^ (-(3 / 2 : ℝ)) * t ^ (-(3 / 2 : ℝ)) :=
          MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
            (fun t ht => Real.mul_rpow h4π.le (ht₀.trans ht).le)
      _ = (4 * Real.pi) ^ (-(3 / 2 : ℝ)) * ∫ t in Set.Ioi t₀, t ^ (-(3 / 2 : ℝ)) :=
          MeasureTheory.integral_const_mul _ _
  rw [hstep, integral_Ioi_rpow_of_lt (by norm_num) ht₀]
  rw [show (-(3 / 2 : ℝ) + 1) = -(1 / 2 : ℝ) by norm_num]
  have h1 : t₀ ^ (-(1 / 2 : ℝ)) = (Real.sqrt t₀)⁻¹ := by
    rw [Real.sqrt_eq_rpow, Real.rpow_neg ht₀.le]
  rw [h1]
  field_simp

end Commons.Analysis.Integral