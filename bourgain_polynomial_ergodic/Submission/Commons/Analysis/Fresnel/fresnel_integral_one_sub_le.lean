import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

namespace Commons.Analysis.Fresnel

open MeasureTheory
open scoped BigOperators ENNReal Topology

/-- Bourgain (5.18) for the quadratic phase: the Fresnel factor differs from `1` by at most
`2π N²|β|` (in the variable `x = N²β`). -/
theorem fresnel_integral_one_sub_le (x : ℝ) :
    ‖(∫ s in (0:ℝ)..1, Complex.exp (2 * Real.pi * Complex.I * ((x * s^2 : ℝ) : ℂ))) - 1‖
      ≤ 2 * Real.pi * |x| := by
  have hcont : Continuous fun s : ℝ =>
      Complex.exp (2 * Real.pi * Complex.I * ((x * s^2 : ℝ) : ℂ)) := by fun_prop
  have hsub :
      (∫ s in (0:ℝ)..1, Complex.exp (2 * Real.pi * Complex.I * ((x * s^2 : ℝ) : ℂ))) - 1
        = ∫ s in (0:ℝ)..1,
            (Complex.exp (2 * Real.pi * Complex.I * ((x * s^2 : ℝ) : ℂ)) - 1) := by
    rw [intervalIntegral.integral_sub (hcont.intervalIntegrable 0 1)
      (continuous_const.intervalIntegrable (0:ℝ) 1)]
    simp
  rw [hsub]
  have hpt : ∀ s ∈ Set.uIoc (0:ℝ) 1,
      ‖Complex.exp (2 * Real.pi * Complex.I * ((x * s^2 : ℝ) : ℂ)) - 1‖ ≤ 2 * Real.pi * |x| := by
    intro s hs
    rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hs
    have hs0 : 0 < s := hs.1
    have hs1 : s ≤ 1 := hs.2
    have hsq : s ^ 2 ≤ 1 := by nlinarith
    have hsq0 : 0 ≤ s ^ 2 := sq_nonneg s
    have hcongr : Complex.exp (2 * Real.pi * Complex.I * ((x * s^2 : ℝ) : ℂ)) - 1
        = Complex.exp (Complex.I * ((2 * Real.pi * x * s^2 : ℝ) : ℂ)) - 1 := by
      congr 1
      push_cast
      ring
    rw [hcongr]
    calc ‖Complex.exp (Complex.I * ((2 * Real.pi * x * s^2 : ℝ) : ℂ)) - 1‖
        ≤ |2 * Real.pi * x * s^2| := Real.norm_exp_I_mul_ofReal_sub_one_le
      _ = 2 * Real.pi * |x| * s^2 := by
            rw [abs_mul, abs_mul, abs_of_nonneg hsq0,
              abs_of_nonneg (by positivity : (0:ℝ) ≤ 2 * Real.pi)]
      _ ≤ 2 * Real.pi * |x| := by
            have hnn : 0 ≤ 2 * Real.pi * |x| := by positivity
            nlinarith [hsq, hnn]
  have hfin := intervalIntegral.norm_integral_le_of_norm_le_const hpt
  simpa using hfin

end Commons.Analysis.Fresnel