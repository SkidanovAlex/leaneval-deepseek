import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

namespace Commons.Analysis.ExpLog

theorem logPhase_sqrt_mul (t x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    Complex.exp ((((2 * Real.pi * (-(t / (2 * Real.pi)) * Real.log (x * y))) : ℝ) : ℂ) * Complex.I)
        / ((Real.sqrt (x * y) : ℝ) : ℂ)
      = (Complex.exp ((((2 * Real.pi * (-(t / (2 * Real.pi)) * Real.log x)) : ℝ) : ℂ) * Complex.I)
          / ((Real.sqrt x : ℝ) : ℂ))
        * (Complex.exp ((((2 * Real.pi * (-(t / (2 * Real.pi)) * Real.log y)) : ℝ) : ℂ) * Complex.I)
          / ((Real.sqrt y : ℝ) : ℂ)) := by
  have hx' : x ≠ 0 := ne_of_gt hx
  have hy' : y ≠ 0 := ne_of_gt hy
  have hlog : Real.log (x * y) = Real.log x + Real.log y := Real.log_mul hx' hy'
  have hsqrt : Real.sqrt (x * y) = Real.sqrt x * Real.sqrt y := Real.sqrt_mul (le_of_lt hx) y
  have hcast : ((2 * Real.pi * (-(t / (2 * Real.pi)) * Real.log (x * y)) : ℝ) : ℂ)
      = ((2 * Real.pi * (-(t / (2 * Real.pi)) * Real.log x) : ℝ) : ℂ)
        + ((2 * Real.pi * (-(t / (2 * Real.pi)) * Real.log y) : ℝ) : ℂ) := by
    rw [hlog]; push_cast; ring
  have hsqcast : ((Real.sqrt (x * y) : ℝ) : ℂ)
      = ((Real.sqrt x : ℝ) : ℂ) * ((Real.sqrt y : ℝ) : ℂ) := by
    rw [hsqrt]; push_cast; ring
  rw [hcast, hsqcast, add_mul, Complex.exp_add, ← div_mul_div_comm]

end Commons.Analysis.ExpLog