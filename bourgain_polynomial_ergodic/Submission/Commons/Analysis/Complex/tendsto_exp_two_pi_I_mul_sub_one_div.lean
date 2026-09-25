import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

namespace Commons.Analysis.Complex

theorem tendsto_exp_two_pi_I_mul_sub_one_div (t : ℝ) :
    Filter.Tendsto (fun h : ℝ => (Complex.exp (2 * Real.pi * Complex.I * t * h) - 1) / h)
      (nhdsWithin (0 : ℝ) ({(0 : ℝ)}ᶜ)) (nhds (2 * Real.pi * Complex.I * t)) := by
  have h1 : HasDerivAt (fun h : ℝ => (h : ℂ)) 1 0 := Complex.ofRealCLM.hasDerivAt
  have h2 : HasDerivAt (fun h : ℝ => (2 * Real.pi * Complex.I * t) * (h : ℂ))
      (2 * Real.pi * Complex.I * t) 0 := by
    simpa using h1.const_mul (2 * Real.pi * Complex.I * t)
  have h3 : HasDerivAt (fun h : ℝ => Complex.exp ((2 * Real.pi * Complex.I * t) * (h : ℂ)))
      (2 * Real.pi * Complex.I * t) 0 := by
    simpa using h2.cexp
  have h4 := h3.tendsto_slope_zero
  simpa [Complex.real_smul, div_eq_inv_mul, mul_comm, mul_left_comm, mul_assoc] using h4

end Commons.Analysis.Complex