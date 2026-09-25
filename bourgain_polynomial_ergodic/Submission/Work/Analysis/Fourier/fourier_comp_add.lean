import Mathlib
open MeasureTheory
open scoped ENNReal FourierTransform

namespace Commons.Analysis.Fourier

/-- **The translate rule for the one-dimensional Fourier transform** (function level):
`𝓕(f(·+y))(ξ) = e^{2πiyξ}·𝓕f(ξ)`. -/
lemma fourier_comp_add (f : ℝ → ℂ) (y η : ℝ) :
    FourierTransform.fourier (fun z : ℝ => f (z + y)) η
      = Complex.exp ((↑(2 * Real.pi * y * η) * Complex.I) : ℂ) *
        FourierTransform.fourier f η := by
  rw [Real.fourier_eq', Real.fourier_eq']
  simp only [Real.inner_apply]
  have hshift : (fun z : ℝ => Complex.exp ((↑(-2 * Real.pi * (z * η)) * Complex.I) : ℂ) • f (z + y))
      = fun z : ℝ => (fun u : ℝ =>
          Complex.exp ((↑(-2 * Real.pi * ((u - y) * η)) * Complex.I) : ℂ) • f u) (z + y) := by
    funext z
    simp only [add_sub_cancel_right]
  have hkey : (∫ z : ℝ, (fun u : ℝ =>
        Complex.exp ((↑(-2 * Real.pi * ((u - y) * η)) * Complex.I) : ℂ) • f u) (z + y))
      = ∫ u : ℝ, Complex.exp ((↑(-2 * Real.pi * ((u - y) * η)) * Complex.I) : ℂ) • f u :=
    MeasureTheory.integral_add_right_eq_self (f := fun u : ℝ =>
      Complex.exp ((↑(-2 * Real.pi * ((u - y) * η)) * Complex.I) : ℂ) • f u) y
  rw [hshift, hkey]
  rw [← MeasureTheory.integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  simp only [smul_eq_mul]
  rw [show (-2 * Real.pi * ((u - y) * η) : ℝ)
      = 2 * Real.pi * y * η + (-(2 * Real.pi * (u * η))) by ring]
  rw [Complex.ofReal_add]
  rw [show ((↑(2 * Real.pi * y * η) : ℂ) + ↑(-(2 * Real.pi * (u * η)))) * Complex.I
      = ↑(2 * Real.pi * y * η) * Complex.I + ↑(-(2 * Real.pi * (u * η))) * Complex.I by ring]
  rw [Complex.exp_add]
  ring

end Commons.Analysis.Fourier
