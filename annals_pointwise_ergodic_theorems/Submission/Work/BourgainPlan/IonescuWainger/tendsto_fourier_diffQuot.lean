import Mathlib

namespace Work.BourgainPlan.IonescuWainger

/-- The difference quotient of the character `fourier n` at `0` on the circle `ℝ/ℤ` converges to
its derivative `2πi n`:
`t⁻¹ (e^{2πi n t} - 1) → 2πi n` as `t → 0`, `t ≠ 0`. -/
theorem tendsto_fourier_diffQuot (n : ℤ) :
    Filter.Tendsto (fun t : ℝ => ((t : ℂ)⁻¹ * (fourier n (t : AddCircle (1 : ℝ)) - 1)))
      (nhdsWithin (0 : ℝ) ({0}ᶜ)) (nhds ((2 : ℂ) * Real.pi * Complex.I * (n : ℂ))) := by
  -- `hasDerivAt_fourier` gives the derivative of `y ↦ fourier n y` at `0`; the slope form of
  -- `HasDerivAt` turns it into exactly the claimed difference quotient.
  have h := (hasDerivAt_fourier (T := 1) n 0).tendsto_slope_zero
  simp only [zero_add, Complex.real_smul, Complex.ofReal_inv, AddCircle.coe_zero,
    fourier_eval_zero, mul_one, div_one, Complex.ofReal_one] at h
  exact h

end Work.BourgainPlan.IonescuWainger
