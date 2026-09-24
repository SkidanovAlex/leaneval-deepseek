import Mathlib
import Submission.Work.GM.Energy.RMoments.FejerDefs

namespace Work.GM.Energy.RMoments

open MeasureTheory

/-- The Fourier transform of the Fejér kernel `fejerK u = (2π)⁻¹ sinc(u/2)²` is the triangle
function `tri` (supported in `[-1,1]`): `∫ fejerK u · e^{i s u} du = tri s`.

This is the classical transform pair: rescaling `u = 2π y` turns the integral into
`∫ sinc (π y)² e^{2π i s y} dy`, which is the (already established) pair
`Commons.Analysis.Fourier.integral_sinc_pi_sq_mul_exp` at frequency `-s`. -/
theorem fejerK_transform (s : ℝ) :
    ∫ u : ℝ, ((fejerK u : ℝ) : ℂ) * Complex.exp (Complex.I * ((s * u : ℝ) : ℂ))
      = ((Commons.Analysis.Fourier.tri s : ℝ) : ℂ) := by
  -- The rescaled integrand `gs y` satisfies `fejerK u · e^{isu} = (2π)⁻¹ · gs (u/2π)`.
  set gs : ℝ → ℂ := fun y => ((Real.sinc (Real.pi * y) ^ 2 : ℝ) : ℂ) *
      Complex.exp (Complex.I * ((s * (2 * Real.pi * y) : ℝ) : ℂ)) with hgs
  have h2pi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  have hpt : ∀ u : ℝ, ((fejerK u : ℝ) : ℂ) * Complex.exp (Complex.I * ((s * u : ℝ) : ℂ))
      = ((2 * Real.pi)⁻¹ : ℂ) * gs ((2 * Real.pi)⁻¹ * u) := by
    intro u
    have harg : Real.pi * ((2 * Real.pi)⁻¹ * u) = u / 2 := by
      have h1 : Real.pi * (2 * Real.pi)⁻¹ = (2 : ℝ)⁻¹ := by
        rw [mul_comm Real.pi (2 * Real.pi)⁻¹, mul_inv, mul_assoc,
          inv_mul_cancel₀ Real.pi_ne_zero, mul_one]
      rw [← mul_assoc, h1]
      ring
    have harg2 : 2 * Real.pi * ((2 * Real.pi)⁻¹ * u) = u := by
      rw [← mul_assoc, mul_inv_cancel₀ h2pi, one_mul]
    rw [hgs]
    simp only
    rw [harg, harg2, fejerK]
    push_cast
    ring
  have htrans : (∫ u : ℝ, ((fejerK u : ℝ) : ℂ) * Complex.exp (Complex.I * ((s * u : ℝ) : ℂ)))
      = ∫ u : ℝ, ((2 * Real.pi)⁻¹ : ℂ) * gs ((2 * Real.pi)⁻¹ * u) :=
    MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt)
  -- Substitute `u = 2π y` (a linear change of variables on `ℝ`).
  rw [htrans, MeasureTheory.integral_const_mul,
      MeasureTheory.Measure.integral_comp_inv_mul_left,
      show |(2 * Real.pi : ℝ)| = 2 * Real.pi from abs_of_pos (by positivity)]
  have hcancel : ∀ z : ℂ, ((2 : ℂ) * (Real.pi : ℂ))⁻¹ * ((2 * Real.pi : ℝ) • z) = z := by
    intro z
    rw [Complex.real_smul, Complex.ofReal_mul]
    norm_num
    field_simp
  rw [hcancel]
  -- The remaining integral is the standard Fourier pair `∫ sinc (π y)² e^{-2π i y (-s)} dy = tri (-s)`.
  have hgs_eq : (∫ y : ℝ, gs y)
      = ∫ y : ℝ, ((Real.sinc (Real.pi * y) ^ 2 : ℝ) : ℂ)
          * Complex.exp (↑(-(2 * Real.pi * y * (-s))) * Complex.I) := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    rw [hgs]
    simp only
    rw [mul_comm Complex.I ((s * (2 * Real.pi * y) : ℝ) : ℂ)]
    congr 1
    push_cast
    ring_nf
  rw [hgs_eq, Commons.Analysis.Fourier.integral_sinc_pi_sq_mul_exp (-s)]
  rw [Commons.Analysis.Fourier.tri_even]

end Work.GM.Energy.RMoments
