import Mathlib
import Submission.Work.Modular.E8ThetaAux

namespace Work.Modular

open UpperHalfPlane
open scoped Real MatrixGroups

/-- Jacobi's imaginary transformation for `θ₄`, phrased for the `E₈` chapter:
`Θ₄(-1/τ) = (-i τ)^{1/2} Θ₂(τ)`.

This is the specialization `z = τ/2` of Mathlib's two-variable functional equation
`jacobiTheta₂_functional_equation`, together with `jacobiTheta₂ (-z) τ = jacobiTheta₂ z τ`
and the identification `(Θ₂ τ) = exp (π i τ/4) · θ(τ/2; τ)`. -/
theorem Th4_S_smul (τ : ℍ) :
    Work.Modular.Th4 (ModularGroup.S • τ) =
      (-Complex.I * (τ : ℂ)) ^ (1 / 2 : ℂ) * Work.Modular.Th2 τ := by
  have h0 : (τ : ℂ) ≠ 0 := by
    intro h
    have : (τ : ℂ).im = 0 := by rw [h]; simp
    rw [UpperHalfPlane.coe_im] at this
    exact absurd this (ne_of_gt τ.2)
  have hA : (-Complex.I * (τ : ℂ)) ^ (1 / 2 : ℂ) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff, not_and_or]
    exact Or.inl (mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) h0)
  have hτ : (((ModularGroup.S • τ : ℍ)) : ℂ) = (-(τ : ℂ))⁻¹ := by
    rw [UpperHalfPlane.modular_S_smul]
  simp only [Work.Modular.Th4, Work.Modular.Th2, hτ]
  -- Jacobi's functional equation, specialised to `z = τ / 2`, `τ = τ`.
  have hfe := jacobiTheta₂_functional_equation ((τ : ℂ) / 2) (τ : ℂ)
  rw [show (-1:ℂ)/(τ:ℂ) = (-(τ:ℂ))⁻¹ from by rw [neg_div, one_div, inv_neg]] at hfe
  rw [show ((τ:ℂ)/2)/(τ:ℂ) = 1/2 from by field_simp] at hfe
  rw [show -(↑π:ℂ) * Complex.I * ((τ:ℂ)/2)^2 / (τ:ℂ) = -(↑π:ℂ) * Complex.I * (τ:ℂ)/4 from by
        field_simp; ring] at hfe
  have hE : Complex.exp (-(↑π:ℂ) * Complex.I * (τ:ℂ) / 4) ≠ 0 := Complex.exp_ne_zero _
  -- Multiply the functional equation by `(-i τ)^{1/2}`.
  have hmul : (-Complex.I * (τ:ℂ))^(1/2:ℂ) * jacobiTheta₂ ((τ:ℂ)/2) (τ:ℂ)
      = Complex.exp (-(↑π:ℂ) * Complex.I * (τ:ℂ)/4) * jacobiTheta₂ (1/2) (-(τ:ℂ))⁻¹ := by
    rw [hfe]
    field_simp
  have h2 : jacobiTheta₂ (1/2) (-(τ:ℂ))⁻¹
      = (Complex.exp (-(↑π:ℂ) * Complex.I * (τ:ℂ)/4))⁻¹
        * ((-Complex.I * (τ:ℂ))^(1/2:ℂ) * jacobiTheta₂ ((τ:ℂ)/2) (τ:ℂ)) := by
    rw [hmul, ← mul_assoc, inv_mul_cancel₀ hE, one_mul]
  rw [h2]
  rw [show (Complex.exp (-(↑π:ℂ) * Complex.I * (τ:ℂ)/4))⁻¹
        = Complex.exp ((↑π:ℂ) * Complex.I * (τ:ℂ)/4) from by
      rw [← Complex.exp_neg]; ring_nf]
  ring

end Work.Modular
