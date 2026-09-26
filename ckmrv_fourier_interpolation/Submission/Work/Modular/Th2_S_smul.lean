import Mathlib
import Submission.Work.Modular.E8ThetaAux

namespace Work.Modular

open UpperHalfPlane
open scoped Real MatrixGroups

/-- The modular `S`-transformation of the Jacobi theta function `Θ₂`:
`Θ₂(-1/τ) = (-i τ)^{1/2} · Θ₄(τ)`.

This is obtained from Mathlib's functional equation for the two-variable Jacobi theta
function `jacobiTheta₂_functional_equation` at `z = 1/2`: it reads
`Θ₄(τ) = 1/(-iτ)^{1/2} · exp(-π i/(4τ)) · Θ₂(-1/τ)`, and `exp(-π i/(4τ))` is precisely the
factor relating `Θ₂(-1/τ)` to `jacobiTheta₂((S • τ)/2) (S • τ)`. -/
theorem Th2_S_smul (τ : ℍ) :
    Work.Modular.Th2 (ModularGroup.S • τ) =
      (-Complex.I * (τ : ℂ)) ^ (1 / 2 : ℂ) * Work.Modular.Th4 τ := by
  -- The action of `S` on `ℍ` sends `τ` to `-1/τ`.
  have hS : ((ModularGroup.S • τ : ℍ) : ℂ) = (-(τ : ℂ))⁻¹ := by
    rw [UpperHalfPlane.modular_S_smul]
  -- The automorphy factor is non-zero.
  have hc : (-Complex.I * (τ : ℂ)) ^ (1 / 2 : ℂ) ≠ 0 := by
    rw [Complex.cpow_ne_zero_iff]
    left
    exact mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) τ.ne_zero
  -- Mathlib's functional equation at `z = 1/2`.
  have hfe := jacobiTheta₂_functional_equation (1/2 : ℂ) (τ : ℂ)
  rw [Th2, Th4, hS]
  -- The two exponential factors agree: `π i (-τ)⁻¹ / 4 = -π i (1/2)² / τ`.
  have hE : Complex.exp (π * Complex.I * (-(τ : ℂ))⁻¹ / 4) =
      Complex.exp (-(π : ℂ) * Complex.I * ((1/2 : ℂ)) ^ 2 / (τ : ℂ)) := by
    congr 1
    field_simp
    ring
  -- The two theta values agree, using evenness of `jacobiTheta₂` in its first variable.
  have hJ : jacobiTheta₂ ((-(τ : ℂ))⁻¹ / 2) (-(τ : ℂ))⁻¹ =
      jacobiTheta₂ ((1/2 : ℂ) / (τ : ℂ)) (-1 / (τ : ℂ)) := by
    have hz : (-(τ : ℂ))⁻¹ / 2 = -(((1/2 : ℂ)) / (τ : ℂ)) := by
      rw [inv_neg]; field_simp
    have hw : (-(τ : ℂ))⁻¹ = -((τ : ℂ)⁻¹) := inv_neg
    rw [hz, hw, jacobiTheta₂_neg_left]
    congr 1
    rw [neg_div, one_div]
  rw [hfe, hE, hJ]
  -- Multiply out and cancel the automorphy factor.
  rw [← mul_assoc, ← mul_assoc, mul_one_div_cancel hc, one_mul]

end Work.Modular
