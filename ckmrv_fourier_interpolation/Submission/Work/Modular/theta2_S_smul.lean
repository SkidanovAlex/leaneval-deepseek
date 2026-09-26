import Mathlib
import Submission.Work.Modular.ThetaFuncs

/-!
# Jacobi's imaginary transformation for `θ₂`

`θ₂(-1/τ) = (-i τ)^{1/2} · θ₄(τ)`.

Here `θ₂(τ) = ∑_{n ∈ ℤ} exp (π i τ (n + 1/2)²)` and `θ₄(τ) = ∑_{n ∈ ℤ} (-1)^n exp (π i τ n²)`
are the definitions of `Work.Modular.theta2` and `Work.Modular.theta4` from
`Submission.Work.Modular.ThetaFuncs`, i.e.

`theta2 τ = exp (π i τ / 4) · jacobiTheta₂ (τ/2) τ`, `theta4 τ = jacobiTheta₂ (1/2) τ`.

The proof is the specialisation `z = 1/2` of Mathlib's two-variable functional equation
`jacobiTheta₂_functional_equation`,

`jacobiTheta₂ z τ = 1/(-i τ)^{1/2} · exp(-π i z²/τ) · jacobiTheta₂ (z/τ) (-1/τ)`:

taking `z = 1/2` and multiplying by `(-i τ)^{1/2} · exp(π i (-1/τ)/4)` turns the right hand
side into `(-i τ)^{1/2} · θ₄(τ)`, because the exponential factors combine to `1` and
`jacobiTheta₂ ((-1/τ)/2) (-1/τ) = jacobiTheta₂ ((1/2)/τ) (-1/τ)` by evenness of `jacobiTheta₂`
in its first variable.

(The functions `Work.Modular.theta2` and `Work.Modular.theta4` are definitionally equal to
`Work.Modular.Th2` and `Work.Modular.Th4` of `Submission.Work.Modular.E8ThetaAux`; the proof
below is nevertheless self-contained, using only Mathlib.)
-/

open UpperHalfPlane
open scoped Real MatrixGroups

namespace Work.Modular

theorem theta2_S_smul (τ : UpperHalfPlane) :
    Work.Modular.theta2 (ModularGroup.S • τ) =
      (-Complex.I * (τ : ℂ)) ^ (1 / 2 : ℂ) * Work.Modular.theta4 τ := by
  -- The action of `S` on `ℍ` sends `τ` to `-1/τ`.
  have hS : (((ModularGroup.S • τ : ℍ)) : ℂ) = (-(τ : ℂ))⁻¹ := by
    rw [UpperHalfPlane.modular_S_smul]
  -- The automorphy factor is non-zero.
  have hc : (-Complex.I * (τ : ℂ)) ^ (1 / 2 : ℂ) ≠ 0 := by
    rw [Complex.cpow_ne_zero_iff]
    exact Or.inl (mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) τ.ne_zero)
  have hfe := jacobiTheta₂_functional_equation (1/2 : ℂ) (τ : ℂ)
  rw [Work.Modular.theta2, Work.Modular.theta4, hS]
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
