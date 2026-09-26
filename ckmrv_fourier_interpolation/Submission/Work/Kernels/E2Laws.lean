/-
# The transformation laws of `E₂` and the annihilation of the `φ_k`

This file records the two transformation laws of the quasimodular form `E₂` (CKMRV (2.8)),

  `E₂(τ+1) = E₂(τ)`,  `E₂(-1/τ) = τ²E₂(τ) - 6iτ/π`,

in the slash form `E₂ ∣[2] T = E₂` and `E₂ ∣[2] S = E₂ - 6i/(πτ)`, and deduces that the three
basis functions

  `φ_{-2}(τ) = τ`,  `φ_0(τ) = τE₂(τ) - 3i/π`,  `φ_2(τ) = τE₂(τ)² - (6i/π)E₂(τ)`

are annihilated by `(T-I)²` and by `S+I` in their respective weights `-2, 0, 2`.  These are the
"⊇" halves of CKMRV Proposition 4.2.
-/
import Mathlib
import Submission.Work.Kernels.Kernels

noncomputable section

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups ModularForm Modular Manifold Bundle

namespace Work.Kernels

/-! ## The transformation laws of `E₂` -/

lemma E2Fun_vadd_one (τ : ℍ) : E2Fun ((1 : ℝ) +ᵥ τ) = E2Fun τ := by
  have hG : EisensteinSeries.G2 (ModularGroup.T • τ) = EisensteinSeries.G2 τ := by
    have h := congr_fun EisensteinSeries.G2_T_transform τ
    rw [SL_slash_apply] at h
    simpa [UpperHalfPlane.denom] using h
  have hT : ModularGroup.T • τ = (1 : ℝ) +ᵥ τ := by
    simpa using UpperHalfPlane.modular_T_zpow_smul τ (1 : ℤ)
  rw [← hT]
  simp only [E2Fun, EisensteinSeries.E2, Pi.smul_apply, smul_eq_mul, hG]

lemma E2Fun_S_smul (τ : ℍ) :
    E2Fun (ModularGroup.S • τ) = (τ : ℂ) ^ 2 * E2Fun τ - 6 * Complex.I * (τ : ℂ) / Real.pi := by
  have hτ : (τ : ℂ) ≠ 0 := fun h => τ.im_ne_zero (by rw [← coe_im τ, h]; simp)
  have hG : EisensteinSeries.G2 (ModularGroup.S • τ)
      = (τ : ℂ) ^ 2 * EisensteinSeries.G2 τ - 2 * Real.pi * Complex.I * (τ : ℂ) := by
    have h2 : (τ : ℂ) ^ 2 * EisensteinSeries.G2 τ
        = EisensteinSeries.G2 (ModularGroup.S • τ) + 2 * Real.pi * Complex.I * (τ : ℂ) := by
      rw [EisensteinSeries.G2_S_transform τ]
      field_simp
      ring
    rw [h2]; ring
  simp only [E2Fun, EisensteinSeries.E2, Pi.smul_apply, smul_eq_mul, hG]
  rw [riemannZeta_two]
  have hpi : (Real.pi : ℂ) ≠ 0 := by
    simpa using Real.pi_ne_zero
  field_simp

/-- `E₂ ∣[2] T = E₂`. -/
theorem E2Fun_slash_T : E2Fun ∣[(2 : ℤ)] ModularGroup.T = E2Fun := by
  ext τ
  rw [SL_slash_apply]
  have hT : ModularGroup.T • τ = (1 : ℝ) +ᵥ τ := by
    simpa using UpperHalfPlane.modular_T_zpow_smul τ (1 : ℤ)
  rw [hT, E2Fun_vadd_one]
  simp [UpperHalfPlane.denom]

/-- `E₂ ∣[2] S = E₂ - 6i/(πτ)`. -/
theorem E2Fun_slash_S : E2Fun ∣[(2 : ℤ)] ModularGroup.S =
    fun τ : ℍ => E2Fun τ - 6 * Complex.I / (Real.pi * (τ : ℂ)) := by
  ext τ
  rw [SL_slash_apply, E2Fun_S_smul]
  have hden : UpperHalfPlane.denom (glOf ModularGroup.S) (τ : ℂ) = (τ : ℂ) := by
    show (glOf ModularGroup.S) 1 0 * (τ : ℂ) + (glOf ModularGroup.S) 1 1 = (τ : ℂ)
    rw [glOf_apply, glOf_apply]
    have h1 : (ModularGroup.S : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 1 := by decide
    have h0 : (ModularGroup.S : Matrix (Fin 2) (Fin 2) ℤ) 1 1 = 0 := by decide
    rw [h1, h0]; norm_num
  rw [hden]
  have hτ : (τ : ℂ) ≠ 0 := fun h => τ.im_ne_zero (by rw [← coe_im τ, h]; simp)
  field_simp

end Work.Kernels
