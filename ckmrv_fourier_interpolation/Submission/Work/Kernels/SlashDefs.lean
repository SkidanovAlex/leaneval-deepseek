/-
# The slash action of `SL(2, ℤ)` on `ℍ → ℂ` and the factor of automorphy

This file collects the elementary facts about the slash operator

  `(F ∣[k] γ) τ = j(γ,τ)^{-k} F (γ • τ)`,  `j(γ,τ) = cτ + d`,

used to prove that the class `𝒫` of `Work.Kernels.InP` is preserved by the slash action
(Lemma "HCmoderategrowthPslashed" of CKMRV, Section 4.1).
-/
import Mathlib
import Submission.Work.Kernels.ModerateGrowth

noncomputable section

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups ModularForm Modular Manifold Bundle

namespace Work.Kernels

/-- The image of `γ ∈ SL(2,ℤ)` in `GL(2, ℝ)`. -/
abbrev glOf (γ : SL(2,ℤ)) : GL (Fin 2) ℝ :=
  Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) γ)

/-- The factor of automorphy `j(γ,τ) = cτ + d` of `γ ∈ SL(2,ℤ)`, as a function of
`z ∈ ℂ`. -/
def jFun (γ : SL(2,ℤ)) (z : ℂ) : ℂ := UpperHalfPlane.denom (glOf γ) z

/-- The numerator `aτ + b` of the Möbius transformation attached to `γ ∈ SL(2,ℤ)`,
as a function of `z ∈ ℂ`. -/
def nFun (γ : SL(2,ℤ)) (z : ℂ) : ℂ := UpperHalfPlane.num (glOf γ) z

lemma glOf_apply (γ : SL(2,ℤ)) (i j : Fin 2) : glOf γ i j = ((γ i j : ℤ) : ℝ) := rfl

lemma jFun_apply (γ : SL(2,ℤ)) (z : ℂ) : jFun γ z = (γ 1 0 : ℂ) * z + (γ 1 1 : ℂ) := rfl

lemma nFun_apply (γ : SL(2,ℤ)) (z : ℂ) : nFun γ z = (γ 0 0 : ℂ) * z + (γ 0 1 : ℂ) := rfl

lemma jFun_ne_zero (γ : SL(2,ℤ)) (τ : ℍ) : jFun γ (τ : ℂ) ≠ 0 :=
  UpperHalfPlane.denom_ne_zero _ τ

/-- The slash action in terms of `jFun`. -/
lemma slash_apply' (F : ℍ → ℂ) (k : ℤ) (γ : SL(2,ℤ)) (τ : ℍ) :
    (F ∣[k] γ) τ = F (γ • τ) * (jFun γ (τ : ℂ)) ^ (-k) := by
  rw [SL_slash_apply]
  rfl

/-- The imaginary part of `γ • τ`. -/
lemma im_smul_eq (γ : SL(2,ℤ)) (τ : ℍ) :
    (γ • τ).im = τ.im / ‖jFun γ (τ : ℂ)‖ ^ 2 := by
  rw [ModularGroup.im_smul_eq_div_normSq, Complex.normSq_eq_norm_sq]
  rfl

/-- The complex number `γ • τ` as a quotient of the linear forms `nFun` and `jFun`. -/
lemma coe_smul_eq (γ : SL(2,ℤ)) (τ : ℍ) :
    ((γ • τ : ℍ) : ℂ) = nFun γ (τ : ℂ) / jFun γ (τ : ℂ) := by
  rw [show ((γ • τ : ℍ) : ℂ) = ((glOf γ) • τ : ℍ) from rfl]
  rw [UpperHalfPlane.coe_smul]
  simp only [σ, Matrix.SpecialLinearGroup.coeToGL_det, Units.val_one, zero_lt_one,
    ↓reduceIte, ContinuousAlgEquiv.refl_apply]
  rfl

lemma norm_slash (F : ℍ → ℂ) (k : ℤ) (γ : SL(2,ℤ)) (τ : ℍ) :
    ‖(F ∣[k] γ) τ‖ = ‖F (γ • τ)‖ * ‖jFun γ (τ : ℂ)‖ ^ (-k) := by
  rw [slash_apply', norm_mul, norm_zpow]

end Work.Kernels
