import Mathlib
import Submission.Work.Whitney.BumpModel.Defs
import Submission.Work.Whitney.BumpModel.structMap_immersion_infty

namespace Work.Whitney.BumpModel

open scoped Manifold ContDiff
open Set Filter Topology

open Work.Whitney

/-- The scaled cut-off model `bumpPlus n χ ρ : x ↦ ρ • structMap n χ (ρ⁻¹ • x)` is `C^∞` whenever
`χ` is, and its derivative is the derivative of `structMap n χ` at the rescaled point: the two
scalar multiplications by `ρ` and `ρ⁻¹` cancel in the derivative. -/
theorem bumpPlus_fderiv_smooth (n : ℕ) [NeZero n] {χ : (Fin n → ℝ) → ℝ} (hχ : ContDiff ℝ ∞ χ)
    {ρ : ℝ} (hρ : ρ ≠ 0) :
    ContDiff ℝ ∞ (bumpPlus n χ ρ) ∧
      (∀ x : Fin n → ℝ,
        fderiv ℝ (bumpPlus n χ ρ) x = fderiv ℝ (structMap n χ) (ρ⁻¹ • x)) := by
  -- `û = χ/(1 + ∑ xᵢ²)` and hence `structMap n χ` are smooth as soon as `χ` is
  have hstruct : ContDiff ℝ ∞ (structMap n χ) := by
    unfold structMap
    have h : ContDiff ℝ ∞ (uhat n χ) := contDiff_uhat_smooth n hχ
    fun_prop
  constructor
  · -- `bumpPlus n χ ρ` is the composite of the smooth maps `ρ⁻¹ • ·`, `structMap n χ`, `ρ • ·`
    have hin : ContDiff ℝ ∞ (fun y : Fin n → ℝ => ρ⁻¹ • y) :=
      contDiff_id.const_smul (ρ⁻¹)
    exact (hstruct.comp hin).const_smul ρ
  · intro x
    -- the model is differentiable at the rescaled point
    have hD : HasFDerivAt (structMap n χ)
        (fderiv ℝ (structMap n χ) (ρ⁻¹ • x)) (ρ⁻¹ • x) :=
      (hstruct.differentiable (by simp)).differentiableAt.hasFDerivAt
    -- the inner rescaling `y ↦ ρ⁻¹ • y` is linear with derivative `ρ⁻¹ • 1`
    have hinner : HasFDerivAt (fun y : Fin n → ℝ => ρ⁻¹ • y)
        ((ρ⁻¹) • (1 : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))) x :=
      (hasFDerivAt_id x).const_smul (ρ⁻¹)
    have hcomp : HasFDerivAt (fun y : Fin n → ℝ => structMap n χ (ρ⁻¹ • y))
        ((fderiv ℝ (structMap n χ) (ρ⁻¹ • x)).comp
          ((ρ⁻¹) • (1 : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)))) x :=
      hD.comp x hinner
    have hsm : HasFDerivAt (fun y : Fin n → ℝ => ρ • structMap n χ (ρ⁻¹ • y))
        (ρ • ((fderiv ℝ (structMap n χ) (ρ⁻¹ • x)).comp
          ((ρ⁻¹) • (1 : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))))) x :=
      hcomp.const_smul ρ
    have hfinal : HasFDerivAt (bumpPlus n χ ρ)
        (ρ • ((fderiv ℝ (structMap n χ) (ρ⁻¹ • x)).comp
          ((ρ⁻¹) • (1 : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))))) x := hsm
    -- the two scalar multiplications cancel
    have hkey : ρ • ((fderiv ℝ (structMap n χ) (ρ⁻¹ • x)).comp
          ((ρ⁻¹) • (1 : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))))
        = fderiv ℝ (structMap n χ) (ρ⁻¹ • x) := by
      apply ContinuousLinearMap.ext
      intro v
      simp only [smul_apply, ContinuousLinearMap.comp_apply, one_apply_eq_self, map_smul,
        smul_smul]
      rw [mul_inv_cancel₀ hρ, one_smul]
    rw [hfinal.fderiv, hkey]

end Work.Whitney.BumpModel
