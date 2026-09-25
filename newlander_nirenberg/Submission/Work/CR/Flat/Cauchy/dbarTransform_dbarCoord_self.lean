import Mathlib
import Submission.Work.CR.Flat.Cauchy.openSolDefs
import Submission.Work.CR.Flat.Cauchy.dbarC_cauchyTransform

/-!
# The Cauchy-type transform is a left inverse of `∂̄` in one coordinate

`Work.CR.Flat.Cauchy.dbarTransform ρ j` is the (unsubtracted) Cauchy potential in the `j`-th
coordinate.  The main statement `dbarTransform_dbarCoord_self` proves that it inverts the
`j`-th `∂̄`-operator on functions that vanish near the boundary of the disc: for `g` of class
`C¹` with `g y = 0` whenever `‖y j‖ ≥ ρ/2`, and `‖z j‖ < ρ/2`,

  `-(1/π) ∫_{‖w‖<ρ} (∂̄_j g)(z + w e_j)/w dw = g z`.

The proof reduces to the one-variable Pompeiu formula for the `j`-th slice
`F ζ = g (z with `j`-th coordinate `= ζ)`:  the `j`-th `∂̄`-derivative of `g` at the slice
equals `∂̄F`, and `F` is supported in the disc of radius `ρ/2` (and `‖z j‖ < ρ/2`), so the
shifted Cauchy–Green formula `cauchyGreen_shift` computes the integral as `F (z j) = g z`.
-/

namespace Work.CR.Flat.Cauchy

open scoped NNReal ENNReal
open MeasureTheory Set

/-- The `j`-th slice `ζ ↦ Function.update z j ζ : ℂ → ℂⁿ` is affine with linear part the
coordinate inclusion `ContinuousLinearMap.single ℝ (fun _ : Fin n => ℂ) j`. -/
private lemma hasFDerivAt_updateSlice {n : ℕ} (z : Fin n → ℂ) (c : Fin n) (w : ℂ) :
    HasFDerivAt (fun w : ℂ => Function.update z c w)
      (ContinuousLinearMap.single ℝ (fun _ : Fin n => ℂ) c) w := by
  have hfun : (fun w : ℂ => Function.update z c w)
      = fun w : ℂ => Function.update z c 0 +
          (ContinuousLinearMap.single ℝ (fun _ : Fin n => ℂ) c) w := by
    funext v
    rw [ContinuousLinearMap.single_apply]
    ext i
    by_cases h : i = c <;> simp [h]
  rw [hfun]
  exact (ContinuousLinearMap.hasFDerivAt (ContinuousLinearMap.single ℝ (fun _ : Fin n => ℂ) c)
    (x := w)).const_add (Function.update z c 0)

private lemma single_apply_eq {n : ℕ} (c : Fin n) (τ : ℂ) :
    (ContinuousLinearMap.single ℝ (fun _ : Fin n => ℂ) c) τ = Pi.single c τ :=
  congrFun (ContinuousLinearMap.single_apply ℝ (fun _ : Fin n => ℂ) c) τ

/-- The chain rule identity connecting `∂̄` in the `j`-th coordinate with the one-variable
`∂̄` of the slice: `∂̄ (ζ ↦ g (z with j-th coordinate ζ)) = (∂̄_j g)` on the slice. -/
private lemma dbarC_slice_eq_dbarCoord {n : ℕ} (j : Fin n) {g : (Fin n → ℂ) → ℂ}
    (hg : ContDiff ℝ 1 g) (z : Fin n → ℂ) (ζ : ℂ) :
    dbarC (fun ζ' : ℂ => g (Function.update z j ζ')) ζ
      = dbarCoord j g (Function.update z j ζ) := by
  have hd : DifferentiableAt ℝ g (Function.update z j ζ) :=
    (hg.differentiable one_ne_zero) _
  have hfd : fderiv ℝ (fun ζ' : ℂ => g (Function.update z j ζ')) ζ
      = (fderiv ℝ g (Function.update z j ζ)).comp
          (ContinuousLinearMap.single ℝ (fun _ : Fin n => ℂ) j) :=
    (hd.hasFDerivAt.comp ζ (hasFDerivAt_updateSlice z j ζ)).fderiv
  rw [dbarC, dbarCoord, hfd]
  simp only [ContinuousLinearMap.comp_apply]
  rw [single_apply_eq, single_apply_eq]

theorem dbarTransform_dbarCoord_self {n : ℕ} {ρ : ℝ} (hρ : 0 < ρ) (j : Fin n)
    {g : (Fin n → ℂ) → ℂ} (hg : ContDiff ℝ 1 g)
    (hsupp : ∀ y : Fin n → ℂ, ρ / 2 ≤ ‖y j‖ → g y = 0) {z : Fin n → ℂ} (hz : ‖z j‖ < ρ / 2) :
    dbarTransform ρ j (fun y => dbarCoord j g y) z = g z := by
  set F : ℂ → ℂ := fun ζ => g (Function.update z j ζ) with hF
  have hFcd : ContDiff ℝ 1 F := by
    rw [hF]
    refine hg.comp ?_
    have hfun : (Function.update z j : ℂ → Fin n → ℂ)
        = fun ζ : ℂ => Function.update z j 0 +
            (ContinuousLinearMap.single ℝ (fun _ : Fin n => ℂ) j) ζ := by
      funext v
      rw [ContinuousLinearMap.single_apply]
      ext i
      by_cases h : i = j <;> simp [h]
    rw [hfun]
    exact contDiff_const.add (ContinuousLinearMap.contDiff _)
  have hFsupp : SupportedInBall (ρ / 2) F := by
    intro ζ hζ
    rw [hF]
    apply hsupp
    have huj : (Function.update z j ζ) j = ζ := by simp
    rw [huj]; exact hζ
  have hInt : IntegrableOn (fun w : ℂ => dbarC F (z j + w) / w) (Metric.ball 0 ρ) :=
    integrableOn_div_of_continuous
      ((continuous_dbarC hFcd).comp (continuous_const.add continuous_id)) ρ
  have hkey : cauchyTransformUnsub ρ (dbarC F) (z j) = F (z j) := by
    rw [← cauchyTransform_eq_unsub hInt]
    exact cauchyGreen_shift hρ hFcd hFsupp hz
  have hpt : ∀ w : ℂ, dbarCoord j g (z + Function.update (0 : Fin n → ℂ) j w)
      = dbarC F (z j + w) := by
    intro w
    have hupd : z + Function.update (0 : Fin n → ℂ) j w = Function.update z j (z j + w) := by
      funext i
      by_cases h : i = j <;> simp [Pi.add_apply, h]
    rw [hupd]
    exact (dbarC_slice_eq_dbarCoord j hg z (z j + w)).symm
  unfold dbarTransform
  have hcongr : (∫ w in Metric.ball (0 : ℂ) ρ,
        (fun y : Fin n → ℂ => dbarCoord j g y)
          (z + Function.update (0 : Fin n → ℂ) j w) / w)
      = ∫ w in Metric.ball (0 : ℂ) ρ, dbarC F (z j + w) / w := by
    apply setIntegral_congr_fun measurableSet_ball
    intro w _
    show dbarCoord j g (z + Function.update (0 : Fin n → ℂ) j w) / w
      = dbarC F (z j + w) / w
    rw [hpt w]
  rw [hcongr]
  change cauchyTransformUnsub ρ (dbarC F) (z j) = g z
  rw [hkey, hF]
  simp

end Work.CR.Flat.Cauchy
