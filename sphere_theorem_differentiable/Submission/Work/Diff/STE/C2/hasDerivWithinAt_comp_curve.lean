import Mathlib

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option backward.isDefEq.respectTransparency false

namespace Work.Diff.STE.C2

/-- **Chain rule along a curve, evaluated form.**

If `γ : ℝ → M` has within-derivative `(1 : ℝ →L[ℝ] ℝ).smulRight v` at `t` along `J`, and
`ψ : M → F` is differentiable at `γ t`, then `s ↦ ψ (γ s)` has within-derivative
`mvfderiv I ψ (γ t) v` at `t` along `J`. -/
theorem hasDerivWithinAt_comp_curve
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {ψ : M → F} {γ : ℝ → M} {J : Set ℝ} {t : ℝ} {v : TangentSpace I (γ t)}
    (hγ : HasMFDerivWithinAt (modelWithCornersSelf ℝ ℝ) I γ J t
      ((1 : ℝ →L[ℝ] ℝ).smulRight v))
    (hψ : MDifferentiableAt I (modelWithCornersSelf ℝ F) ψ (γ t)) :
    HasDerivWithinAt (fun s : ℝ ↦ ψ (γ s)) (mvfderiv I ψ (γ t) v) J t := by
  rw [hasDerivWithinAt_iff_hasFDerivWithinAt]
  -- chain rule for manifold derivatives, with the outer map evaluated at `γ t`
  have hcomp := HasMFDerivAt.comp_hasMFDerivWithinAt t hψ.hasMFDerivAt hγ
  -- the composite derivative `mfderiv ψ (γ t) ∘ (1).smulRight v` is `(1).smulRight (mvfderiv ψ (γ t) v)`
  have key : (mfderiv I (modelWithCornersSelf ℝ F) ψ (γ t) ∘SL
      (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) v))
      = ContinuousLinearMap.toSpanSingleton ℝ (mvfderiv I ψ (γ t) v) := by
    rw [show mvfderiv I ψ (γ t) v = mfderiv I (modelWithCornersSelf ℝ F) ψ (γ t) v from rfl]
    rw [ContinuousLinearMap.smulRight_one_eq_toSpanSingleton ℝ v]
    exact ContinuousLinearMap.comp_toSpanSingleton _ v
  exact hcomp.hasFDerivWithinAt.congr_fderiv key

end Work.Diff.STE.C2
