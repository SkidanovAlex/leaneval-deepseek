import Mathlib
import Submission.Work.Drive.Generic.HeightDefs

namespace Work.Drive.Generic

/-- The height function `q ↦ ⟪v, Φ q⟫` of a `C³` map `Φ` has second derivative
`⟪v, D2 Φ p · ·⟫` at `p`. -/
theorem fderiv_fderiv_height_eq {Φ : ℝ × ℝ → Work.Drive.Generic.E3} (hΦ : ContDiff ℝ 3 Φ)
    (v : Work.Drive.Generic.E3) (p : ℝ × ℝ) (w w' : ℝ × ℝ) :
    fderiv ℝ (fderiv ℝ (fun q => inner ℝ v (Φ q))) p w w' =
      inner ℝ v (Work.Drive.Generic.D2 Φ p w w') := by
  have hΦd : Differentiable ℝ Φ := hΦ.differentiable (by norm_num)
  have hfd : Differentiable ℝ (fderiv ℝ Φ) :=
    (hΦ.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  -- the first derivative of the height, as a continuous linear map
  have hA : ∀ x : ℝ × ℝ, HasFDerivAt (fun q : ℝ × ℝ => inner ℝ v (Φ q))
      ((innerSL ℝ v).comp (fderiv ℝ Φ x)) x := by
    intro x
    have hc : HasFDerivAt (fun _ : ℝ × ℝ => v) (0 : ℝ × ℝ →L[ℝ] E3) x :=
      hasFDerivAt_const v x
    have h := hc.inner ℝ (hΦd x).hasFDerivAt
    refine h.congr_fderiv ?_
    apply ContinuousLinearMap.ext
    intro y
    simp [ContinuousLinearMap.prod_apply, fderivInnerCLM_apply]
  have h1 : fderiv ℝ (fun q : ℝ × ℝ => inner ℝ v (Φ q))
      = fun q => (innerSL ℝ v).comp (fderiv ℝ Φ q) := by
    funext q
    exact (hA q).fderiv
  -- differentiating the first derivative
  have h2 : fderiv ℝ (fun q : ℝ × ℝ => (innerSL ℝ v).comp (fderiv ℝ Φ q)) p
      = (ContinuousLinearMap.compL ℝ (ℝ × ℝ) E3 ℝ (innerSL ℝ v)).comp (D2 Φ p) := by
    have hfun : (fun q : ℝ × ℝ => (innerSL ℝ v).comp (fderiv ℝ Φ q))
        = (fun q : ℝ × ℝ =>
            (ContinuousLinearMap.compL ℝ (ℝ × ℝ) E3 ℝ (innerSL ℝ v)) (fderiv ℝ Φ q)) := by
      funext q
      rw [ContinuousLinearMap.compL_apply]
    rw [hfun]
    have hK : HasFDerivAt (fun L : ℝ × ℝ →L[ℝ] E3 =>
        (ContinuousLinearMap.compL ℝ (ℝ × ℝ) E3 ℝ (innerSL ℝ v)) L)
        (ContinuousLinearMap.compL ℝ (ℝ × ℝ) E3 ℝ (innerSL ℝ v)) (fderiv ℝ Φ p) :=
      (ContinuousLinearMap.compL ℝ (ℝ × ℝ) E3 ℝ (innerSL ℝ v)).hasFDerivAt
    exact (hK.comp p (hfd p).hasFDerivAt).fderiv
  rw [h1, h2]
  simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.compL_apply, innerSL_apply_apply]

end Work.Drive.Generic
