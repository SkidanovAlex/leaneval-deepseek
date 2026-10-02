import Mathlib
import Submission.Work.Gen.EulerStdTangent
import Submission.Work.Gen.EulerSplit
import Submission.Work.TangentClasses.Tangent

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false

/-!
# The change of coordinates of the real tangent bundle of `ℂP⁴` over the standard charts

`Work.Gen.stdTangentReal` is the real tangent bundle of `ℂP⁴` presented over the standard
`Fin 5` chart cover (`Work.Gen.stdChart 4`), whose charts are `euclidChart 4 p = E4 ∘ chartFun p`.

The transition function of the tangent bundle between the charts `p` and `q` is the Fréchet
derivative of the chart transition.  Since the chart transition is `E4 ∘ Phi p q ∘ E4⁻¹`, where
`Phi p q = chartFun q ∘ chartInv p` is the *holomorphic* transition of the affine charts of `ℂP⁴`,
its real derivative is the realification of the complex derivative:

`stdTangentReal.coordChange p q b = E4 ∘ (restrictScalars ℝ (fderiv ℂ (Phi p q) (chartFun p b))) ∘ E4⁻¹`.

This is the identification used to read the complex structure on the real tangent bundle of `ℂP⁴`
off the holomorphic transitions of the projective charts.
-/

namespace Work.Gen

open scoped Manifold ContDiff
open Work.Projective

theorem tangentCoordChange_stdChart :
    ∀ (p q : Fin 5) (b : Work.Projective.CP 4),
      b ∈ Work.Projective.chartSet p ∩ Work.Projective.chartSet q →
      Work.Gen.stdTangentReal.coordChange p q b
      = (Work.Gen.E4 : (Fin 4 → ℂ) →L[ℝ] EuclideanSpace ℝ (Fin 8)).comp
          ((ContinuousLinearMap.restrictScalars ℝ
            (fderiv ℂ (Work.Gen.Phi p q) (Work.Projective.chartFun p b))).comp
            (Work.Gen.E4.symm : EuclideanSpace ℝ (Fin 8) →L[ℝ] (Fin 4 → ℂ))) := by
  intro p q b hb
  have hp : b ∈ chartSet p := hb.1
  have hq : b ∈ chartSet q := hb.2
  -- The tangent-bundle transition is the derivative of `euclidChart q ∘ (euclidChart p)⁻¹`,
  -- which as a function is `E4 ∘ Phi p q ∘ E4⁻¹`.
  have hfun : (↑((Work.Gen.stdChart 4 q).1.extend (𝓡 8))
        ∘ ↑((Work.Gen.stdChart 4 p).1.extend (𝓡 8)).symm)
      = fun y : EuclideanSpace ℝ (Fin 8) =>
          Work.Gen.E4 (Work.Gen.Phi p q (Work.Gen.E4.symm y)) := by
    funext y
    rw [OpenPartialHomeomorph.extend_coe, OpenPartialHomeomorph.extend_coe_symm]
    simp only [Function.comp_apply, modelWithCornersSelf_coe, id_eq]
    simp only [Work.Gen.stdChart, Work.Projective.euclidChart, OpenPartialHomeomorph.trans_apply,
      Work.Projective.chart_toFun, Homeomorph.toOpenPartialHomeomorph_apply,
      OpenPartialHomeomorph.coe_trans_symm, Work.Projective.chart_symm_toFun,
      Homeomorph.toOpenPartialHomeomorph_symm_apply, modelWithCornersSelf_coe_symm]
    rfl
  have hpt : ((Work.Gen.stdChart 4 p).1.extend (𝓡 8)) b = Work.Gen.E4 (chartFun p b) := by
    rw [OpenPartialHomeomorph.extend_coe]
    simp only [Function.comp_apply, modelWithCornersSelf_coe, id_eq]
    simp only [Work.Gen.stdChart, Work.Projective.euclidChart, OpenPartialHomeomorph.trans_apply,
      Work.Projective.chart_toFun, Homeomorph.toOpenPartialHomeomorph_apply]
    rfl
  -- `Phi p q` is holomorphic at the relevant point, so its real derivative is the realification
  -- of its complex derivative; the chain rule then identifies the derivative of the transition.
  have hcp : chartInv p (chartFun p b) = b := chartInv_chartFun p b hp
  have hu : chartInv p (chartFun p b) ∈ chartSet q := by rw [hcp]; exact hq
  have hPhi : HasFDerivAt (Work.Gen.Phi p q)
      (fderiv ℂ (Work.Gen.Phi p q) (chartFun p b)) (chartFun p b) :=
    (Work.Gen.differentiableAt_Phi hu).hasFDerivAt
  have h1 : HasFDerivAt (fun y => Work.Gen.E4.symm y)
      (Work.Gen.E4.symm : EuclideanSpace ℝ (Fin 8) →L[ℝ] (Fin 4 → ℂ))
      (Work.Gen.E4 (chartFun p b)) :=
    (Work.Gen.E4.symm : EuclideanSpace ℝ (Fin 8) →L[ℝ] (Fin 4 → ℂ)).hasFDerivAt
  have h2 : HasFDerivAt (Work.Gen.Phi p q)
      (ContinuousLinearMap.restrictScalars ℝ (fderiv ℂ (Work.Gen.Phi p q) (chartFun p b)))
      (Work.Gen.E4.symm (Work.Gen.E4 (chartFun p b))) := by
    rw [ContinuousLinearEquiv.symm_apply_apply]
    exact hPhi.restrictScalars ℝ
  have h3 : HasFDerivAt (fun z => Work.Gen.E4 z)
      (Work.Gen.E4 : (Fin 4 → ℂ) →L[ℝ] EuclideanSpace ℝ (Fin 8))
      (Work.Gen.Phi p q (Work.Gen.E4.symm (Work.Gen.E4 (chartFun p b)))) :=
    (Work.Gen.E4 : (Fin 4 → ℂ) →L[ℝ] EuclideanSpace ℝ (Fin 8)).hasFDerivAt
  have h21 : HasFDerivAt (fun y => Work.Gen.Phi p q (Work.Gen.E4.symm y))
      ((ContinuousLinearMap.restrictScalars ℝ (fderiv ℂ (Work.Gen.Phi p q) (chartFun p b))).comp
        (Work.Gen.E4.symm : EuclideanSpace ℝ (Fin 8) →L[ℝ] (Fin 4 → ℂ)))
      (Work.Gen.E4 (chartFun p b)) :=
    h2.comp (Work.Gen.E4 (chartFun p b)) h1
  have hchain : HasFDerivAt (fun y => Work.Gen.E4 (Work.Gen.Phi p q (Work.Gen.E4.symm y)))
      ((Work.Gen.E4 : (Fin 4 → ℂ) →L[ℝ] EuclideanSpace ℝ (Fin 8)).comp
        ((ContinuousLinearMap.restrictScalars ℝ (fderiv ℂ (Work.Gen.Phi p q) (chartFun p b))).comp
          (Work.Gen.E4.symm : EuclideanSpace ℝ (Fin 8) →L[ℝ] (Fin 4 → ℂ))))
      (Work.Gen.E4 (chartFun p b)) :=
    h3.comp (Work.Gen.E4 (chartFun p b)) h21
  rw [Work.Gen.stdTangentReal_coordChange]
  simp only [Work.TangentClasses.tangentBundle, tangentBundleCore_coordChange]
  rw [hpt]
  rw [fderivWithin_congr (fun y _ => congrFun hfun y)
    (congrFun hfun (Work.Gen.E4 (chartFun p b)))]
  rw [show Set.range (↑(𝓡 8)) = Set.univ from ModelWithCorners.range_eq_univ (𝓡 8),
    fderivWithin_univ]
  exact hchain.fderiv

end Work.Gen
