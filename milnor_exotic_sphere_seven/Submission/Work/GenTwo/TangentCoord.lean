import Mathlib
import Submission.Work.GenTwo.Split
import Submission.Work.Gen.EulerStdTangent
import Submission.Work.TangentClasses.Tangent

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-!
# The change of coordinates of the real tangent bundle of `ℂPⁿ` over the standard charts

Dimension-`n` version of `Submission/Work/Gen/tangentCoordChange_stdChart.lean` (the case `n = 4`):
the transition function of the tangent bundle between the standard Euclidean charts `p` and `q` is
the realification of the complex derivative of the holomorphic chart transition `Phi p q`.
-/

namespace Work.Gen.E2

open scoped Manifold ContDiff
open Work.Projective Work.TangentClasses

noncomputable section

variable {n : ℕ}

/-- The (real) tangent bundle of `ℂPⁿ` over the standard Euclidean chart cover. -/
def stdTangentRealN (n : ℕ) : RealBundle (CP n) (EuclideanSpace ℝ (Fin (2 * n))) (Fin (n + 1)) :=
  (Work.TangentClasses.tangentBundle 𝓘(ℝ, EuclideanSpace ℝ (Fin (2 * n))) (CP n)).reindex
    (stdChart n) (stdChart_covers n)

theorem stdTangentRealN_baseSet (n : ℕ) (p : Fin (n + 1)) :
    (stdTangentRealN n).baseSet p = chartSet p := by
  show (Work.TangentClasses.tangentBundle 𝓘(ℝ, EuclideanSpace ℝ (Fin (2 * n))) (CP n)).baseSet
    (stdChart n p) = chartSet p
  rw [Work.TangentClasses.tangentBundle_baseSet, stdChart_source]

theorem stdTangentRealN_coordChange (n : ℕ) (p q : Fin (n + 1)) (b : CP n) :
    (stdTangentRealN n).coordChange p q b
      = (Work.TangentClasses.tangentBundle 𝓘(ℝ, EuclideanSpace ℝ (Fin (2 * n))) (CP n)).coordChange
          (stdChart n p) (stdChart n q) b := rfl

/-- **The tangent-bundle transition is the derivative of the holomorphic chart transition.** -/
theorem tangentCoordChange_stdChart_gen :
    ∀ (n : ℕ) (p q : Fin (n + 1)) (b : Work.Projective.CP n),
      b ∈ Work.Projective.chartSet p ∩ Work.Projective.chartSet q →
      (Work.Gen.E2.stdTangentRealN n).coordChange p q b
      = (Work.Gen.E2.E n : (Fin n → ℂ) →L[ℝ] EuclideanSpace ℝ (Fin (2 * n))).comp
          ((ContinuousLinearMap.restrictScalars ℝ
            (fderiv ℂ (Work.Gen.Phi p q) (Work.Projective.chartFun p b))).comp
            ((Work.Gen.E2.E n).symm : EuclideanSpace ℝ (Fin (2 * n)) →L[ℝ] (Fin n → ℂ))) := by
  intro n p q b hb
  have hp : b ∈ chartSet p := hb.1
  have hq : b ∈ chartSet q := hb.2
  have hfun : (↑((stdChart n q).1.extend (𝓡 (2 * n)))
        ∘ ↑((stdChart n p).1.extend (𝓡 (2 * n))).symm)
      = fun y : EuclideanSpace ℝ (Fin (2 * n)) =>
          E n (Phi p q ((E n).symm y)) := by
    funext y
    rw [OpenPartialHomeomorph.extend_coe, OpenPartialHomeomorph.extend_coe_symm]
    simp only [Function.comp_apply, modelWithCornersSelf_coe, id_eq]
    simp only [Work.Gen.stdChart, Work.Projective.euclidChart, OpenPartialHomeomorph.trans_apply,
      Work.Projective.chart_toFun, Homeomorph.toOpenPartialHomeomorph_apply,
      OpenPartialHomeomorph.coe_trans_symm, Work.Projective.chart_symm_toFun,
      Homeomorph.toOpenPartialHomeomorph_symm_apply, modelWithCornersSelf_coe_symm]
    rfl
  have hpt : ((stdChart n p).1.extend (𝓡 (2 * n))) b = E n (chartFun p b) := by
    rw [OpenPartialHomeomorph.extend_coe]
    simp only [Function.comp_apply, modelWithCornersSelf_coe, id_eq]
    simp only [Work.Gen.stdChart, Work.Projective.euclidChart, OpenPartialHomeomorph.trans_apply,
      Work.Projective.chart_toFun, Homeomorph.toOpenPartialHomeomorph_apply]
    rfl
  have hcp : chartInv p (chartFun p b) = b := chartInv_chartFun p b hp
  have hu : chartInv p (chartFun p b) ∈ chartSet q := by rw [hcp]; exact hq
  have hPhi : HasFDerivAt (Phi p q)
      (fderiv ℂ (Phi p q) (chartFun p b)) (chartFun p b) :=
    (differentiableAt_Phi hu).hasFDerivAt
  have h1 : HasFDerivAt (fun y => (E n).symm y)
      ((E n).symm : EuclideanSpace ℝ (Fin (2 * n)) →L[ℝ] (Fin n → ℂ))
      (E n (chartFun p b)) :=
    ((E n).symm : EuclideanSpace ℝ (Fin (2 * n)) →L[ℝ] (Fin n → ℂ)).hasFDerivAt
  have h2 : HasFDerivAt (Phi p q)
      (ContinuousLinearMap.restrictScalars ℝ (fderiv ℂ (Phi p q) (chartFun p b)))
      ((E n).symm (E n (chartFun p b))) := by
    rw [ContinuousLinearEquiv.symm_apply_apply]
    exact hPhi.restrictScalars ℝ
  have h3 : HasFDerivAt (fun z => E n z)
      (E n : (Fin n → ℂ) →L[ℝ] EuclideanSpace ℝ (Fin (2 * n)))
      (Phi p q ((E n).symm (E n (chartFun p b)))) :=
    (E n : (Fin n → ℂ) →L[ℝ] EuclideanSpace ℝ (Fin (2 * n))).hasFDerivAt
  have h21 : HasFDerivAt (fun y => Phi p q ((E n).symm y))
      ((ContinuousLinearMap.restrictScalars ℝ (fderiv ℂ (Phi p q) (chartFun p b))).comp
        ((E n).symm : EuclideanSpace ℝ (Fin (2 * n)) →L[ℝ] (Fin n → ℂ)))
      (E n (chartFun p b)) :=
    h2.comp (E n (chartFun p b)) h1
  have hchain : HasFDerivAt (fun y => E n (Phi p q ((E n).symm y)))
      ((E n : (Fin n → ℂ) →L[ℝ] EuclideanSpace ℝ (Fin (2 * n))).comp
        ((ContinuousLinearMap.restrictScalars ℝ (fderiv ℂ (Phi p q) (chartFun p b))).comp
          ((E n).symm : EuclideanSpace ℝ (Fin (2 * n)) →L[ℝ] (Fin n → ℂ))))
      (E n (chartFun p b)) :=
    h3.comp (E n (chartFun p b)) h21
  rw [stdTangentRealN_coordChange]
  simp only [Work.TangentClasses.tangentBundle, tangentBundleCore_coordChange]
  rw [hpt]
  rw [fderivWithin_congr (fun y _ => congrFun hfun y)
    (congrFun hfun (E n (chartFun p b)))]
  rw [show Set.range (↑(𝓡 (2 * n))) = Set.univ from ModelWithCorners.range_eq_univ (𝓡 (2 * n)),
    fderivWithin_univ]
  exact hchain.fderiv

end

end Work.Gen.E2
