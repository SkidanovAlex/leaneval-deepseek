import Mathlib
import Submission.Work.Agree.S4Bundle
import Submission.Work.Whitney.Basic
import Submission.Work.Whitney.nonempty_bundleIso_whitneySum_comm
import Submission.Work.Gen.EulerToolkit
import Submission.Work.Thom.manifoldP1

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.Agree

theorem whitneySumR_sum_iso {B : Type} [TopologicalSpace B] {k₁ k₂ : ℕ} {ι₁ ι₂ : Type}
    (Z₁ : Work.TangentClasses.RealBundle B (EuclideanSpace ℝ (Fin k₁)) ι₁)
    (Z₂ : Work.TangentClasses.RealBundle B (EuclideanSpace ℝ (Fin k₂)) ι₂) :
    Nonempty (Work.Thom.BundleIso (Work.Whitney.whitneySumR Z₁ Z₂) (Z₁.sum Z₂)) := by
  refine Work.Whitney.nonempty_bundleIso_of_gauge_fibre
    (Work.Whitney.whitneySumR Z₁ Z₂) (Z₁.sum Z₂)
    ((Work.Whitney.sumFibreR k₁ k₂).symm) (Equiv.refl (ι₁ × ι₂)) ?_ ?_ ?_
  · intro i
    simp only [Work.Whitney.whitneySumR_baseSet, Work.TangentClasses.RealBundle.sum_baseSet,
      Equiv.refl_apply]
  · intro b
    simp only [Work.Whitney.whitneySumR_indexAt, Work.TangentClasses.RealBundle.sum_indexAt,
      Equiv.refl_apply]
  · intro i b
    apply ContinuousLinearMap.ext
    intro v
    simp only [ContinuousLinearMap.comp_apply, Work.Whitney.whitneySumR_coordChange,
      Work.TangentClasses.RealBundle.sum_coordChange, Work.Whitney.whitneySumR_indexAt,
      Work.TangentClasses.RealBundle.sum_indexAt, Equiv.refl_apply,
      ContinuousLinearMap.coe_prodMap', ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.symm_apply_apply]

end Work.Agree
