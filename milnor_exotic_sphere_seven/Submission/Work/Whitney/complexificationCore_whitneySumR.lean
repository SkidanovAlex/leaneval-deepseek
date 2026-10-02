import Mathlib
import Submission.Work.Whitney.Basic
import Submission.Work.Whitney.sumFibre_cxTrans

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

/-!
# The complexification of a real direct sum

**Deliverable item 1 of the Whitney subproject.**  For real gluing-data bundles `Z₁, Z₂` over a
common base with standard fibres `ℝ^{k₁}`, `ℝ^{k₂}`, the complexification of their direct sum is the
direct sum of their complexifications:

  `(Z₁ ⊕ Z₂) ⊗_ℝ ℂ = (Z₁ ⊗_ℝ ℂ) ⊕ (Z₂ ⊗_ℝ ℂ)`

as complex gluing data with standard fibre `ℂ^{k₁+k₂}` over the product cover.  This is stronger than
a `Work.Thom.BundleIso`: the two cores are *equal*, because both are the transport, along the same
splitting `sumFibreC k₁ k₂`, of the block-diagonal transition functions
`(T₁ × T₂) ⊗ id = (T₁ ⊗ id) × (T₂ ⊗ id)` — which is
`Work.Whitney.sumFibre_cxTrans` (`Submission/Work/Whitney/sumFibre_cxTrans.lean`).
-/

namespace Work.Whitney

open Work.TangentClasses

noncomputable section

variable {B : Type} [TopologicalSpace B]

theorem complexificationCore_whitneySumR {k₁ k₂ : ℕ} {ι₁ ι₂ : Type}
    (Z₁ : VectorBundleCore ℝ B (EuclideanSpace ℝ (Fin k₁)) ι₁)
    (Z₂ : VectorBundleCore ℝ B (EuclideanSpace ℝ (Fin k₂)) ι₂) :
    Work.Thom.complexificationCore (whitneySumR Z₁ Z₂) =
      whitneySum (Work.Thom.complexificationCore Z₁)
        (Work.Thom.complexificationCore Z₂) := by
  refine Work.Thom.bundleCore_ext rfl rfl (fun p q x => ?_)
  apply ContinuousLinearMap.ext
  intro v
  simp only [Work.Thom.complexificationCore_coordChange,
    sumCore_coordChange_eq_transportEnd]
  exact congrArg (fun f => f v)
    (sumFibre_cxTrans (k₁ := k₁) (k₂ := k₂)
      (Z₁.coordChange p.1 q.1 x) (Z₂.coordChange p.2 q.2 x))

end

end Work.Whitney
