import Mathlib
import Submission.Work.LerayHirsch.Twist
import Submission.Work.Whitney.Basic

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

/-!
# Index bookkeeping and the transition-function identity for `L ⊗ (E ⊕ F) ≅ (L ⊗ E) ⊕ (L ⊗ F)`

`Work.LerayHirsch.twistCore L (Work.Whitney.whitneySum E F)` is a gluing datum over the cover
`ιL × (ιE × ιF)` with fibre `ℂ^{n+p}`, while
`Work.Whitney.whitneySum (twistCore L E) (twistCore L F)` is one over the cover
`(ιL × ιE) × (ιL × ιF)` with the same fibre.  This module records:

* `Work.LerayHirsch.diagProdIndex` — the reindexing `(l, (e, f)) ↦ ((l, e), (l, f))`;
* `Work.LerayHirsch.diagProdIndex_baseSet_twistSum`,
  `Work.LerayHirsch.diagProdIndex_indexAt_twistSum` — its compatibility with the base sets and
  with `indexAt`;
* `Work.LerayHirsch.comp_prodMap_smul_comp` — the elementary `ℂ`-linear fact that a scalar multiple
  of a block-diagonal endomorphism is stable under conjugation by a continuous linear equivalence;
* `Work.LerayHirsch.twistCore_whitneySum_coordChange` — **the transition functions of the two
  presentations agree**, which is the mathematical content of the distributivity of the tensor
  product over the direct sum.
-/

namespace Work.LerayHirsch

open Work.TangentClasses Work.Thom

noncomputable section

/-- **The reindexing identifying the cover of `L ⊗ (E ⊕ F)` with that of `(L ⊗ E) ⊕ (L ⊗ F)`**:
`(l, (e, f)) ↦ ((l, e), (l, f))`. -/
def diagProdIndex {α β γ : Type*} : α × (β × γ) → (α × β) × (α × γ) :=
  fun i => ((i.1, i.2.1), (i.1, i.2.2))

@[simp] theorem diagProdIndex_apply {α β γ : Type*} (i : α × (β × γ)) :
    diagProdIndex i = ((i.1, i.2.1), (i.1, i.2.2)) := rfl

theorem diagProdIndex_injective {α β γ : Type*} :
    Function.Injective (@diagProdIndex α β γ) := by
  rintro ⟨a, b, c⟩ ⟨a', b', c'⟩ h
  simp only [diagProdIndex_apply, Prod.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  obtain ⟨h11, h12⟩ := h1
  obtain ⟨h21, h22⟩ := h2
  simp [h11, h12, h22]

variable {B : Type} [TopologicalSpace B] {ιL ιE ιF : Type} {n p : ℕ}

/-- **The base sets of the two presentations of `L ⊗ (E ⊕ F)` agree** under `diagProdIndex`. -/
theorem diagProdIndex_baseSet_twistSum
    (L : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ιL)
    (E : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin n)) ιE)
    (F : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin p)) ιF)
    (i : ιL × (ιE × ιF)) :
    (Work.Whitney.whitneySum (twistCore L E) (twistCore L F)).baseSet (diagProdIndex i)
      = (twistCore L (Work.Whitney.whitneySum E F)).baseSet i := by
  ext x
  simp only [Work.Whitney.whitneySum_baseSet, twistCore_baseSet, diagProdIndex_apply,
    Set.mem_inter_iff]
  tauto

/-- **The base points of the two presentations of `L ⊗ (E ⊕ F)` agree** under `diagProdIndex`. -/
theorem diagProdIndex_indexAt_twistSum
    (L : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ιL)
    (E : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin n)) ιE)
    (F : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin p)) ιF)
    (b : B) :
    (Work.Whitney.whitneySum (twistCore L E) (twistCore L F)).indexAt b
      = diagProdIndex ((twistCore L (Work.Whitney.whitneySum E F)).indexAt b) := by
  simp only [Work.Whitney.whitneySum_indexAt, twistCore_indexAt, diagProdIndex_apply]

/-- **A scalar multiple of a block-diagonal endomorphism is stable under conjugation** by a
continuous linear equivalence: `e ∘ ((c·T₁) × (c·T₂)) ∘ e⁻¹ = c · (e ∘ (T₁ × T₂) ∘ e⁻¹)`. -/
theorem comp_prodMap_smul_comp (c : ℂ) {F₁ F₂ G : Type*} [NormedAddCommGroup F₁]
    [NormedSpace ℂ F₁] [NormedAddCommGroup F₂] [NormedSpace ℂ F₂] [NormedAddCommGroup G]
    [NormedSpace ℂ G] (e : (F₁ × F₂) ≃L[ℂ] G) (T₁ : F₁ →L[ℂ] F₁) (T₂ : F₂ →L[ℂ] F₂) :
    ((e : (F₁ × F₂) →L[ℂ] G)).comp
        (((c • T₁).prodMap (c • T₂)).comp ((e.symm : G →L[ℂ] (F₁ × F₂))))
      = c • (((e : (F₁ × F₂) →L[ℂ] G)).comp
        ((T₁.prodMap T₂).comp ((e.symm : G →L[ℂ] (F₁ × F₂))))) := by
  apply ContinuousLinearMap.ext
  intro v
  have h : Prod.map (⇑(c • T₁)) (⇑(c • T₂)) (e.symm v)
      = c • (Prod.map (⇑T₁) (⇑T₂) (e.symm v)) := by
    obtain ⟨a, b⟩ := e.symm v
    simp
  show e (Prod.map (⇑(c • T₁)) (⇑(c • T₂)) (e.symm v))
      = c • e (Prod.map (⇑T₁) (⇑T₂) (e.symm v))
  rw [h, map_smul]

/-- **The transition functions of the two presentations of `L ⊗ (E ⊕ F)` agree.**  This is the
identity expressing that the tensor product of a line bundle distributes over the direct sum:
unfolded, it says that `sumFibreC ∘ ((scl λ • E_ij) × (scl λ • F_ij)) ∘ sumFibreC⁻¹` equals
`scl λ • (sumFibreC ∘ (E_ij × F_ij) ∘ sumFibreC⁻¹)`. -/
theorem twistCore_whitneySum_coordChange
    (L : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ιL)
    (E : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin n)) ιE)
    (F : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin p)) ιF)
    (i : ιL × (ιE × ιF)) (b : B) :
    (Work.Whitney.whitneySum (twistCore L E) (twistCore L F)).coordChange
        ((Work.Whitney.whitneySum (twistCore L E) (twistCore L F)).indexAt b)
        (diagProdIndex i) b
      = (twistCore L (Work.Whitney.whitneySum E F)).coordChange
        ((twistCore L (Work.Whitney.whitneySum E F)).indexAt b) i b := by
  simp only [Work.Whitney.whitneySum_coordChange, Work.Whitney.whitneySum_indexAt,
    twistCore_coordChange, twistCore_indexAt, diagProdIndex_apply]
  exact comp_prodMap_smul_comp _ _ _ _

end

end Work.LerayHirsch
