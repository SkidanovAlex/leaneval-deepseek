import Mathlib
import Submission.Work.BoseBoxFock.boxSmoothAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END
set_option synthInstance.maxSize 1024
set_option synthInstance.maxHeartbeats 400000

namespace Work.BoseBoxFock

theorem boxPiSet_sum_setIntegral {τ₁ τ₂ : Type*} [Fintype τ₁] [Fintype τ₂] {ℓ : ℝ} (hℓ : 0 < ℓ)
    (G : (τ₁ ⊕ τ₂ → EuclideanSpace ℝ (Fin 3)) → ℝ) (hG : Continuous G) :
    (∫ a in Work.BoseBoxFock.boxPiSet (τ₁ ⊕ τ₂) ℓ, G a)
      = ∫ b in Work.BoseBoxFock.boxPiSet τ₁ ℓ, ∫ c in Work.BoseBoxFock.boxPiSet τ₂ ℓ,
          G (Sum.elim b c) := by
  -- The measurable equivalence identifying functions on `τ₁ ⊕ τ₂` with pairs of functions.
  let ee : ((τ₁ ⊕ τ₂) → EuclideanSpace ℝ (Fin 3)) ≃ᵐ
      ((τ₁ → EuclideanSpace ℝ (Fin 3)) × (τ₂ → EuclideanSpace ℝ (Fin 3))) :=
    MeasurableEquiv.sumPiEquivProdPi (fun _ : τ₁ ⊕ τ₂ => EuclideanSpace ℝ (Fin 3))
  -- It maps the box over `τ₁ ⊕ τ₂` onto the product of the boxes.
  have himg : ee '' boxPiSet (τ₁ ⊕ τ₂) ℓ
      = boxPiSet τ₁ ℓ ×ˢ boxPiSet τ₂ ℓ := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine Set.mem_prod.mpr ⟨mem_boxPiSet.mpr (fun i => ?_), mem_boxPiSet.mpr (fun j => ?_)⟩
      · exact mem_boxPiSet.mp hx (Sum.inl i)
      · exact mem_boxPiSet.mp hx (Sum.inr j)
    · intro hz
      obtain ⟨hz1, hz2⟩ := Set.mem_prod.mp hz
      refine ⟨Sum.elim z.1 z.2, ?_, ?_⟩
      · refine mem_boxPiSet.mpr (fun k => ?_)
        cases k with
        | inl i => exact mem_boxPiSet.mp hz1 i
        | inr j => exact mem_boxPiSet.mp hz2 j
      · show (Equiv.sumPiEquivProdPi (fun _ : τ₁ ⊕ τ₂ => EuclideanSpace ℝ (Fin 3)))
          (Sum.elim z.1 z.2) = z
        simp only [Equiv.sumPiEquivProdPi_apply]
        exact Prod.ext (funext fun i => rfl) (funext fun j => rfl)
  -- `ee` is measure preserving for the product (Haar) measures.
  have hmp : MeasureTheory.MeasurePreserving ee MeasureTheory.volume MeasureTheory.volume :=
    MeasureTheory.volume_measurePreserving_sumPiEquivProdPi _
  -- Change of variables along `ee`: the integral over the box becomes an integral over the
  -- product of the boxes against the "reassembled" configuration.
  have hkey : (∫ y in boxPiSet τ₁ ℓ ×ˢ boxPiSet τ₂ ℓ, G (ee.symm y))
      = ∫ x in boxPiSet (τ₁ ⊕ τ₂) ℓ, G x := by
    have h := hmp.setIntegral_image_emb (MeasurableEquiv.measurableEmbedding ee)
      (fun z => G (ee.symm z)) (boxPiSet (τ₁ ⊕ τ₂) ℓ)
    rw [himg] at h
    rw [h]
    simp
  -- Fubini for the product measure, on the compact product of boxes.
  have hf : MeasureTheory.IntegrableOn
      (fun y : (τ₁ → EuclideanSpace ℝ (Fin 3)) × (τ₂ → EuclideanSpace ℝ (Fin 3)) =>
        G (Sum.elim y.1 y.2))
      (boxPiSet τ₁ ℓ ×ˢ boxPiSet τ₂ ℓ)
      (MeasureTheory.volume.prod MeasureTheory.volume) := by
    have hc : Continuous (fun y : (τ₁ → EuclideanSpace ℝ (Fin 3)) ×
        (τ₂ → EuclideanSpace ℝ (Fin 3)) => Sum.elim y.1 y.2) := by
      rw [continuous_pi_iff]
      intro k
      cases k with
      | inl i => exact (continuous_apply i).comp continuous_fst
      | inr j => exact (continuous_apply j).comp continuous_snd
    have hcomp : IsCompact (boxPiSet τ₁ ℓ ×ˢ boxPiSet τ₂ ℓ) :=
      (isCompact_boxPiSet hℓ).prod (isCompact_boxPiSet hℓ)
    exact ContinuousOn.integrableOn_compact (μ := MeasureTheory.volume) hcomp
      (hG.comp hc).continuousOn
  have hsymm : ∀ y : (τ₁ → EuclideanSpace ℝ (Fin 3)) × (τ₂ → EuclideanSpace ℝ (Fin 3)),
      ee.symm y = Sum.elim y.1 y.2 := by
    intro y
    funext t
    show (Equiv.sumPiEquivProdPi (fun _ : τ₁ ⊕ τ₂ => EuclideanSpace ℝ (Fin 3))).symm y t
      = Sum.elim y.1 y.2 t
    rw [Equiv.sumPiEquivProdPi_symm_apply]
    rfl
  rw [← hkey]
  simp only [hsymm]
  rw [MeasureTheory.Measure.volume_eq_prod]
  rw [MeasureTheory.setIntegral_prod (fun y => G (Sum.elim y.1 y.2)) hf]

end Work.BoseBoxFock
