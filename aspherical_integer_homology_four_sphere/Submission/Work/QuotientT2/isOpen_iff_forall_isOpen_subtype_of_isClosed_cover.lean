import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.QuotientT2

theorem isOpen_iff_forall_isOpen_subtype_of_isClosed_cover {X : Type*} [TopologicalSpace X]
    {ι : Type*} [Finite ι] {C : ι → Set X} (hC : ∀ i, IsClosed (C i))
    (hcov : ⋃ i, C i = Set.univ) {s : Set X} :
    IsOpen s ↔ ∀ i, IsOpen ((Subtype.val : C i → X) ⁻¹' s) := by
  constructor
  · -- Forward implication: preimage of an open set under the (continuous) inclusion.
    intro hs i
    exact hs.preimage continuous_subtype_val
  · -- Backward implication: use that sᶜ is a finite union of closed pieces.
    intro hs
    rw [← isClosed_compl_iff]
    have hcover : sᶜ = ⋃ i, (C i ∩ sᶜ) := by
      rw [← Set.iUnion_inter, hcov, Set.univ_inter]
    rw [hcover]
    refine isClosed_iUnion_of_finite (fun i => ?_)
    have himg : (Subtype.val : C i → X) '' ((Subtype.val : C i → X) ⁻¹' sᶜ) = C i ∩ sᶜ :=
      Subtype.image_preimage_coe (C i) sᶜ
    have hpre : IsClosed ((Subtype.val : C i → X) ⁻¹' sᶜ) := by
      rw [Set.preimage_compl]
      exact (hs i).isClosed_compl
    rw [← himg]
    exact (hC i).isClosedEmbedding_subtypeVal.isClosed_iff_image_isClosed.mp hpre

end Work.QuotientT2
