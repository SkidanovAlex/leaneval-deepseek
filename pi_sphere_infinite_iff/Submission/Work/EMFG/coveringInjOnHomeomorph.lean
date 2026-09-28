import Mathlib

namespace Work.EMFG

open Topology Set Function

/-- If `p : E → X` is a covering map and `A ⊆ E` is an open set on which `p` is injective,
then `p` restricts to a homeomorphism between `A` and its image `p '' A`. -/
theorem coveringInjOnHomeomorph {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    (p : C(E, X)) (hp : IsCoveringMap p) {A : Set E} (hAo : IsOpen A) (hA : Set.InjOn p A) :
    ∃ φ : ↥(p '' A) ≃ₜ ↥A, ∀ y : ↥(p '' A), p (φ y) = (y : X) := by
  -- The restriction of `p` to `A` is continuous, injective, and open,
  -- hence an open embedding.
  have hcont : Continuous (A.domRestrict (⇑p)) := p.continuous.comp continuous_subtype_val
  have hopen : IsOpenMap (A.domRestrict (⇑p)) :=
    (show (A.domRestrict (⇑p)) = ⇑p ∘ Subtype.val from rfl) ▸
      hp.isOpenMap.comp hAo.isOpenMap_subtype_val
  have hinj : Injective (A.domRestrict (⇑p)) := Set.injOn_iff_injective.mp hA
  have hemb : IsOpenEmbedding (A.domRestrict (⇑p)) :=
    isOpenEmbedding_iff_continuous_injective_isOpenMap.mpr ⟨hcont, hinj, hopen⟩
  -- The induced homeomorphism `A ≃ₜ p '' A`, whose forward map is `p`.
  let e : ↥A ≃ₜ ↥(p '' A) :=
    hemb.toIsEmbedding.toHomeomorph.trans
      (Homeomorph.setCongr (Set.range_domRestrict (⇑p) A))
  have key : ∀ a : ↥A, ↑(e a) = p ↑a := by
    intro a
    change ↑((hemb.toIsEmbedding.toHomeomorph.trans
      (Homeomorph.setCongr (Set.range_domRestrict (⇑p) A))) a) = p ↑a
    rw [Homeomorph.trans_apply]
    exact IsEmbedding.toHomeomorph_apply_coe hemb.toIsEmbedding a
  refine ⟨e.symm, fun y => ?_⟩
  calc p ↑(e.symm y) = ↑(e (e.symm y)) := (key (e.symm y)).symm
    _ = ↑y := congrArg Subtype.val (Homeomorph.apply_symm_apply e y)

end Work.EMFG
