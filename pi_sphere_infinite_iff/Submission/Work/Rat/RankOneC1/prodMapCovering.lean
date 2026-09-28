import Mathlib

namespace Work.Rat.RankOneC1

open Set

/-- If a point `x` is evenly covered by `p : E → X` with fiber `I`, then the point `(y, x)` is
evenly covered by the product map `Y × E → Y × X`, `(y, e) ↦ (y, p e)`, still with fiber `I`. -/
theorem isEvenlyCovered_prodMap_id {E X Y : Type} [TopologicalSpace E] [TopologicalSpace X]
    [TopologicalSpace Y] {p : E → X} {I : Type} [TopologicalSpace I] {x : X}
    (h : IsEvenlyCovered p x I) (y : Y) :
    IsEvenlyCovered (fun z : Y × E => (z.1, p z.2)) (y, x) I := by
  obtain ⟨discI, U, hxU, hU, hfU, H, hH⟩ := h
  have hset : (fun z : Y × E => (z.1, p z.2)) ⁻¹' (Set.univ ×ˢ U) = Set.univ ×ˢ (p ⁻¹' U) := by
    ext z
    simp
  let F : ((fun z : Y × E => (z.1, p z.2)) ⁻¹' (Set.univ ×ˢ U)) ≃ₜ (Set.univ ×ˢ U) × I :=
      (Homeomorph.setCongr hset).trans <|
      (Homeomorph.Set.prod (Set.univ : Set Y) (p ⁻¹' U)).trans <|
      ((Homeomorph.Set.univ Y).prodCongr (Homeomorph.refl (p ⁻¹' U))).trans <|
      ((Homeomorph.refl Y).prodCongr H).trans <|
      (Homeomorph.prodAssoc Y U I).symm |>.trans <|
      (((Homeomorph.Set.univ Y).symm.prodCongr (Homeomorph.refl U)).trans
        ((Homeomorph.Set.prod (Set.univ : Set Y) U).symm)).prodCongr (Homeomorph.refl I)
  refine ⟨discI, Set.univ ×ˢ U, ⟨trivial, hxU⟩, isOpen_univ.prod hU, ?_, F, ?_⟩
  · rw [hset]
    exact isOpen_univ.prod hfU
  · intro z
    simp only [F, Homeomorph.trans_apply]
    simp only [Homeomorph.prodCongr, Homeomorph.homeomorph_mk_coe, Equiv.prodCongr_apply, Prod.map,
      Homeomorph.prodAssoc, Equiv.prodAssoc_symm_apply, Homeomorph.Set.univ, Equiv.Set.univ,
      Homeomorph.symm, Equiv.setCongr_apply, Homeomorph.setCongr]
    simp
    constructor
    · rfl
    · exact hH _

theorem prodMapCovering {E X Y : Type} [TopologicalSpace E] [TopologicalSpace X]
    [TopologicalSpace Y] {p : E → X} (hp : IsCoveringMap p) :
    IsCoveringMap (fun z : Y × E => (z.1, p z.2)) := by
  intro b
  exact (isEvenlyCovered_prodMap_id (hp b.2) b.1).to_isEvenlyCovered_preimage

end Work.Rat.RankOneC1
