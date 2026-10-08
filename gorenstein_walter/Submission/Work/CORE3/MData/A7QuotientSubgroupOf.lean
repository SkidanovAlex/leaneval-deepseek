import Mathlib
import Submission.Work.CORE3.Defs

namespace Work.CORE3.MData

/-- An isomorphism of groups induces an isomorphism of their central quotients. -/
theorem quotientCenterCongr {G H : Type*} [Group G] [Group H] (e : G ≃* H) :
    Nonempty (G ⧸ Subgroup.center G ≃* H ⧸ Subgroup.center H) := by
  have hf : Function.Surjective ((QuotientGroup.mk' (Subgroup.center H)).comp (e : G →* H)) :=
    (QuotientGroup.mk'_surjective (Subgroup.center H)).comp e.surjective
  have hk : ((QuotientGroup.mk' (Subgroup.center H)).comp (e : G →* H)).ker = Subgroup.center G := by
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
    rw [← Subgroup.map_center_eq e, Subgroup.comap_map_eq_self_of_injective e.injective]
  exact ⟨QuotientGroup.liftEquiv (Subgroup.center G) hf hk.symm⟩

theorem A7QuotientSubgroupOf {G : Type} [Group G] {E N : Subgroup G} (hEN : E ≤ N)
    (h : Nonempty ((↥E ⧸ Subgroup.center ↥E) ≃* alternatingGroup (Fin 7))) :
    Nonempty ((↥(E.subgroupOf N) ⧸ Subgroup.center ↥(E.subgroupOf N))
      ≃* alternatingGroup (Fin 7)) := by
  obtain ⟨e⟩ := h
  obtain ⟨e'⟩ := quotientCenterCongr (Subgroup.subgroupOfEquivOfLe hEN)
  exact ⟨e'.trans e⟩

end Work.CORE3.MData
