import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Hering.Step5

/-- If `K` (a subgroup of `M`) meets the preimage of `C` in `M` trivially, then the image
of `K` in `G` meets `C` trivially. -/
theorem map_inf_eq_bot {G : Type*} [Group G] {H C : Subgroup G} {M : Subgroup H}
    (hCM : C ≤ H) (hCM' : C.subgroupOf H ≤ M) {K : Subgroup M}
    (hK : K ⊓ (C.subgroupOf H).subgroupOf M = ⊥) :
    K.map (H.subtype.comp M.subtype) ⊓ C = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  obtain ⟨hxK, hxC⟩ := Subgroup.mem_inf.mp hx
  obtain ⟨k, hkK, hkx⟩ := Subgroup.mem_map.mp hxK
  have hk : k ∈ (C.subgroupOf H).subgroupOf M := by
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    show (H.subtype.comp M.subtype) k ∈ C
    exact hkx ▸ hxC
  have hmem : k ∈ K ⊓ (C.subgroupOf H).subgroupOf M := ⟨hkK, hk⟩
  rw [hK] at hmem
  rw [Subgroup.mem_bot] at hmem
  rw [← hkx, hmem]
  simp

end Work.Hering.Step5
