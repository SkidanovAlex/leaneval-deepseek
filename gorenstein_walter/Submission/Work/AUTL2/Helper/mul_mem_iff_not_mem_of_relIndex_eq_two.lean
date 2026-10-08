import Mathlib

namespace Work.AUTL2.Helper

theorem mul_mem_iff_not_mem_of_relIndex_eq_two {G : Type*} [Group G] {H K : Subgroup G}
    (hidx : H.relIndex K = 2) {a : G} (haK : a ∈ K) (haH : a ∉ H) :
    ∀ b ∈ K, b * a ∈ H ↔ b ∉ H := by
  intro b hbK
  have hKidx : (H.subgroupOf K).index = 2 := hidx
  have hmem := Subgroup.mul_mem_iff_of_index_two (H := H.subgroupOf K) hKidx
    (a := ⟨b, hbK⟩) (b := ⟨a, haK⟩)
  simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul] at hmem
  simpa [haH] using hmem

end Work.AUTL2.Helper
