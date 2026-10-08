import Mathlib

namespace Work.CORE4

theorem mul_mem_of_relIndex_eq_two {G : Type} [Group G] {H K : Subgroup G} (hKH : K ≤ H)
    (hidx : K.relIndex H = 2) {x y : G} (hx : x ∈ H) (hy : y ∈ H) (hxK : x ∉ K) (hyK : y ∉ K) :
    x * y ∈ K := by
  have hidx' : (K.subgroupOf H).index = 2 := hidx
  have hmem : (⟨x, hx⟩ : H) * ⟨y, hy⟩ ∈ K.subgroupOf H := by
    rw [Subgroup.mul_mem_iff_of_index_two hidx']
    simp [Subgroup.mem_subgroupOf, hxK, hyK]
  simpa using (Subgroup.mem_subgroupOf.mp hmem)

end Work.CORE4
