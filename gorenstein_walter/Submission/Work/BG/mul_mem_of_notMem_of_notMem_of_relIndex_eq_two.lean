import Mathlib

namespace Work.BG

/-- If `H.relIndex K = 2`, i.e. the index of `H ⊓ K` in `K` is two, then the product of two
elements of `K` lying outside `H` again lies in `H`. -/
theorem mul_mem_of_notMem_of_notMem_of_relIndex_eq_two {G : Type*} [Group G]
    {H K : Subgroup G} {x y : G} (hidx : H.relIndex K = 2)
    (hx : x ∈ K) (hx0 : x ∉ H) (hy : y ∈ K) (hy0 : y ∉ H) : x * y ∈ H := by
  -- `H.relIndex K` is by definition the index of `H.subgroupOf K` inside `K`.
  have h2 : (H.subgroupOf K).index = 2 := by
    rw [Subgroup.relIndex] at hidx
    exact hidx
  -- Apply the index-two criterion inside the group `K` to `⟨x, hx⟩` and `⟨y, hy⟩`.
  have key := Subgroup.mul_mem_iff_of_index_two (H := H.subgroupOf K) h2
    (a := (⟨x, hx⟩ : K)) (b := (⟨y, hy⟩ : K))
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf] at key
  simp only [Subgroup.coe_mul] at key
  rw [key]
  simp [hx0, hy0]

end Work.BG
