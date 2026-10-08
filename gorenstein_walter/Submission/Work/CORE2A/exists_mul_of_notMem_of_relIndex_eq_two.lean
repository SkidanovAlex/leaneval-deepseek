import Mathlib

namespace Work.CORE2A

/-- If `S0` is a subgroup of `S` of index two and `s, y ∈ S` both lie outside `S0`,
then they lie in the same coset: `y = s * c` for some `c ∈ S0`. -/
theorem exists_mul_of_notMem_of_relIndex_eq_two {G : Type} [Group G] {S S0 : Subgroup G}
    (hidx : S0.relIndex S = 2) {s y : G} (hs : s ∈ S) (hs0 : s ∉ S0) (hy : y ∈ S)
    (hy0 : y ∉ S0) : ∃ c ∈ S0, y = s * c := by
  -- Work inside `S`, where `S0` becomes the subgroup `S0.subgroupOf S` of index two.
  have hindex : (S0.subgroupOf S).index = 2 := hidx
  let a : S := ⟨s, hs⟩
  let b : S := ⟨s⁻¹ * y, mul_mem (inv_mem hs) hy⟩
  -- `a * b` is the element `y` of `S`.
  have hab : (a * b : S) = ⟨y, hy⟩ := by
    ext
    simp [a, b, mul_inv_cancel_left]
  have ha_not : a ∉ S0.subgroupOf S := by
    simp only [Subgroup.mem_subgroupOf]
    simpa [a] using hs0
  have hab_not : a * b ∉ S0.subgroupOf S := by
    rw [hab]
    simp only [Subgroup.mem_subgroupOf]
    simpa using hy0
  -- Index two: membership of a product is governed by membership of its factors.
  have hiff := Subgroup.mul_mem_iff_of_index_two (H := S0.subgroupOf S) hindex (a := a) (b := b)
  have hb_mem : b ∈ S0.subgroupOf S := by
    by_contra hbn
    exact hab_not (hiff.mpr ⟨fun ha => absurd ha ha_not, fun hb => absurd hb hbn⟩)
  refine ⟨s⁻¹ * y, ?_, ?_⟩
  · simpa [b, Subgroup.mem_subgroupOf] using hb_mem
  · rw [mul_inv_cancel_left]

end Work.CORE2A
