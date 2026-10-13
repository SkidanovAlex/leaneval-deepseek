import Mathlib

namespace Work.WilE7

theorem clopenPartition {α : Type*} [TopologicalSpace α] {ι : Type*} [Finite ι]
    (A : ι → Set α) (hcover : ∀ x : α, ∃ i, x ∈ A i)
    (hdisj : ∀ i i', i ≠ i' → Disjoint (A i) (A i')) (hcl : ∀ i, IsClosed (A i)) (i : ι) :
    IsClopen (A i) := by
  refine ⟨hcl i, ?_⟩
  -- `A i` is the complement of the finite (hence closed) union of the other parts.
  have hUn : A i = (⋃ j ∈ ({i}ᶜ : Set ι), A j)ᶜ := by
    ext x
    constructor
    · intro hx
      simp only [Set.mem_compl_iff, Set.mem_iUnion, not_exists]
      intro j hj hxj
      exact (Set.disjoint_left.mp (hdisj i j (fun h => hj h.symm))) hx hxj
    · intro hx
      simp only [Set.mem_compl_iff, Set.mem_iUnion, not_exists] at hx
      obtain ⟨j, hj⟩ := hcover x
      by_cases h : j = i
      · rw [h] at hj; exact hj
      · exact absurd hj (hx j h)
  rw [hUn]
  exact isOpen_compl_iff.mpr (Set.Finite.isClosed_biUnion (Set.toFinite _) (fun j _ => hcl j))

end Work.WilE7
