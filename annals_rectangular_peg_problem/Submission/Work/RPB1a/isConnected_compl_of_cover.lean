import Mathlib

namespace Work.RPB1a

theorem isConnected_compl_of_cover {X : Type*} [TopologicalSpace X] {A B C : Set X}
    (hcover : A ∪ B = Cᶜ) (hdisj : Disjoint A B) (hB : IsConnected B)
    (hcl : closure B = B ∪ C) : C ⊆ closure ((A ∪ C)ᶜ) ∧ IsConnected (Aᶜ) := by
  -- B lies in the complement of C, and C lies in the closure of B.
  have hBsub : B ⊆ Cᶜ := by
    rw [← hcover]; exact Set.subset_union_right
  have hCsub : C ⊆ closure B := by
    rw [hcl]; exact Set.subset_union_right
  -- A is exactly the complement of B ∪ C.
  have hAc : Aᶜ = B ∪ C := by
    apply Set.Subset.antisymm
    · intro x hx
      rw [Set.mem_union]
      by_cases hxB : x ∈ B
      · exact Or.inl hxB
      · right
        by_contra hxC
        have : x ∈ A ∪ B := by rw [hcover]; exact hxC
        rcases this with h | h
        · exact hx h
        · exact hxB h
    · intro x hx
      rcases hx with hxB | hxC
      · intro hxA
        exact (Set.disjoint_left.mp hdisj hxA) hxB
      · intro hxA
        have hmem : x ∈ Cᶜ := by rw [← hcover]; exact Set.mem_union_left B hxA
        exact hmem hxC
  -- Consequently (A ∪ C)ᶜ = B.
  have hAcC : (A ∪ C)ᶜ = B := by
    rw [Set.compl_union, hAc, Set.union_inter_distrib_right, Set.inter_compl_self,
      Set.union_empty]
    exact Set.inter_eq_left.mpr hBsub
  -- And Aᶜ = B ∪ C = closure B, which is connected because B is.
  have hpart2 : IsConnected (Aᶜ) := by
    rw [hAc, ← hcl]
    exact hB.closure
  exact ⟨by rw [hAcC]; exact hCsub, hpart2⟩

end Work.RPB1a
