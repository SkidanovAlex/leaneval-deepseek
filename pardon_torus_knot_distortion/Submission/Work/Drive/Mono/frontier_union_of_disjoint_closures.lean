import Mathlib

namespace Work.Drive.Mono

open Set

/-- If the closures of `A` and `B` are disjoint, then the frontier of the union
is the union of the frontiers.  The forward inclusion needs no hypothesis; the
reverse one uses that a point of `frontier A` (say) cannot be an interior point
of `A ∪ B`, because it lies in `closure A` and hence outside `closure B`. -/
theorem frontier_union_of_disjoint_closures {α : Type*} [TopologicalSpace α] {A B : Set α}
    (h : Disjoint (closure A) (closure B)) :
    frontier (A ∪ B) = frontier A ∪ frontier B := by
  apply Subset.antisymm
  · -- `frontier (A ∪ B) ⊆ frontier A ∪ frontier B`
    intro x hx
    simp only [frontier, mem_sdiff, closure_union, mem_union] at hx ⊢
    rcases hx with ⟨hxc | hxc, hxi⟩
    · exact Or.inl ⟨hxc, fun hA => hxi (interior_mono subset_union_left hA)⟩
    · exact Or.inr ⟨hxc, fun hB => hxi (interior_mono subset_union_right hB)⟩
  · -- `frontier A ∪ frontier B ⊆ frontier (A ∪ B)`
    intro x hx
    simp only [frontier, mem_sdiff, closure_union, mem_union] at hx ⊢
    refine ⟨?_, ?_⟩
    · rcases hx with ⟨hxc, _⟩ | ⟨hxc, _⟩
      · exact Or.inl hxc
      · exact Or.inr hxc
    · intro hxint
      have hxint' : A ∪ B ∈ nhds x := mem_interior_iff_mem_nhds.mp hxint
      rcases hx with ⟨hxc, hxi⟩ | ⟨hxc, hxi⟩
      · -- `x ∈ frontier A`: then `x ∉ closure B`, and `(A ∪ B) ∩ (closure B)ᶜ ⊆ A`
        have hnb : x ∉ closure B := (disjoint_left.mp h) hxc
        have hcompl : (closure B)ᶜ ∈ nhds x := isClosed_closure.isOpen_compl.mem_nhds hnb
        have hsub : (A ∪ B) ∩ (closure B)ᶜ ⊆ A := by
          rintro y ⟨hyAB, hyc⟩
          rcases hyAB with hyA | hyB
          · exact hyA
          · exact absurd (subset_closure hyB) hyc
        exact hxi (mem_interior_iff_mem_nhds.mpr
          (Filter.mem_of_superset (Filter.inter_mem hxint' hcompl) hsub))
      · -- `x ∈ frontier B`: symmetric
        have hna : x ∉ closure A := (disjoint_right.mp h) hxc
        have hcompl : (closure A)ᶜ ∈ nhds x := isClosed_closure.isOpen_compl.mem_nhds hna
        have hsub : (A ∪ B) ∩ (closure A)ᶜ ⊆ B := by
          rintro y ⟨hyAB, hyc⟩
          rcases hyAB with hyA | hyB
          · exact absurd (subset_closure hyA) hyc
          · exact hyB
        exact hxi (mem_interior_iff_mem_nhds.mpr
          (Filter.mem_of_superset (Filter.inter_mem hxint' hcompl) hsub))

end Work.Drive.Mono
