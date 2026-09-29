import Mathlib

namespace Work.TMComp.RealCartan

theorem rcFrontier_connectedComponentIn_subset {F : Set ℂ} (hF : IsOpen F) (x : ℂ) :
    frontier (connectedComponentIn F x) ⊆ frontier F := by
  by_cases hx : x ∈ F
  · intro y hy
    rw [IsOpen.frontier_eq hF]
    refine ⟨closure_mono (connectedComponentIn_subset F x) (frontier_subset_closure hy), ?_⟩
    intro hyF
    have hCopen : IsOpen (connectedComponentIn F x) := hF.connectedComponentIn
    have hnotC : y ∉ connectedComponentIn F x := by
      intro hyC
      have hmem : y ∈ connectedComponentIn F x ∩ frontier (connectedComponentIn F x) :=
        ⟨hyC, hy⟩
      rw [IsOpen.inter_frontier_eq hCopen] at hmem
      exact hmem
    apply hnotC
    have hclC : y ∈ closure (connectedComponentIn F x) := frontier_subset_closure hy
    have hpre : IsPreconnected (connectedComponentIn F x ∪ {y}) :=
      isPreconnected_connectedComponentIn.subset_closure Set.subset_union_left (by
        intro z hz
        rcases hz with hz | hz
        · exact subset_closure hz
        · rw [Set.mem_singleton_iff] at hz; rw [hz]; exact hclC)
    have hsubF : connectedComponentIn F x ∪ {y} ⊆ F := by
      intro z hz
      rcases hz with hz | hz
      · exact connectedComponentIn_subset F x hz
      · rw [Set.mem_singleton_iff] at hz; rw [hz]; exact hyF
    exact hpre.subset_connectedComponentIn (Or.inl (mem_connectedComponentIn hx)) hsubF (Or.inr rfl)
  · rw [connectedComponentIn_eq_empty hx, frontier_empty]
    exact Set.empty_subset _

end Work.TMComp.RealCartan
