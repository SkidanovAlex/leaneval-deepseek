import Mathlib

namespace Work.PlanarSC

/-- If `A ⊆ ℂ` is closed and nonempty and `x ∉ A`, then the closure of the connected component of
`Aᶜ` containing `x` meets `A`.

Otherwise that closure would be a connected subset of `Aᶜ` containing `x`, hence contained in the
component by maximality, so the component would be simultaneously open (a component of the open set
`Aᶜ`) and closed, nonempty and proper in the connected space `ℂ` — impossible. -/
theorem nonempty_inter_closure_componentIn {A : Set ℂ} (hAcl : IsClosed A) (hne : A.Nonempty)
    {x : ℂ} (hx : x ∉ A) : (A ∩ closure (connectedComponentIn Aᶜ x)).Nonempty := by
  by_contra h
  rw [Set.not_nonempty_iff_eq_empty] at h
  have hxU : x ∈ Aᶜ := by simpa using hx
  -- the closure of the component is still disjoint from `A`, hence lies in `Aᶜ`
  have hclU : closure (connectedComponentIn Aᶜ x) ⊆ Aᶜ := by
    rw [Set.subset_compl_iff_disjoint_right, Set.disjoint_iff_inter_eq_empty, Set.inter_comm]
    exact h
  -- maximality: the (connected) closure is contained in the component
  have hsub : closure (connectedComponentIn Aᶜ x) ⊆ connectedComponentIn Aᶜ x :=
    isPreconnected_connectedComponentIn.closure.subset_connectedComponentIn
      (subset_closure (mem_connectedComponentIn hxU)) hclU
  have hCclosed : IsClosed (connectedComponentIn Aᶜ x) := isClosed_of_closure_subset hsub
  have hCopen : IsOpen (connectedComponentIn Aᶜ x) := hAcl.isOpen_compl.connectedComponentIn
  have hCne : (connectedComponentIn Aᶜ x).Nonempty := ⟨x, mem_connectedComponentIn hxU⟩
  -- a nonempty clopen subset of the connected space `ℂ` is everything, contradiction
  have hcover : (Set.univ : Set ℂ) ⊆
      connectedComponentIn Aᶜ x ∪ (connectedComponentIn Aᶜ x)ᶜ := by
    intro y _
    by_cases hy : y ∈ connectedComponentIn Aᶜ x
    · exact Or.inl hy
    · exact Or.inr hy
  rcases isPreconnected_univ.subset_or_subset hCopen hCclosed.isOpen_compl
      disjoint_compl_right hcover with h1 | h2
  · obtain ⟨a, ha⟩ := hne
    exact (connectedComponentIn_subset Aᶜ x (h1 (Set.mem_univ a))) ha
  · have hCempty : connectedComponentIn Aᶜ x = ∅ :=
      Set.Subset.antisymm (fun y hy => h2 (Set.mem_univ y) hy) (Set.empty_subset _)
    exact hCne.ne_empty hCempty

end Work.PlanarSC
