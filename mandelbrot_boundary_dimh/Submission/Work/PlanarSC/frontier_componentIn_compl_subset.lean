import Mathlib

namespace Work.PlanarSC

/-- The frontier of a connected component of the complement of a closed set is contained in that
closed set.  (`ℂ` is locally connected, so a component of the open set `Aᶜ` is open; if a point `y`
of the frontier of the component lay in `Aᶜ`, then the component together with `y` would be a
strictly larger preconnected subset of `Aᶜ`.) -/
theorem frontier_componentIn_compl_subset {A : Set ℂ} (hAcl : IsClosed A) (x : ℂ) :
    frontier (connectedComponentIn Aᶜ x) ⊆ A := by
  by_cases hx : x ∈ Aᶜ
  · intro y hy
    by_contra hyA
    have hyAc : y ∈ Aᶜ := hyA
    have hCopen : IsOpen (connectedComponentIn Aᶜ x) := hAcl.isOpen_compl.connectedComponentIn
    have hxC : x ∈ connectedComponentIn Aᶜ x := mem_connectedComponentIn hx
    have hynotC : y ∉ connectedComponentIn Aᶜ x := by
      intro hyC
      have hmem : y ∈ connectedComponentIn Aᶜ x ∩ frontier (connectedComponentIn Aᶜ x) :=
        ⟨hyC, hy⟩
      rw [hCopen.inter_frontier_eq] at hmem
      exact hmem
    have hycl : y ∈ closure (connectedComponentIn Aᶜ x) := frontier_subset_closure hy
    have hpre : IsPreconnected (connectedComponentIn Aᶜ x ∪ {y}) :=
      (isPreconnected_connectedComponentIn (F := Aᶜ) (x := x)).subset_closure
        (Set.subset_union_left : connectedComponentIn Aᶜ x ⊆ connectedComponentIn Aᶜ x ∪ {y})
        ((Set.union_subset subset_closure (Set.singleton_subset_iff.mpr hycl)) :
          connectedComponentIn Aᶜ x ∪ {y} ⊆ closure (connectedComponentIn Aᶜ x))
    have hsub : connectedComponentIn Aᶜ x ∪ {y} ⊆ Aᶜ :=
      Set.union_subset (connectedComponentIn_subset Aᶜ x) (Set.singleton_subset_iff.mpr hyAc)
    have hmem' : y ∈ connectedComponentIn Aᶜ x :=
      hpre.subset_connectedComponentIn (Set.mem_union_left {y} hxC) hsub
        (Set.mem_union_right _ rfl)
    exact hynotC hmem'
  · intro y hy
    rw [connectedComponentIn_eq_empty hx] at hy
    simp at hy

end Work.PlanarSC
