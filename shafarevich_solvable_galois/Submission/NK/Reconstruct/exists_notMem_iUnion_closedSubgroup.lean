import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.Reconstruct

/-- If a finite family of closed subgroups of a compact Hausdorff topological group are all
non-open, they cannot cover the group: a non-open subgroup of a topological group has empty
interior, hence is nowhere dense, and a finite union of closed nowhere dense sets cannot cover a
Baire space. -/
theorem exists_notMem_iUnion_closedSubgroup {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G] {ι : Type*} [Finite ι]
    (H : ι → Subgroup G) (hcl : ∀ i, IsClosed (H i : Set G))
    (h : ∀ i, ¬ IsOpen (H i : Set G)) :
    ∃ g : G, ∀ i, g ∉ H i := by
  by_contra hcon
  simp only [not_exists, not_forall, not_not] at hcon
  have hcover : ⋃ i, (H i : Set G) = Set.univ := by
    ext g
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    exact hcon g
  obtain ⟨i, x, hx⟩ := nonempty_interior_of_iUnion_of_closed (fun i => hcl i) hcover
  exact h i (Subgroup.isOpen_of_mem_nhds (H i)
    (Filter.mem_of_superset (isOpen_interior.mem_nhds hx) interior_subset))

end NK.Reconstruct
