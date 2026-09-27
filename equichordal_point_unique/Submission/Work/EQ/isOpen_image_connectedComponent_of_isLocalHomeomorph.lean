import Mathlib

namespace Work.EQ

/-- The image of a connected component under a local homeomorphism to `ℂ` is open.

This holds because `ℂ` is locally connected: around each point `z` of the component,
`φ` restricts to a homeomorphism `e` onto an open subset `e.target` of `ℂ`.  The
connected component `D` of `φ z` inside `e.target` is open in `ℂ`, and pulling `D`
back along `e.symm` gives a connected set containing `z`, hence contained in
`connectedComponent z = connectedComponent x`; consequently `D ⊆ φ '' connectedComponent x`
and `D` is a neighbourhood of `φ z`. -/
theorem isOpen_image_connectedComponent_of_isLocalHomeomorph
    {X : Type*} [TopologicalSpace X] {φ : X → ℂ} (hφ : IsLocalHomeomorph φ) (x : X) :
    IsOpen (φ '' connectedComponent x) := by
  rw [isOpen_iff_mem_nhds]
  rintro y hy
  obtain ⟨z, hz, rfl⟩ := hy
  obtain ⟨e, hze, hφe⟩ := hφ z
  rw [hφe]
  have hDopen : IsOpen (connectedComponentIn e.target (⇑e z)) :=
    e.open_target.connectedComponentIn (x := ⇑e z)
  have hDmem : ⇑e z ∈ connectedComponentIn e.target (⇑e z) :=
    mem_connectedComponentIn (e.map_source hze)
  have hDsub : connectedComponentIn e.target (⇑e z) ⊆ ⇑e '' connectedComponent x := by
    have hDsubT : connectedComponentIn e.target (⇑e z) ⊆ e.target :=
      connectedComponentIn_subset _ _
    have hpreconn : IsPreconnected (⇑e.symm '' connectedComponentIn e.target (⇑e z)) :=
      (isPreconnected_connectedComponentIn).image _ (e.continuousOn_symm.mono hDsubT)
    have hzmem : z ∈ ⇑e.symm '' connectedComponentIn e.target (⇑e z) :=
      ⟨⇑e z, hDmem, e.left_inv hze⟩
    have hsub : ⇑e.symm '' connectedComponentIn e.target (⇑e z) ⊆ connectedComponent x := by
      rw [← (connectedComponent_eq hz).symm]
      exact hpreconn.subset_connectedComponent hzmem
    intro d hd
    exact ⟨e.symm d, hsub ⟨d, hd, rfl⟩, e.right_inv (hDsubT hd)⟩
  exact Filter.mem_of_superset (hDopen.mem_nhds hDmem) hDsub

end Work.EQ
