import Mathlib

/-!
# A second-countable, locally connected space has countably many connected components

If `M` is second countable and locally connected, then every connected component of `M` is
nonempty and open (`isOpen_connectedComponent`, which needs local connectedness).  A second
countable space is separable (`SecondCountableTopology.to_separableSpace`), so there is a
countable dense set `D ⊆ M`.  Every nonempty open set meets `D`, so every connected component
contains a point of `D`, i.e. the map

`D → ConnectedComponents M`, `y ↦ ConnectedComponents.mk y`

is surjective.  A surjective image of a countable type is countable, hence
`ConnectedComponents M` is countable.

This is the countability input used when assembling a global embedding of a compact manifold out
of embeddings of its (finitely many, in the compact case) connected components.
-/

namespace Work.Embedding

/-- A second countable, locally connected topological space has countably many connected
components. -/
theorem countable_connectedComponents {M : Type*} [TopologicalSpace M] [SecondCountableTopology M]
    [LocallyConnectedSpace M] : Countable (ConnectedComponents M) := by
  -- A second countable space is separable: pick a countable dense set `D`.
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense M
  -- Every connected component is nonempty and open, hence meets `D`.
  have hsurj :
      Function.Surjective fun y : D => (ConnectedComponents.mk y : ConnectedComponents M) := by
    intro C
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe C
    obtain ⟨y, hyD, hyx⟩ :=
      hDd.exists_mem_open isOpen_connectedComponent ⟨x, mem_connectedComponent⟩
    exact ⟨⟨y, hyD⟩, ConnectedComponents.coe_eq_coe'.mpr hyx⟩
  -- A surjective image of a countable type is countable.
  exact @Function.Surjective.countable D (ConnectedComponents M) hDc.to_subtype _ hsurj

end Work.Embedding
