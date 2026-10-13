import Mathlib

namespace Work.WilE2.WilE2Aux

theorem sUnion_connectedComponentIn_sdiff_isClosed {α : Type*} [TopologicalSpace α] {S : Set α}
    (hcl : ∀ y : α, IsClosed (connectedComponentIn S y))
    (hfin : (Set.range (connectedComponentIn S)).Finite) (x : α) :
    IsClosed (⋃₀ (Set.range (connectedComponentIn S) \ {connectedComponentIn S x})) ∧
      x ∉ (⋃₀ (Set.range (connectedComponentIn S) \ {connectedComponentIn S x})) := by
  constructor
  · -- The remaining components form a finite family of closed sets.
    refine Set.Finite.isClosed_sUnion (hfin.subset Set.sdiff_subset) ?_
    intro t ht
    obtain ⟨y, rfl⟩ := ht.1
    exact hcl y
  · -- Each point lies in a single connected component, so `x` is excluded.
    intro hx
    obtain ⟨t, ⟨⟨y, rfl⟩, htx⟩, hxt⟩ := Set.mem_sUnion.mp hx
    exact htx (connectedComponentIn_eq hxt)

end Work.WilE2.WilE2Aux
