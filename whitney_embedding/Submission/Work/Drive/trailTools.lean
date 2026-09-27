import Mathlib

/-!
# Tools for the trail-tube construction of `Work.Drive.rayPieceFamily`

`Work.Drive.exists_tube_nhd`: a compact set inside an open set has an open neighbourhood whose
closure is still inside the open set (in a locally compact space).  This is the "thin tube" tool of
`NOTES_ray_by_truncation_DESIGN_TRAIL.md` §3: applied with `U := W ∩ (⋃ pieces)ᶜ ∩ (K m)ᶜ` it
produces the thin tube along the escaping path `ρ` which avoids everything prescribed.

`Work.Drive.exists_isPreconnected_tube` is the same statement with `V` additionally preconnected
(take the component of a prescribed point) — the form used for the region of a step.
-/

open Set Topology

namespace Work.Drive

variable {M : Type*} [TopologicalSpace M] [T2Space M]

/-- **The thin neighbourhood of a compact set inside an open set** (locally compact `M`). -/
theorem exists_tube_nhd [LocallyCompactSpace M] {T U : Set M} (hT : IsCompact T) (hUo : IsOpen U)
    (hTU : T ⊆ U) : ∃ V : Set M, IsOpen V ∧ T ⊆ V ∧ closure V ⊆ U := by
  classical
  choose K hKc hKint hKU using fun x : ↥T => exists_compact_subset hUo (hTU x.2)
  have hcov : T ⊆ ⋃ x : ↥T, interior (K x) := by
    intro y hy
    exact Set.mem_iUnion.mpr ⟨⟨y, hy⟩, hKint ⟨y, hy⟩⟩
  obtain ⟨t, ht⟩ := hT.elim_finite_subcover (fun x : ↥T => interior (K x))
    (fun x => isOpen_interior) hcov
  refine ⟨⋃ x ∈ t, interior (K x), isOpen_biUnion fun x _ => isOpen_interior, ht, ?_⟩
  refine Subset.trans (closure_minimal (iUnion₂_subset fun x hx =>
    fun y hy => Set.mem_iUnion₂.mpr ⟨x, hx, (interior_subset : interior (K x) ⊆ K x) hy⟩) ?_) ?_
  · exact (Set.Finite.isCompact_biUnion t.finite_toSet fun x _ => hKc x).isClosed
  · exact iUnion₂_subset fun x _ => hKU x

/-- **The thin preconnected neighbourhood**: the component of a point of a *preconnected* trial set
`T` in the thin neighbourhood; it contains all of `T`. -/
theorem exists_isPreconnected_tube [LocallyCompactSpace M] [LocallyConnectedSpace M]
    {T U : Set M} (hT : IsCompact T) (hTpc : IsPreconnected T)
    (hUo : IsOpen U) (hTU : T ⊆ U) {x : M} (hx : x ∈ T) :
    ∃ V : Set M, IsOpen V ∧ IsPreconnected V ∧ x ∈ V ∧ T ⊆ V ∧ closure V ⊆ U := by
  obtain ⟨V₀, hV₀o, hTV₀, hV₀U⟩ := exists_tube_nhd hT hUo hTU
  refine ⟨connectedComponentIn V₀ x, hV₀o.connectedComponentIn, isPreconnected_connectedComponentIn,
    mem_connectedComponentIn (hTV₀ hx), ?_, ?_⟩
  · exact hTpc.subset_connectedComponentIn hx fun y hy => hTV₀ hy
  · exact (closure_mono (connectedComponentIn_subset V₀ x)).trans hV₀U

/-- Every compact subset of `M` lies in a member of any compact exhaustion of `M`. -/
theorem IsCompact.exists_subset_exhaustion {K : CompactExhaustion M} {T : Set M}
    (hT : IsCompact T) : ∃ m : ℕ, T ⊆ K m := K.exists_superset_of_isCompact hT

end Work.Drive
