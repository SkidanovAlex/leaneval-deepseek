import Mathlib

/-!
# A path inside an open preconnected set, as a continuous map on all of `ℝ`

`Work.Noncompact.Routing.exists_arc_in_preconnected`: in a manifold (indeed any charted space over
`ℝ^n`), an open preconnected set `T` is path-connected, and the path can be taken to be a
*continuous map on all of `ℝ`* — which is the form the routing needs, because the connectors of
`Routing.nc_reach_ambient` and the piece engine are functions `ℝ → M`, not `Path`s.

Mathlib's path-connectedness API produces `Path x y` (a structure extending `ContinuousMap` on
`Set.Icc 0 1`); `Path.extend` converts it to `C(ℝ, M)` with `Path.extend_zero`,
`Path.extend_one` and `Path.extend_extends'`, and that is the conversion performed here.  Getting
the path *via* `T`-open is essential: `IsPreconnected` alone is not enough (the comb), while
`IsOpen.isConnected_iff_isPathConnected` is exactly the local path-connectedness of the manifold
turned into path-connectedness of the open set.
-/

namespace Work.Noncompact.Routing

open Set Topology

/-- **An open preconnected set in a charted space over `ℝ^n` carries a path between any two of its
points, as a continuous map on `ℝ`.** -/
theorem exists_arc_in_preconnected {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    {T : Set M} (hTo : IsOpen T) (hTpc : IsPreconnected T)
    {x y : M} (hx : x ∈ T) (hy : y ∈ T) :
    ∃ σ : ℝ → M, Continuous σ ∧ σ 0 = x ∧ σ 1 = y ∧
      ∀ t ∈ Set.Icc (0 : ℝ) 1, σ t ∈ T := by
  haveI : LocallyPathConnectedSpace M :=
    ChartedSpace.locallyPathConnectedSpace (H := EuclideanSpace ℝ (Fin n)) M
  have hc : IsConnected T := ⟨⟨x, hx⟩, hTpc⟩
  have hpc : IsPathConnected T := hTo.isConnected_iff_isPathConnected.mp hc
  obtain ⟨γ, hγ⟩ := hpc.joinedIn x hx y hy
  refine ⟨fun t => γ.extend t, γ.extend.continuous, γ.extend_zero, γ.extend_one, ?_⟩
  intro t ht
  change γ.extend t ∈ T
  rw [γ.extend_extends' ⟨t, ht⟩]
  exact hγ ⟨t, ht⟩

end Work.Noncompact.Routing
