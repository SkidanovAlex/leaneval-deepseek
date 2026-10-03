import Mathlib
import Submission.Lib.Unif2.Work.Spine.Plane.Dyadic
import Submission.Lib.Unif2.Commons.AlgebraicTopology.FundamentalGroup.freeGroup_of_oneDimCWComplex
import Submission.Lib.Unif2.Commons.Topology.CWComplex.exists_cwComplex_univ_of_isClosed_subspace

set_option linter.style.haveILetI false

namespace Work.Spine.Plane

open Set

/-!
# `π₁` of a dyadic polyomino spine is free

The spine `spine U hU n` of level `n` is, by `ySet_eq_segments_spine`, the finite union of the
closed segments `⋃ e ∈ gEdges n (cells U hU n), segment ℝ e.1 e.2` together with the finite set of
grid vertices `gVerts n (cells U hU n)`.  The three incidence properties of this finite family
(`gEdges_endpoints_mem_gVerts`, `gEdges_ne`, `gEdges_disjoint_segments`) make it a one-dimensional
CW complex (`Commons.Topology.Plane.exists_cwComplex_of_finset_segments`), and the spine is closed
in `ℂ` (`isClosed_spine`), so the CW structure transports to the subtype `↥(spine U hU n)`
(`Commons.Topology.CWComplex.exists_cwComplex_univ_of_isClosed_subspace`).

The last ingredient is that a Hausdorff space carrying a CW structure on *all* of itself with no
cells of dimension `≥ 2` has free fundamental group at *every* point — no connectivity hypothesis:
a point lies in a closed cell, hence is joined by a path to a vertex
(`CWGraph.exists_path_to_vertex`), and at a vertex freeness is `CWGraph.Tree.isFreeGroup_vertex`
(`π₁` of a connected one-dimensional CW complex is free; the argument runs inside the connected
component of that vertex).
-/

/-- **`π₁` of a Hausdorff one-dimensional CW complex is free, at any point.** -/
theorem isFreeGroup_fundamentalGroup_of_oneDimCWComplex_point
    {X : Type*} [TopologicalSpace X] [T2Space X]
    (hC : @Topology.CWComplex X _ Set.univ)
    (h2 : ∀ n : ℕ, 2 ≤ n → IsEmpty (@Topology.CWComplex.cell X _ Set.univ hC n))
    (y : X) : IsFreeGroup (FundamentalGroup X y) := by
  letI : Topology.CWComplex (Set.univ : Set X) := hC
  obtain ⟨u, hp⟩ :=
    Commons.AlgebraicTopology.FundamentalGroup.CWGraph.exists_path_to_vertex (X := X) h2 y
  haveI : IsFreeGroup (FundamentalGroup X
      (Commons.AlgebraicTopology.FundamentalGroup.CWGraph.vpt (C := Set.univ) u)) :=
    Commons.AlgebraicTopology.FundamentalGroup.CWGraph.Tree.isFreeGroup_vertex h2 u
  exact IsFreeGroup.ofMulEquiv (FundamentalGroup.fundamentalGroupMulEquivOfPath hp.some).symm

/-- Transport of a CW structure (with vanishing higher cells) along an equality of subspaces. -/
theorem exists_cwComplex_of_eq {X : Type*} [TopologicalSpace X] {S T : Set X} (h : S = T)
    (hC : Topology.CWComplex S)
    (hdim : ∀ m : ℕ, 2 ≤ m → IsEmpty (@Topology.CWComplex.cell X _ S hC m)) :
    ∃ hC' : Topology.CWComplex T,
      ∀ m : ℕ, 2 ≤ m → IsEmpty (@Topology.CWComplex.cell X _ T hC' m) := by
  subst h
  exact ⟨hC, hdim⟩

/-- **The spine of the level-`n` dyadic polyomino is a one-dimensional CW complex** (in the
ambient plane, as a closed subspace of `ℂ`). -/
theorem exists_cwComplex_spine (U : Set ℂ) (hU : IsOpen U) (n : ℕ) :
    ∃ hC : Topology.CWComplex (X := ℂ) (spine U hU n),
      ∀ m : ℕ, 2 ≤ m → IsEmpty (@Topology.CWComplex.cell ℂ _ _ hC m) := by
  obtain ⟨hC, hdim⟩ := Commons.Topology.Plane.exists_cwComplex_of_finset_segments
    (Commons.Topology.Plane.gVerts n (cells U hU n))
    (Commons.Topology.Plane.gEdges n (cells U hU n))
    (fun e he => Commons.Topology.Plane.gEdges_endpoints_mem_gVerts he)
    (fun e he => Commons.Topology.Plane.gEdges_ne he)
    (fun e he e' he' hne => Commons.Topology.Plane.gEdges_disjoint_segments he he' hne)
  exact exists_cwComplex_of_eq (ySet_eq_segments_spine U hU n).symm hC hdim

theorem pi1_spine_isFreeGroup (U : Set ℂ) (hU : IsOpen U) (n : ℕ) (v : ↥(spine U hU n)) :
    IsFreeGroup (FundamentalGroup ↥(spine U hU n) v) := by
  obtain ⟨hC, hdim⟩ := exists_cwComplex_spine U hU n
  obtain ⟨hC', hcell'⟩ := Commons.Topology.CWComplex.exists_cwComplex_univ_of_isClosed_subspace
    (isClosed_spine U hU n) hC
  exact isFreeGroup_fundamentalGroup_of_oneDimCWComplex_point hC'
    (fun m hm => hcell' m (hdim m hm)) v

end Work.Spine.Plane
