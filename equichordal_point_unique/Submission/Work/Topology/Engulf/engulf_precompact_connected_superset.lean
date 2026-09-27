import Mathlib
import Submission.Work.SimplyConnected.ABS.engulfs_filling

/-!
# The existence half of the filling statement

`Work.Topology.Engulf.exists_filled_isCompact_closure` asks for an open connected relatively compact
`Ω ⊇ K` whose complement has **no** relatively compact component.  The present file proves the
existence half: every compact subset of a connected, locally compact, locally connected, locally path
connected `T2` space lies in an open connected relatively compact set.  What remains of the filling
statement is then purely the *filling* itself (adding the relatively compact complementary
components, and showing that the result has no relatively compact complementary component) — the
input `Work.Topology.Engulf.simplyConnectedSpace_of_no_relativelyCompact_component` consumes.

Reduction used by the engulfing (`NOTES_engulf_twofold_cover_route.md` §7):

  `exists_filled_isCompact_closure` = `exists_isOpen_isConnected_isCompact_closure_superset`
                                    + (filling: no relatively compact complementary component).
-/

namespace Work.Topology.Engulf

open Set

/-- **Every compact set lies in an open connected relatively compact set.**

Take a compact connected `L ⊇ K ∪ {x₀}` (`Work.SimplyConnected.ABS.exists_isCompact_isConnected_superset`),
a compact `C` with `L ⊆ interior C`, and the connected component of `x₀` in `interior C`: it is open
(local connectedness), connected, contains `L` (which is connected and meets it), and its closure is
contained in the compact `C`. -/
theorem exists_isOpen_isConnected_isCompact_closure_superset {X : Type*} [TopologicalSpace X]
    [T2Space X] [ConnectedSpace X] [LocallyCompactSpace X] [LocallyConnectedSpace X]
    [LocallyPathConnectedSpace X] {K : Set X} (hK : IsCompact K) :
    ∃ Ω : Set X, IsOpen Ω ∧ IsConnected Ω ∧ IsCompact (closure Ω) ∧ K ⊆ Ω := by
  classical
  let x₀ : X := Classical.choice (inferInstance : Nonempty X)
  obtain ⟨L, hLc, hLconn, hKL⟩ :=
    Work.SimplyConnected.ABS.exists_isCompact_isConnected_superset (X := X) hK x₀
  obtain ⟨C, hCc, hLC⟩ := exists_compact_superset hLc
  have hxL : x₀ ∈ L := hKL (Or.inr (mem_singleton x₀))
  have hxC : x₀ ∈ interior C := hLC hxL
  refine ⟨connectedComponentIn (interior C) x₀, isOpen_interior.connectedComponentIn,
    isConnected_connectedComponentIn_iff.mpr hxC, ?_, ?_⟩
  · refine hCc.of_isClosed_subset isClosed_closure ?_
    exact (closure_mono (connectedComponentIn_subset _ _)).trans
      ((IsClosed.closure_subset_iff hCc.isClosed).mpr interior_subset)
  · exact (subset_union_left.trans hKL).trans
      ((hLconn.isPreconnected).subset_connectedComponentIn hxL hLC)

end Work.Topology.Engulf
