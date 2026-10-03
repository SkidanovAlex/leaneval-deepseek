import Mathlib
import Submission.Lib.Unif2.Commons.Topology.Surface.exists_locallyFinite_coordinateBall_cover_of_noncompact
import Submission.Lib.Unif2.Work.Topology.Connected.closure_cover_hint

/-!
# A countable open cover by relatively compact sets

Step 1 of the ABS exhaustion (Anghel--Bruin--Stan, *Uniformization of Riemann surfaces revisited*,
arXiv:2008.12189, "Exhaustion by compact simply-connected submanifolds"): the cover from which the
exhaustion function `g` is built.  This is the *non-circular* road to the parabolic case of
`Work.SimplyConnected.ABS.exists_chart_with_room_locallyBiholomorphic` — unlike the RegPiece/Perron
route it uses no Green function, no barriers and no embedding (see
`NOTES_frontierConnected_superset_ROUTE_ANALYSIS.md` §41, §46).

**Construction.**  `Commons.Topology.Surface.exists_locallyFinite_coordinateBall_cover_of_noncompact`
gives a locally finite cover `C` of `X` by *compact* coordinate balls.  Then
`Commons.Topology.Connected.interior_closure_cover_of_locallyFinite` says that for a locally finite
covering family `C` every point lies in the *interior* of a finite prefix-union of the closures of the
`C n`; taking `V n := interior (⋃ i < n, closure (C i))` therefore gives an open cover, and each
`V n` is contained in a finite union of compact sets, so `closure (V n)` is compact.  (For
`n = 0`, `V 0 = ∅`, which is harmless.)  The family is *increasing* — local finiteness is not
available for it, which is why the exhaustion function of the next step must be built from a
partition of unity subordinate to the annuli
`V (n+1) \ closure (V n)` rather than to `V` itself.
-/

open Set

namespace Work.SimplyConnected.ABS.OneEnded

/-- **A countable open cover of a non-compact surface by relatively compact sets.** -/
theorem exists_isOpen_isCompact_closure_cover {X : Type*} [TopologicalSpace X] [T2Space X]
    [SecondCountableTopology X] [ChartedSpace ℂ X] (hX : ¬ CompactSpace X) :
    ∃ V : ℕ → Set X, (∀ n, IsOpen (V n)) ∧ (∀ n, IsCompact (closure (V n))) ∧
      (⋃ n, V n) = Set.univ ∧ (∀ n, V n ⊆ V (n + 1)) := by
  obtain ⟨c, r, -, -, hcomp, hcov, hlf⟩ :=
    Commons.Topology.Surface.exists_locallyFinite_coordinateBall_cover_of_noncompact
      (X := X) hX
  set C : ℕ → Set X := fun n => (chartAt ℂ (c n)).symm ''
      Metric.closedBall ((chartAt ℂ (c n)) (c n)) (r n) with hC
  have hcovC : ∀ y : X, y ∈ ⋃ n, C n := by
    intro y
    rw [hC, hcov]
    exact Set.mem_univ y
  refine ⟨fun n => interior (⋃ i ∈ Finset.range n, closure (C i)), fun n => isOpen_interior,
    ?_, ?_, ?_⟩
  · intro n
    have hcl : IsClosed (⋃ i ∈ Finset.range n, closure (C i)) :=
      isClosed_biUnion_finset fun i _ => isClosed_closure
    have hU : IsCompact (⋃ i ∈ Finset.range n, closure (C i)) :=
      Set.Finite.isCompact_biUnion (Finset.finite_toSet _) fun i _ => (hcomp i).closure
    exact hU.of_isClosed_subset isClosed_closure (closure_minimal interior_subset hcl)
  · rw [Set.eq_univ_iff_forall]
    intro x
    obtain ⟨n, hn⟩ :=
      Commons.Topology.Connected.interior_closure_cover_of_locallyFinite C hlf hcovC
        (∅ : Set X) x
    exact Set.mem_iUnion.mpr ⟨n, by simpa using hn⟩

  · intro n
    refine interior_mono ?_
    intro x hx
    obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp hx
    exact mem_iUnion₂.mpr ⟨i, Finset.mem_range.mpr
      (lt_of_lt_of_le (Finset.mem_range.mp hi) (Nat.le_succ n)), hxi⟩

/-- **A level function against an increasing relatively compact cover.**

If `V` is an increasing open cover of `X` and every `closure (U n)` is compact, then each
`closure (U n)` lies in a *single* `V k`: compactness gives finitely many `V k`'s and monotonicity
collapses them to the largest.  This is the `lvl` of §50 of the route notes, and it is the step that
turns a locally finite cover into an exhaustion function. -/
theorem exists_level_function {X : Type*} [TopologicalSpace X] {U V : ℕ → Set X}
    (hVo : ∀ n, IsOpen (V n)) (hVmono : Monotone V) (hVcov : (⋃ n, V n) = Set.univ)
    (hUc : ∀ n, IsCompact (closure (U n))) :
    ∃ lvl : ℕ → ℕ, ∀ n, closure (U n) ⊆ V (lvl n) := by
  have key : ∀ n, ∃ k, closure (U n) ⊆ V k := by
    intro n
    have hcov : closure (U n) ⊆ ⋃ k, V k := by rw [hVcov]; exact subset_univ _
    obtain ⟨s, hs⟩ := (hUc n).elim_finite_subcover V hVo hcov
    refine ⟨s.sup id, fun x hx => ?_⟩
    obtain ⟨k, hks, hkx⟩ := mem_iUnion₂.mp (hs hx)
    exact hVmono (Finset.le_sup (f := id) hks) hkx
  exact ⟨fun n => Classical.choose (key n), fun n => Classical.choose_spec (key n)⟩

end Work.SimplyConnected.ABS.OneEnded
