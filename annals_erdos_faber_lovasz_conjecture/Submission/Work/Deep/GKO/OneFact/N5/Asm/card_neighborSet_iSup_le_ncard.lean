import Submission.Work.Deep.GKO.NarrowImports
import Submission.Work.Deep.GKO.OneFactDefs

namespace Work.Deep.GKO.OneFact.N5.Asm

/-- **A vertex has at most as many neighbours in an edge-disjoint union of matchings as there are
matchings meeting it.**

Let `M : ι → SimpleGraph (Fin n)` be a family of graphs, each of whose edge sets is a matching
(`IsMatching'`), and let `S ⊆ ι` contain every `i` for which `v` has a neighbour in `M i`.  Then
the number of neighbours of `v` in the union `⨆ i, M i` is at most `S.ncard`.

The reason is that the unique partner of `v` in each `M i` determines `i`: every neighbour `w` of
`v` in the union admits some index `i` with `(M i).Adj v w`, and that `i` is uniquely determined
by `w` because `M i` is a matching (so it has at most one edge at `v`).  Hence the map sending
`w` to some such `i` is an injection from the neighbour set of `v` into `S`.  The pairwise
edge-disjointness of the `M i` is not needed for this counting argument. -/
theorem card_neighborSet_iSup_le_ncard {n : ℕ} {ι : Type*} [Fintype ι]
    (M : ι → SimpleGraph (Fin n))
    (hM : ∀ i, Work.Deep.GKO.IsMatching' (M i))
    (hdisj : ∀ i j, i ≠ j → Disjoint (M i).edgeSet (M j).edgeSet)
    (S : Set ι) (v : Fin n) (hS : ∀ i, (∃ w, (M i).Adj v w) → i ∈ S) :
    Nat.card ((⨆ i, M i).neighborSet v) ≤ S.ncard := by
  classical
  have _hdisj := hdisj
  -- Every neighbour of `v` in the union is a neighbour in one of the `M i`.
  have hwit : ∀ w : ↥((⨆ i, M i).neighborSet v), ∃ i : ι, (M i).Adj v w.1 := by
    intro w
    have h : (⨆ i, M i).Adj v w.1 :=
      (SimpleGraph.mem_neighborSet (⨆ i, M i) v w.1).mp w.2
    rw [SimpleGraph.iSup_adj] at h
    exact h
  -- Choose, for each neighbour of `v`, an index witnessing the adjacency; it lies in `S`.
  let f : ↥((⨆ i, M i).neighborSet v) → ↥S :=
    fun w => ⟨Classical.choose (hwit w),
      hS _ ⟨w.1, Classical.choose_spec (hwit w)⟩⟩
  -- The chosen index is injective, because each `M i` is a matching.
  have hf : Function.Injective f := by
    intro w w' hww
    have hidx : Classical.choose (hwit w) = Classical.choose (hwit w') := by
      have := congrArg Subtype.val hww
      simpa [f] using this
    have h1 : (M (Classical.choose (hwit w))).Adj v w.1 := Classical.choose_spec (hwit w)
    have h2 : (M (Classical.choose (hwit w))).Adj v w'.1 := by
      have h := Classical.choose_spec (hwit w')
      rw [← hidx] at h
      exact h
    exact Subtype.ext (hM _ v _ _ h1 h2)
  have hcard := Nat.card_le_card_of_injective f hf
  simpa only [Nat.card_coe_set_eq] using hcard

end Work.Deep.GKO.OneFact.N5.Asm
