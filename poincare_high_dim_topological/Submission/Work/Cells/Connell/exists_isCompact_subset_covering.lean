import Mathlib
import Submission.Work.PL.Defs

namespace Work.Cells.Connell

/-- A finite open cover of a compact Hausdorff space can be shrunk to a cover by
compact sets: every compact Hausdorff space is locally compact, so the shrinking
lemma `exists_subset_iUnion_compact_subset_t2space` applied to the whole space
(`s = univ`) produces closed, hence compact, sets `K i ⊆ W i` covering `M`. -/
theorem exists_isCompact_subset_covering {M : Type*} [TopologicalSpace M] [T2Space M]
    [CompactSpace M] {m : ℕ} (W : Fin m → Set M) (hW : ∀ i, IsOpen (W i))
    (hcover : (⋃ i, W i) = Set.univ) :
    ∃ K : Fin m → Set M, (∀ i, IsCompact (K i) ∧ K i ⊆ W i) ∧
      (⋃ i, K i) = Set.univ := by
  obtain ⟨K, hKcov, _hKcl, hKsub, hKcomp⟩ :=
    exists_subset_iUnion_compact_subset_t2space (s := Set.univ) (u := W)
      isCompact_univ hW (fun x _ => Set.finite_univ.subset (Set.subset_univ _))
      (by rw [hcover])
  exact ⟨K, fun i => ⟨hKcomp i, hKsub i⟩, Set.eq_univ_of_univ_subset hKcov⟩

end Work.Cells.Connell
