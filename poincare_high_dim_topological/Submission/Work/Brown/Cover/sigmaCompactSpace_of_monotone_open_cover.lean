import Mathlib
import Submission.Work.Brown.Basic

namespace Work.Brown.Cover

open Set

/-- A countable open cover of `X` by σ-compact subspaces makes `X` σ-compact.

Indeed `X = ⋃ k, U k`, and each `U k` is σ-compact as a subspace, hence — since the
subtype inclusion `↥(U k) → X` is an embedding — its image `U k` is a σ-compact subset
of `X`.  A countable union of σ-compact subsets is σ-compact, so `univ` is σ-compact. -/
theorem sigmaCompactSpace_of_monotone_open_cover {X : Type*} [TopologicalSpace X] {U : ℕ → Set X}
    (hopen : ∀ k, IsOpen (U k)) (hcover : (⋃ k, U k) = Set.univ)
    (hsc : ∀ k, SigmaCompactSpace ↥(U k)) : SigmaCompactSpace X := by
  rw [← isSigmaCompact_univ_iff, ← hcover]
  apply isSigmaCompact_iUnion
  intro k
  exact (isSigmaCompact_iff_sigmaCompactSpace (s := U k)).mpr (hsc k)

end Work.Brown.Cover
