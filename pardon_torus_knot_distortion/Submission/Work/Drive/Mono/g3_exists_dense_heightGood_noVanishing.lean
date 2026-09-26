import Mathlib
import Submission.Work.Drive.Mono.g3_exists_dense_heightGood_avoiding_chords
import Submission.Work.Drive.Mono.Band.HeightGoodDefs
import Submission.Work.Drive.Mono.NoGrazeDefs
import Submission.Work.Drive.Mono.exists_countable_heightGood_dense

/-!
# A countable dense set of good height directions with no vanishing coordinate

The sweep direction attached to a height direction `n` is
`v = orthDir (shiftVσ σ 1) (unitDir n)`, the normalised component of the `σ 2`-axis orthogonal to
`n`.  This file records the purely set-theoretic half of
`Work.Drive.Mono.g3_exists_dense_heightGood_avoiding_chords`: the good height directions
(`Work.Drive.Mono.Band.HeightGood`) can be chosen inside a countable dense set `Q'` on which `v`
has **no vanishing coordinate**.

The point is that `g3_orthDir_unitDir_coord_ne_zero` says that a direction `n` all of whose
coordinates are non-zero produces a sweep direction with all coordinates non-zero, and the set of
such `n` is open and dense (`g3_isOpen_noVanishingCoord`, `g3_dense_noVanishingCoord`).  Hence
intersecting the countable dense set of good directions
(`Work.Drive.Mono.exists_countable_heightGood_dense`) with that open dense set gives `Q'`.
-/

namespace Work.Drive.Mono

open LeanEval.KnotTheory.PardonDistortion
open scoped RealInnerProductSpace

noncomputable section

/-- **A countable dense set of good height directions with no vanishing sweep coordinate.**

Every `ng ∈ Q'` is a `HeightGood` height direction of the parametrised torus, `Q'` is countable and
dense, and the associated sweep direction `orthDir (shiftVσ σ 1) (unitDir ng)` has no vanishing
coordinate. -/
theorem g3_exists_dense_heightGood_noVanishing (ψ : Submission.Diffeo)
    (σ : Equiv.Perm (Fin 3)) :
    ∃ Q' : Set LeanEval.KnotTheory.PardonDistortion.R3, Q'.Countable ∧
      (∀ n ∈ Q', Work.Drive.Mono.Band.HeightGood ψ n) ∧
      (∀ U : Set LeanEval.KnotTheory.PardonDistortion.R3, IsOpen U → U.Nonempty →
        (U ∩ Q').Nonempty) ∧
      (∀ ng ∈ Q', ∀ j : Fin 3,
        (Work.Drive.Mono.orthDir (Work.BoxShrink.shiftVσ σ 1)
          (Work.Drive.Mono.unitDir ng)) j ≠ 0) := by
  classical
  obtain ⟨Q, hQc, hQH, hQd⟩ := exists_countable_heightGood_dense ψ
  refine ⟨Q ∩ g3_noVanishingCoord, hQc.mono Set.inter_subset_left, ?_, ?_, ?_⟩
  · intro n hn
    exact hQH n hn.1
  · -- the intersection of a dense set with an open dense set is dense
    intro U hU hne
    obtain ⟨n, hnU, hnZ⟩ := (dense_iff_inter_open.mp g3_dense_noVanishingCoord) U hU hne
    obtain ⟨n', ⟨hn'U, hn'Z⟩, hn'Q⟩ :=
      hQd (U ∩ g3_noVanishingCoord) (hU.inter g3_isOpen_noVanishingCoord) ⟨n, hnU, hnZ⟩
    exact ⟨n', hn'U, hn'Q, hn'Z⟩
  · intro ng hng j
    exact g3_orthDir_unitDir_coord_ne_zero hng.2 j

end

end Work.Drive.Mono
