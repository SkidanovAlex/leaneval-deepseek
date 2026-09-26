import Mathlib
import Submission.Work.Smooth.JordanSeparation.plApprox
import Submission.Work.Smooth.JordanSeparation.plCut

/-!
# Splitting a polygonal loop at a vertex (step (B), first piece)

`exists_polygonal_homotopic` (step (A)) represents a loop in an open set as the join
`joinNat F N` of its chords, lifted into the open set.  The induction of step (B) cuts such a join
at a *repeated vertex*: if `p i = p j` with `i < j`, the loop splits as
`(join of the first i) · (the piece from i to j) · (the rest)`, where the middle piece is a loop at
`p i` and the complementary loop is the first and last pieces combined; then
`nullhomotopic_trans_trans_of_nullhomotopic` (`plCut.lean`) concludes the induction step.

This file contains the first piece of that: the splitting of a joined family of paths at an index.
-/

namespace Work.Smooth.JordanSeparation

noncomputable section

variable {X : Type*} [TopologicalSpace X]

/-- **Splitting a joined family of paths at an index.**  The join of the first `i + j` paths is
homotopic, as a path from `p 0` to `p (i + j)`, to the join of the first `i` paths followed by the
join of the next `j`. -/
theorem joinNat_add {p : ℕ → X} (F : ∀ k, Path (p k) (p (k + 1))) (i : ℕ) :
    ∀ j, Path.Homotopic (joinNat F (i + j))
      ((joinNat F i).trans (joinNat (p := fun k => p (i + k)) (fun k => F (i + k)) j))
  | 0 => (Path.Homotopic.trans_refl (joinNat F i)).symm
  | j + 1 => by
    exact (Path.Homotopic.hcomp (joinNat_add F i j) (Path.Homotopic.refl _)).trans
      (Path.Homotopic.trans_assoc (joinNat F i)
        (joinNat (p := fun k => p (i + k)) (fun k => F (i + k)) j) (F (i + j)))


/-! ### Finding the double point

The entry point of the induction of step (B): a closed polygonal vertex list which is *not* simple
has an ordered pair `i < j` of distinct indices with `v i = v j` which is not the trivial pair of
endpoints. -/

/-- **A non-simple closed polygonal list has a non-trivial double point.** -/
theorem exists_double_index_of_not_simple {n : ℕ} (v : Fin (n + 1) → ℂ)
    (hclose : v 0 = v (Fin.last n))
    (hnot : ¬ ∀ i j : Fin (n + 1), v i = v j →
      i = j ∨ (i = 0 ∧ j = Fin.last n) ∨ (j = 0 ∧ i = Fin.last n)) :
    ∃ i j : Fin (n + 1), i < j ∧ v i = v j ∧ (i ≠ 0 ∨ j ≠ Fin.last n) := by
  have _ := hclose
  push_neg at hnot
  obtain ⟨i, j, hij, hne, h1, h2⟩ := hnot
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · refine ⟨i, j, hlt, hij, ?_⟩
    by_cases h : i = 0
    · exact Or.inr (h1 h)
    · exact Or.inl h
  · refine ⟨j, i, hgt, hij.symm, ?_⟩
    by_cases h : j = 0
    · exact Or.inr (h2 h)
    · exact Or.inl h

end

end Work.Smooth.JordanSeparation
