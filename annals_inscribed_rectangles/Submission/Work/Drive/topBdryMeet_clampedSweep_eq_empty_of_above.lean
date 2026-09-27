import Mathlib
import Submission.Work.Drive.SeamMeetDefs
import Submission.Work.Drive.clampedSweep
import Submission.Work.Drive.clampedSweepLevel
import Submission.Work.Drive.Interfaces

/-!
# The top of a clamped radial sweep is empty when the other two planes lie strictly below

`Work.Drive.clampedSweep (c k) ψ (P k)` is the radial sweep of the plane presentation `P k` from the
level `c k` (at `x 2 = 0`) up to the plane itself (at `x 2 = 1`).  On the top face `x 2 = 1` the sweep
*is* the plane (`Work.Drive.clampedSweep_face_one`), while for every `j` the level of the sweep never
exceeds the level of the plane it sweeps (`Work.Drive.levelOf_clampedSweep_le_local`).

Hence if, for every `j ≠ k`, `P j` is *strictly below* `P k` on the whole parameter box — the
hypothesis `habove` — the `k`-th block can never be on its top face at a triple point: the common point
shared by the three sweeps would have to have a level both `≤ levelOf (P j ·) < levelOf (P k ·)` and
`= levelOf (P k ·)`.  This is the geometric input that makes the "distinct level" design's top count
vanish for the block with the largest level (`ENDS_AND_SEAMS_NOTES.md`, `END_LEVEL_OBSTRUCTION.md`).
-/

namespace Work.Drive

open Manifold
open scoped Manifold ContDiff

/-- **The top boundary triple intersections of the clamped sweeps vanish when the other planes lie
strictly below.**  Assuming the levels of `P j` (`j ≠ k`) are bounded below by `c j` and are strictly
below every level of `P k` on the unit box, no triple point of the three clamped radial sweeps with
`ψ t = 1 - t` has its `k`-th parameter on the top face `x k 2 = 1`. -/
theorem topBdryMeet_clampedSweep_eq_empty_of_above (c : Fin 3 → ℝ)
    (P : Fin 3 → EuclideanSpace ℝ (Fin 2) → Work.Drive.CappingSpace) (k : Fin 3)
    (hc : ∀ j, 0 < c j)
    (hlow : ∀ j, j ≠ k → ∀ y ∈ Submission.Drive.unitBox 1, c j ≤ Work.Drive.levelOf (P j y))
    (habove : ∀ j, j ≠ k → ∀ y ∈ Submission.Drive.unitBox 1, ∀ y' ∈ Submission.Drive.unitBox 1,
      Work.Drive.levelOf (P j y) < Work.Drive.levelOf (P k y')) :
    Work.Drive.topBdryMeet Work.Drive.CappingSpace
      (fun j => Work.Drive.clampedSweep (c j) (fun r => 1 - r) (P j)) k = ∅ := by
  -- Name the three sweeps once and for all, so that `D j (x j)` maps directly to the hypotheses of
  -- `tripleBdryMeet`.
  set D : Fin 3 → EuclideanSpace ℝ (Fin 3) → Work.Drive.CappingSpace :=
    fun j => Work.Drive.clampedSweep (c j) (fun r => 1 - r) (P j) with hD
  change Work.Drive.topBdryMeet Work.Drive.CappingSpace D k = ∅
  rw [Set.eq_empty_iff_forall_notMem]
  intro x hx
  simp only [Work.Drive.topBdryMeet, Set.mem_ofPred_eq] at hx
  obtain ⟨htriple, hxk2⟩ := hx
  simp only [Work.Drive.tripleBdryMeet, Set.mem_ofPred_eq] at htriple
  obtain ⟨hbox, h01, h02, -⟩ := htriple
  -- All three sweeps meet at the same point of the capping space.
  have hto0 : ∀ j : Fin 3, D j (x j) = D 0 (x 0) := by
    intro j
    fin_cases j
    · rfl
    · exact h01.symm
    · exact h02.symm
  -- Pick any index `j ≠ k`; `Fin 3` has more than one element.
  obtain ⟨j, hjk⟩ := Fintype.exists_ne_of_one_lt_card (α := Fin 3) (by simp) k
  -- The two-parameter points lie in the unit box of the plane.
  have hyj : Work.Drive.mk2 (x j 0) (x j 1) ∈ Submission.Drive.unitBox 1 := by
    intro i
    fin_cases i
    · simpa using (hbox j) 0
    · simpa using (hbox j) 1
  have hyk : Work.Drive.mk2 (x k 0) (x k 1) ∈ Submission.Drive.unitBox 1 := by
    intro i
    fin_cases i
    · simpa using (hbox k) 0
    · simpa using (hbox k) 1
  -- The cutoff `ψ r = 1 - r` takes `[0,1]` to `[0,1]`.
  have hψ01 : ∀ t ∈ Set.Icc (0:ℝ) 1, (fun r => 1 - r) t ∈ Set.Icc (0:ℝ) 1 := by
    intro t ht
    exact ⟨by linarith [ht.2], by linarith [ht.1]⟩
  -- The `j`-th sweep does not exceed the level of its plane ...
  have hlevel_j : Work.Drive.levelOf (D j (x j)) ≤
      Work.Drive.levelOf (P j (Work.Drive.mk2 (x j 0) (x j 1))) :=
    Work.Drive.levelOf_clampedSweep_le_local (hc j) hψ01 (P j) (x j) (hbox j 2)
      (hlow j hjk _ hyj)
  -- ... while on its top face the `k`-th sweep *is* its plane.
  have hlevel_k : Work.Drive.levelOf (D k (x k)) =
      Work.Drive.levelOf (P k (Work.Drive.mk2 (x k 0) (x k 1))) := by
    change Work.Drive.levelOf
      (Work.Drive.clampedSweep (c k) (fun r => 1 - r) (P k) (x k)) = _
    rw [Work.Drive.clampedSweep_face_one (c k) (fun r => 1 - r) (P k) (by norm_num) (x k) hxk2]
  have hlt := habove j hjk (Work.Drive.mk2 (x j 0) (x j 1)) hyj
    (Work.Drive.mk2 (x k 0) (x k 1)) hyk
  -- The three sweeps meet, so the two levels agree: contradiction.
  have heq : Work.Drive.levelOf (D j (x j)) = Work.Drive.levelOf (D k (x k)) :=
    congrArg Work.Drive.levelOf ((hto0 j).trans (hto0 k).symm)
  linarith

end Work.Drive
