import Mathlib
import Submission.Work.Drive.SeamMeetDefs

/-!
# The split of the boundary triple intersections into seam / top / bottom

`Work.Drive.tripleBdryMeet M D k` is the set of triples of parameter points at which the three chains
`D 0, D 1, D 2` meet, with the `k`-th parameter on the boundary of its cube.  Since the boundary of the
cube has six faces, but the first two coordinates of the `k`-th parameter are the coordinates of the
*plane's own presentation* and the third is the sweep parameter, the boundary splits into three
geometrically different kinds of face:

* the seam faces `x k 0 ∈ {0,1}` or `x k 1 ∈ {0,1}` (`seamBdryMeet`);
* the top face `x k 2 = 1` (`topBdryMeet`), the plane `P_k` itself;
* the bottom face `x k 2 = 0` (`bottomBdryMeet`), the end face of the sweep.

This file proves that the three sets *partition* `tripleBdryMeet M D k` (the seam being disjoint from
the other two by the hypothesis `hdisj`, the top and bottom being disjoint because `0 ≠ 1`), so that
the cardinality of the boundary triple intersections is the sum of the three face counts — the
algebraic content of the "boundary summands" of Hugelmeyer's parity identities.
-/

namespace Work.Drive

/-- A point of the boundary of the `3`-cube which is not on the seam (`x 0` nor `x 1` in `{0,1}`)
lies on the top face `x 2 = 1` or on the bottom face `x 2 = 0`. -/
private lemma onSeam_or_sweepFace_of_mem_unitBoxBdry {y : EuclideanSpace ℝ (Fin 3)}
    (hy : y ∈ Submission.Drive.unitBoxBdry 2) :
    onSeam y ∨ y 2 = 1 ∨ y 2 = 0 := by
  obtain ⟨-, i, hi⟩ := hy
  fin_cases i
  · exact Or.inl (by rw [onSeam]; tauto)
  · exact Or.inl (by rw [onSeam]; tauto)
  · rcases hi with h | h
    · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl h)

theorem tripleBdryMeet_ncard_split (M : Type*) [TopologicalSpace M]
    (D : Fin 3 → EuclideanSpace ℝ (Fin 3) → M)
    (hdisj : ∀ (k : Fin 3) (x : Fin 3 → EuclideanSpace ℝ (Fin 3)),
      x ∈ Work.Drive.tripleBdryMeet M D k →
      ¬ (Work.Drive.onSeam (x k) ∧ (x k 2 = 0 ∨ x k 2 = 1)))
    (hfin : ∀ k : Fin 3, (Work.Drive.tripleBdryMeet M D k).Finite) (k : Fin 3) :
    (Work.Drive.tripleBdryMeet M D k).ncard
      = (Work.Drive.seamBdryMeet M D k).ncard + (Work.Drive.topBdryMeet M D k).ncard
        + (Work.Drive.bottomBdryMeet M D k).ncard := by
  classical
  -- The three sets cover the boundary triple intersections.
  have hunion : tripleBdryMeet M D k
      = seamBdryMeet M D k ∪ (topBdryMeet M D k ∪ bottomBdryMeet M D k) := by
    ext x
    constructor
    · intro hx
      obtain ⟨hbox, h01, h02, hbdk⟩ := hx
      rcases onSeam_or_sweepFace_of_mem_unitBoxBdry hbdk with h | h | h
      · exact Or.inl ⟨⟨hbox, h01, h02, hbdk⟩, h⟩
      · exact Or.inr (Or.inl ⟨⟨hbox, h01, h02, hbdk⟩, h⟩)
      · exact Or.inr (Or.inr ⟨⟨hbox, h01, h02, hbdk⟩, h⟩)
    · rintro (⟨hx, -⟩ | ⟨hx, -⟩ | ⟨hx, -⟩)
      · exact hx
      · exact hx
      · exact hx
  have hSfin : (seamBdryMeet M D k).Finite := (hfin k).subset (fun x hx => hx.1)
  have hTfin : (topBdryMeet M D k).Finite := (hfin k).subset (fun x hx => hx.1)
  have hBfin : (bottomBdryMeet M D k).Finite := (hfin k).subset (fun x hx => hx.1)
  -- The three pieces are pairwise disjoint.
  have hdST : Disjoint (seamBdryMeet M D k) (topBdryMeet M D k) := by
    rw [Set.disjoint_iff]
    rintro x ⟨hs, ht⟩
    exact hdisj k x hs.1 ⟨hs.2, Or.inr ht.2⟩
  have hdSB : Disjoint (seamBdryMeet M D k) (bottomBdryMeet M D k) := by
    rw [Set.disjoint_iff]
    rintro x ⟨hs, hb⟩
    exact hdisj k x hs.1 ⟨hs.2, Or.inl hb.2⟩
  have hdTB : Disjoint (topBdryMeet M D k) (bottomBdryMeet M D k) := by
    rw [Set.disjoint_iff]
    rintro x ⟨ht, hb⟩
    exact one_ne_zero (ht.2.symm.trans hb.2)
  rw [hunion]
  rw [Set.ncard_union_eq (hdST.union_right hdSB) hSfin (hTfin.union hBfin)]
  rw [Set.ncard_union_eq hdTB hTfin hBfin]
  ring

end Work.Drive
