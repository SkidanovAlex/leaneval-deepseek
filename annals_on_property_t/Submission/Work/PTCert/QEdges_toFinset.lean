import Mathlib
import Submission.Work.PTCert.QAdjOpDefs

namespace Work.PTCert

/-- Membership in the list `QEdges r`: a pair `(a,b)` occurs iff `a < b < r`. -/
theorem mem_QEdges (r : ℕ) (x : ℕ × ℕ) :
    x ∈ Submission.PTCert.QEdges r ↔ x.1 < x.2 ∧ x.2 < r := by
  rw [Submission.PTCert.QEdges]
  simp only [List.mem_flatMap, List.mem_filterMap, List.mem_range]
  constructor
  · rintro ⟨i, hi, j, hj, h⟩
    by_cases hij : i < j
    · rw [if_pos hij] at h
      simp only [Option.some.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨hij, hj⟩
    · rw [if_neg hij] at h
      exact absurd h (by simp)
  · rintro ⟨h1, h2⟩
    exact ⟨x.1, by omega, x.2, by omega, by rw [if_pos h1]⟩

/-- Membership in the image of the edges of the simplex under `edgePair`. -/
theorem mem_image_edgePair (r : ℕ) (x : ℕ × ℕ) :
    x ∈ (Finset.univ : Finset (Submission.RouteB.Edge r)).image
        (Submission.PTCert.edgePair (r := r)) ↔ x.1 < x.2 ∧ x.2 < r := by
  rw [Finset.mem_image]
  constructor
  · rintro ⟨p, -, hp⟩
    have h1 : p.1.1.val = x.1 := by
      simpa [Submission.PTCert.edgePair] using congrArg Prod.fst hp
    have h2 : p.1.2.val = x.2 := by
      simpa [Submission.PTCert.edgePair] using congrArg Prod.snd hp
    refine ⟨?_, ?_⟩
    · rw [← h1, ← h2]; exact p.2
    · rw [← h2]; exact p.1.2.isLt
  · rintro ⟨h1, h2⟩
    refine ⟨⟨(⟨x.1, by omega⟩, ⟨x.2, by omega⟩), by simp; omega⟩,
      Finset.mem_univ _, ?_⟩
    simp [Submission.PTCert.edgePair]

theorem QEdges_toFinset (r : ℕ) :
    (Submission.PTCert.QEdges r).toFinset =
      (Finset.univ : Finset (Submission.RouteB.Edge r)).image
        (Submission.PTCert.edgePair (r := r)) := by
  ext x
  rw [List.mem_toFinset, mem_QEdges, mem_image_edgePair]

end Work.PTCert
