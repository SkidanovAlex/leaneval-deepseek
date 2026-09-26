import Mathlib
import Submission.Work.PTCert.Interfaces
import Submission.Work.PTCert.pairArith

namespace Work.PTCert

open Submission.PTCert

/-- The `pairIdx` of a valid ordered pair `(i,j)` lies in the range `r * (r-1)`. -/
theorem pairIdx_lt (r i j : ℕ) (hr : 2 ≤ r) (hi : i < r) (hj : j < r) (_hij : i ≠ j) :
    pairIdx r i j < r * (r - 1) := by
  have he : (if j < i then j else j - 1) < r - 1 := by
    split_ifs with h
    · omega
    · omega
  rw [pairIdx]
  calc i * (r - 1) + (if j < i then j else j - 1)
      < i * (r - 1) + (r - 1) := by omega
    _ = (i + 1) * (r - 1) := by ring
    _ ≤ r * (r - 1) := Nat.mul_le_mul_right _ (by omega)

theorem pairOfChar (r : ℕ) (hr : 2 ≤ r) :
    (∀ q, q < r * (r - 1) → ∀ i j, Submission.PTCert.pairOf r q = (i, j) ↔
        i < r ∧ j < r ∧ i ≠ j ∧ q = i * (r - 1) + (if j < i then j else j - 1)) ∧
    (∀ i j, i < r → j < r → i ≠ j → ∃ q, q < r * (r - 1) ∧ Submission.PTCert.pairOf r q = (i, j)) := by
  constructor
  · intro q hq i j
    constructor
    · intro h
      have hb := pairOf_bounds hq
      rw [h] at hb
      have hpi := pairIdx_pairOf hq
      rw [h] at hpi
      exact ⟨hb.1, hb.2.1, hb.2.2, (by simpa [pairIdx] using hpi.symm)⟩
    · rintro ⟨hi, hj, hij, hq'⟩
      rw [hq']
      simpa [pairIdx] using pairOf_pairIdx hi hj hij
  · intro i j hi hj hij
    exact ⟨pairIdx r i j, pairIdx_lt r i j hr hi hj hij,
      by simpa [pairIdx] using pairOf_pairIdx hi hj hij⟩

end Work.PTCert
