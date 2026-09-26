import Mathlib
import Submission.Work.PTCert.letterDefs

namespace Work.PTCert

open Submission.PTCert

theorem pairOf_eq_pairOfValid (r q : ℕ) :
    pairOf r q = (q / (r - 1), if q % (r - 1) < q / (r - 1) then q % (r - 1) else q % (r - 1) + 1) := by
  simp only [pairOf]

theorem pairOfValid (r q : ℕ) (hr : 2 ≤ r) (hq : q < r * (r - 1)) :
    (Submission.PTCert.pairOf r q).1 < r ∧ (Submission.PTCert.pairOf r q).2 < r ∧
      (Submission.PTCert.pairOf r q).1 ≠ (Submission.PTCert.pairOf r q).2 := by
  rw [pairOf_eq_pairOfValid]
  have hr1 : 0 < r - 1 := by omega
  have hj' : q % (r - 1) < r - 1 := Nat.mod_lt _ hr1
  have hi : q / (r - 1) < r := by
    rw [Nat.div_lt_iff_lt_mul hr1]
    omega
  by_cases h : q % (r - 1) < q / (r - 1)
  · rw [if_pos h]
    refine ⟨hi, by omega, by omega⟩
  · rw [if_neg h]
    refine ⟨hi, by omega, by omega⟩

end Work.PTCert
