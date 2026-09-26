import Mathlib
import Submission.Work.PTCert.letterDefs

namespace Work.PTCert

open Submission.PTCert

/-- Unfolding lemma: `pairOf` splits a number into quotient and (adjusted) remainder. -/
theorem pairOf_eq_pairOfPairIndex (r q : ℕ) :
    pairOf r q = (q / (r - 1),
      if q % (r - 1) < q / (r - 1) then q % (r - 1) else q % (r - 1) + 1) := by
  simp only [pairOf]

theorem pairOfPairIndex (r i j : ℕ) (hr : 2 ≤ r) (hi : i < r) (hj : j < r) (hij : i ≠ j) :
    Submission.PTCert.pairOf r (Submission.PTCert.pairIndex r i j) = (i, j) := by
  have hr1 : 0 < r - 1 := by omega
  rcases lt_trichotomy j i with hji | heq | hji'
  · -- j < i
    have hc : j < r - 1 := by omega
    have hpi : pairIndex r i j = (r - 1) * i + j := by
      simp only [pairIndex, mul_comm i (r - 1), if_pos hji]
    have hd : ((r - 1) * i + j) / (r - 1) = i := by
      rw [Nat.mul_add_div hr1, Nat.div_eq_of_lt hc, Nat.add_zero]
    have hm : ((r - 1) * i + j) % (r - 1) = j := by
      rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hc]
    rw [hpi, pairOf_eq_pairOfPairIndex, hd, hm, if_pos hji]
  · exact (hij heq.symm).elim
  · -- i < j
    have hc : j - 1 < r - 1 := by omega
    have hnj : ¬ j < i := by omega
    have hpi : pairIndex r i j = (r - 1) * i + (j - 1) := by
      simp only [pairIndex, mul_comm i (r - 1), if_neg hnj]
    have hd : ((r - 1) * i + (j - 1)) / (r - 1) = i := by
      rw [Nat.mul_add_div hr1, Nat.div_eq_of_lt hc, Nat.add_zero]
    have hm : ((r - 1) * i + (j - 1)) % (r - 1) = j - 1 := by
      rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hc]
    have hnot : ¬ (j - 1 < i) := by omega
    rw [hpi, pairOf_eq_pairOfPairIndex, hd, hm, if_neg hnot, Nat.sub_add_cancel (by omega : 1 ≤ j)]

end Work.PTCert
