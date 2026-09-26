import Mathlib
import Submission.Work.PTCert.Interfaces
import Submission.Work.PTCert.signCodesDefs

/-!
# The letter index: `pairOf` and `pairIdx` are mutually inverse

The letters `b1 r k`, `1 ≤ k < NB1 r`, are indexed by the ordered pairs `(i,j)`, `i ≠ j`, via
`q = (k-1)/4` and `(i,j) = pairOf r q`.  For the sign-flip computation we need the inverse map
`pairIdx r i j = i * (r-1) + (if j < i then j else j - 1)` (this is the index `q`, not the letter
index `k`): on the range `q < r * (r-1)` the two are mutually inverse, and `pairOf r q` is always
a pair of distinct elements of `Fin r`.
-/

set_option autoImplicit false

namespace Work.PTCert

open Submission.PTCert

/-- Unfolding of `pairOf` with the `let`s removed. -/
theorem pairOf_eq (r q : ℕ) :
    pairOf r q = (q / (r - 1),
      if q % (r - 1) < q / (r - 1) then q % (r - 1) else q % (r - 1) + 1) := by
  simp only [pairOf]

theorem pairOf_pairIdx {r i j : ℕ} (hi : i < r) (hj : j < r) (hij : i ≠ j) :
    pairOf r (pairIdx r i j) = (i, j) := by
  have hr1 : 0 < r - 1 := by omega
  rcases lt_trichotomy j i with hji | heq | hji'
  · have hc : j < r - 1 := by omega
    have hpi : pairIdx r i j = (r - 1) * i + j := by
      simp only [pairIdx, mul_comm i (r - 1), if_pos hji]
    have hd : ((r - 1) * i + j) / (r - 1) = i := by
      rw [Nat.mul_add_div hr1, Nat.div_eq_of_lt hc, Nat.add_zero]
    have hm : ((r - 1) * i + j) % (r - 1) = j := by
      rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hc]
    rw [hpi, pairOf_eq, hd, hm, if_pos hji]
  · exact (hij heq.symm).elim
  · have hc : j - 1 < r - 1 := by omega
    have hnj : ¬ j < i := by omega
    have hpi : pairIdx r i j = (r - 1) * i + (j - 1) := by
      simp only [pairIdx, mul_comm i (r - 1), if_neg hnj]
    have hd : ((r - 1) * i + (j - 1)) / (r - 1) = i := by
      rw [Nat.mul_add_div hr1, Nat.div_eq_of_lt hc, Nat.add_zero]
    have hm : ((r - 1) * i + (j - 1)) % (r - 1) = j - 1 := by
      rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hc]
    have hnot : ¬ (j - 1 < i) := by omega
    rw [hpi, pairOf_eq, hd, hm, if_neg hnot, Nat.sub_add_cancel (by omega : 1 ≤ j)]

theorem pairIdx_pairOf {r q : ℕ} (hq : q < r * (r - 1)) :
    pairIdx r (pairOf r q).1 (pairOf r q).2 = q := by
  have hr1 : 0 < r - 1 := by
    rcases Nat.eq_zero_or_pos (r - 1) with h | h
    · rw [h, mul_zero] at hq; omega
    · exact h
  have hdm : q / (r - 1) * (r - 1) + q % (r - 1) = q := by
    rw [mul_comm]
    exact Nat.div_add_mod q (r - 1)
  rw [pairOf_eq]
  by_cases h : q % (r - 1) < q / (r - 1)
  · rw [if_pos h]
    simp only [pairIdx]
    rw [if_pos h]
    exact hdm
  · rw [if_neg h]
    have hnot : ¬ (q % (r - 1) + 1 < q / (r - 1)) := by omega
    have hsub : q % (r - 1) + 1 - 1 = q % (r - 1) := by omega
    simp only [pairIdx]
    rw [if_neg hnot, hsub]
    exact hdm

theorem pairOf_bounds {r q : ℕ} (hq : q < r * (r - 1)) :
    (pairOf r q).1 < r ∧ (pairOf r q).2 < r ∧ (pairOf r q).1 ≠ (pairOf r q).2 := by
  have hr1 : 0 < r - 1 := by
    rcases Nat.eq_zero_or_pos (r - 1) with h | h
    · rw [h, mul_zero] at hq; omega
    · exact h
  have hj' : q % (r - 1) < r - 1 := Nat.mod_lt _ hr1
  have hi : q / (r - 1) < r := by
    rw [Nat.div_lt_iff_lt_mul hr1]
    omega
  rw [pairOf_eq]
  by_cases h : q % (r - 1) < q / (r - 1)
  · rw [if_pos h]
    omega
  · rw [if_neg h]
    omega

end Work.PTCert
