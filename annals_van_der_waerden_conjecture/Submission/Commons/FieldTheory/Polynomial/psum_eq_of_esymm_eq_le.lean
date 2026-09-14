import Mathlib
import Submission.Commons.FieldTheory.Polynomial.multiset_psum_newton

namespace Commons.FieldTheory.Polynomial

/-- If two multisets `s`, `t` have the same cardinality and the same elementary symmetric
functions `e_i` for `1 ≤ i ≤ N`, then their power sums `p_j` agree for `1 ≤ j ≤ N`.

This is a consequence of Newton's identities: `p_j` is a universal integral polynomial in
`e_1, …, e_j` (no division by `j` is needed), hence determined by the elementary symmetric
functions. -/
theorem psum_eq_of_esymm_eq_le {F : Type*} [Field F] (s t : Multiset F) (N : ℕ)
    (hcard : s.card = t.card) (hN : N ≤ s.card)
    (h : ∀ i : ℕ, 1 ≤ i → i ≤ N → s.esymm i = t.esymm i) :
    ∀ j : ℕ, 1 ≤ j → j ≤ N → (s.map (· ^ j)).sum = (t.map (· ^ j)).sum := by
  have hE : ∀ i : ℕ, 1 ≤ i → i ≤ N → s.esymm i = t.esymm i := h
  have key : ∀ j : ℕ, 1 ≤ j → j ≤ N →
      (s.map (· ^ j)).sum = (t.map (· ^ j)).sum := by
    intro j
    induction j using Nat.strong_induction_on with
    | h j ih =>
      intro hj1 hjN
      have hsc : j ≤ s.card := le_trans hjN hN
      have htc : j ≤ t.card := le_trans hjN (hcard ▸ hN)
      rw [multiset_psum_newton s j hj1 hsc, multiset_psum_newton t j hj1 htc]
      have hsum : (∑ i ∈ Finset.Icc 1 (j - 1),
            (-1 : F) ^ i * s.esymm i * (s.map (· ^ (j - i))).sum)
          = (∑ i ∈ Finset.Icc 1 (j - 1),
            (-1 : F) ^ i * t.esymm i * (t.map (· ^ (j - i))).sum) := by
        apply Finset.sum_congr rfl
        intro i hi
        have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
        have hi2 : i ≤ j - 1 := (Finset.mem_Icc.mp hi).2
        have hlti : j - i < j := by omega
        have hge : 1 ≤ j - i := by omega
        have hle : j - i ≤ N := by omega
        rw [hE i hi1 (by omega), ih (j - i) hlti hge hle]
      rw [hE j hj1 hjN, hsum]
  exact key

end Commons.FieldTheory.Polynomial
