import Mathlib
import Submission.RSPsum_defs

noncomputable section
open scoped Polynomial BigOperators
open Polynomial Complex

namespace Submission
namespace RudinShapiro

lemma Psum_ge (t m : ℕ) (hm : 2 ^ t ≤ m) : Psum t m = P t := by
  apply Polynomial.ext
  intro n
  by_cases hnm : n < m
  · rw [Psum]
    rw [Polynomial.finsetSum_coeff]
    simp_rw [Polynomial.coeff_C_mul_X_pow]
    rw [Finset.sum_ite_eq]
    simp [hnm]
  · rw [Psum]
    rw [Polynomial.finsetSum_coeff]
    simp_rw [Polynomial.coeff_C_mul_X_pow]
    have hsum : (∑ k ∈ Finset.range m, if n = k then (P t).coeff k else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      have hmn : m ≤ n := by omega
      have hkn : k ≠ n := by
        have hklt : k < m := Finset.mem_range.mp hk
        omega
      refine if_neg ?_
      intro hnk
      exact hkn hnk.symm
    rw [hsum]
    exact (coeff_P_ge t n (by omega)).symm

end RudinShapiro
end Submission
