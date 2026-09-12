import Mathlib
import Submission.RSPsum_defs

noncomputable section
open scoped Polynomial BigOperators
open Polynomial Complex

namespace Submission
namespace RudinShapiro

lemma Psum_coeff (t m i : ℕ) : (Psum t m).coeff i = if i < m then (P t).coeff i else 0 := by
  rw [Psum]
  rw [Polynomial.finsetSum_coeff]
  simp_rw [Polynomial.coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  simp [Finset.mem_range]

lemma Qsum_coeff (t m i : ℕ) : (Qsum t m).coeff i = if i < m then (Q t).coeff i else 0 := by
  rw [Qsum]
  rw [Polynomial.finsetSum_coeff]
  simp_rw [Polynomial.coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  simp [Finset.mem_range]

lemma Psum_full (t : ℕ) : Psum t (2 ^ t) = P t := by
  ext i
  rw [Psum_coeff]
  by_cases hi : i < 2 ^ t
  · simp [hi]
  · rw [if_neg hi]
    exact (coeff_P_ge t i (le_of_not_gt hi)).symm

lemma Qsum_large (t m : ℕ) : Qsum (t + 1) (2 ^ t + m) = P t - X ^ 2 ^ t * Qsum t m := by
  ext i
  rw [Qsum_coeff]
  rw [Polynomial.coeff_sub]
  rw [Polynomial.coeff_X_pow_mul']
  by_cases hlt : i < 2 ^ t
  · have hltm : i < 2 ^ t + m := by omega
    rw [if_pos hltm, coeff_Q_extend t i hlt, if_neg (not_le_of_gt hlt)]
    simp
  · have hge : 2 ^ t ≤ i := le_of_not_gt hlt
    by_cases hltm : i < 2 ^ t + m
    · let j := i - 2 ^ t
      have hij : i = 2 ^ t + j := by dsimp [j]; omega
      have hjm : j < m := by dsimp [j]; omega
      have hsubt : 2 ^ t + j - 2 ^ t = j := by omega
      have hge2 : 2 ^ t ≤ 2 ^ t + j := by omega
      rw [if_pos hltm, if_pos hge, hij]
      rw [coeff_Q_top t j, hsubt]
      rw [coeff_P_ge t (2 ^ t + j) hge2]
      rw [Qsum_coeff, if_pos hjm]
      simp
    · have hge2 : m ≤ i - 2 ^ t := by omega
      rw [if_neg hltm, if_pos hge, coeff_P_ge t i hge]
      rw [Qsum_coeff, if_neg (not_lt_of_ge hge2)]
      simp

end RudinShapiro
end Submission
