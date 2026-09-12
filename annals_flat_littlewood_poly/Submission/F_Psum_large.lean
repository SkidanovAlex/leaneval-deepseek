import Mathlib
import Submission.RSPsum_defs

noncomputable section
open scoped Polynomial BigOperators
open Polynomial Complex

namespace Submission
namespace RudinShapiro

/-- `P t` is the sum of its first `2^t` monomial terms (all other coefficients vanish). -/
lemma Psum_trunc_self (t : ℕ) : Psum t (2 ^ t) = P t := by
  unfold Psum
  have hdeg : (P t).natDegree < 2 ^ t := by
    have h1 : 2 ^ t - 1 < 2 ^ t := by
      have : 0 < 2 ^ t := two_pow_pos t
      omega
    exact lt_of_le_of_lt (P_natDegree_le t) h1
  exact (as_sum_range_C_mul_X_pow' (P t) hdeg).symm

lemma Psum_large (t m : ℕ) : Psum (t + 1) (2 ^ t + m) = P t + X ^ 2 ^ t * Qsum t m := by
  calc
    Psum (t + 1) (2 ^ t + m)
        = ∑ k ∈ Finset.range (2 ^ t + m), C ((P (t + 1)).coeff k) * X ^ k := by rfl
    _ = (∑ k ∈ Finset.range (2 ^ t), C ((P (t + 1)).coeff k) * X ^ k)
          + ∑ j ∈ Finset.range m, C ((P (t + 1)).coeff (2 ^ t + j)) * X ^ (2 ^ t + j) := by
          rw [Finset.sum_range_add]
    _ = Psum t (2 ^ t) + X ^ 2 ^ t * Qsum t m := by
          congr 1
          · unfold Psum
            apply Finset.sum_congr rfl
            intro k hk
            rw [coeff_P_extend t k (Finset.mem_range.mp hk)]
          · unfold Qsum
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j hj
            rw [coeff_P_top, pow_add]
            ring
    _ = P t + X ^ 2 ^ t * Qsum t m := by rw [Psum_trunc_self]

end RudinShapiro
end Submission
