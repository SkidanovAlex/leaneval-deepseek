import Mathlib
import Submission.Commons.NumberTheory.Chebyshev.lcmUpto_even_dvd_binom_mul
import Submission.Commons.NumberTheory.Chebyshev.dvd_lcmUpto_mul_choose_two_mul_self
import Submission.Commons.NumberTheory.NumberField.choose_two_mul_sub_one

namespace Commons.NumberTheory.Chebyshev

theorem dvd_lcmUpto_mul_choose_two_mul_sub_one (n : ℕ) (hn : 1 ≤ n) :
    n * Nat.choose (2 * n - 1) (n - 1) ∣ Nat.lcmUpto (2 * n) := by
  -- `C(2n-1, n-1) = C(2n-1, n)` by symmetry of binomial coefficients.
  have hsym : Nat.choose (2 * n - 1) (n - 1) = Nat.choose (2 * n - 1) n := by
    have h := Nat.choose_symm (n := 2 * n - 1) (k := n) (by omega)
    rwa [show 2 * n - 1 - n = n - 1 by omega] at h
  -- `C(2n, n) = 2 * C(2n-1, n-1)` by Pascal's rule.
  have hC : Nat.choose (2 * n) n = 2 * Nat.choose (2 * n - 1) (n - 1) := by
    have h := Commons.NumberTheory.NumberField.choose_two_mul_sub_one n hn
    rw [show n + n - 1 = 2 * n - 1 by omega] at h
    rw [Nat.centralBinom_eq_two_mul_choose] at h
    rw [← hsym] at h
    exact h.symm
  -- Hence `C(2n-1, n-1)` divides `C(2n, n)`.
  have hdvd : Nat.choose (2 * n - 1) (n - 1) ∣ Nat.choose (2 * n) n := by
    rw [hC]
    exact ⟨2, by ring⟩
  exact dvd_trans (Nat.mul_dvd_mul_left n hdvd)
    (dvd_lcmUpto_mul_choose_two_mul_self n hn)

end Commons.NumberTheory.Chebyshev
