import Mathlib.Algebra.Polynomial.Taylor

namespace Commons.Algebra.Polynomial

open _root_.Polynomial

theorem X_sub_C_pow_dvd_of_hasseDeriv_eval_eq_zero {F : Type*} [Field F] (f : Polynomial F) (a : F) (l : ℕ) (h : ∀ k < l, Polynomial.eval a (Polynomial.hasseDeriv k f) = 0) : (Polynomial.X - Polynomial.C a) ^ l ∣ f := by
  rw [← sum_taylor_eq f a]
  rw [Polynomial.sum]
  apply Finset.dvd_sum
  intro i hi
  have hli : l ≤ i := by
    by_contra hlt
    rw [not_le] at hlt
    exact (mem_support_iff.mp hi) (by rw [taylor_coeff, h i hlt])
  exact dvd_mul_of_dvd_right (pow_dvd_pow (X - C a) hli) (C ((taylor a f).coeff i))

end Commons.Algebra.Polynomial