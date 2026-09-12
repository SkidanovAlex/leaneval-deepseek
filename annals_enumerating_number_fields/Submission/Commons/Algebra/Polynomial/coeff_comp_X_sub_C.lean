import Mathlib.Algebra.Polynomial.Monic

namespace Commons.Algebra.Polynomial

/-- The `n`-th coefficient of `(X - c)^n` is `1`. -/
theorem coeff_X_sub_C_pow_self {R : Type*} [CommRing R] (c : R) (n : ℕ) :
    ((Polynomial.X - Polynomial.C c) ^ n).coeff n = 1 := by
  nontriviality R
  have hmonic : (Polynomial.X - Polynomial.C c).Monic := Polynomial.monic_X_sub_C c
  have hnd : ((Polynomial.X - Polynomial.C c) ^ n).natDegree = n := by
    rw [hmonic.natDegree_pow, Polynomial.natDegree_X_sub_C, mul_one]
  have := (hmonic.pow n).coeff_natDegree
  rwa [hnd] at this

/-- The `n`-th coefficient of `(X - c)^e` vanishes when `e < n`. -/
theorem coeff_X_sub_C_pow_eq_zero {R : Type*} [CommRing R] (c : R) {e n : ℕ} (h : e < n) :
    ((Polynomial.X - Polynomial.C c) ^ e).coeff n = 0 := by
  apply Polynomial.coeff_eq_zero_of_natDegree_lt
  calc ((Polynomial.X - Polynomial.C c) ^ e).natDegree
      ≤ e * (Polynomial.X - Polynomial.C c).natDegree := Polynomial.natDegree_pow_le
    _ ≤ e * 1 := Nat.mul_le_mul_left e (Polynomial.natDegree_X_sub_C_le c)
    _ = e := mul_one e
    _ < n := h

/-- Translating the variable does not change the coefficient of degree `n` when `n` is at least the
degree of the polynomial: `(f (X - c)).coeff n = f.coeff n` for `n ≥ f.natDegree`. -/
theorem coeff_comp_X_sub_C {R : Type*} [CommRing R] (f : Polynomial R) (c : R) {n : ℕ}
    (hn : f.natDegree ≤ n) : (f.comp (Polynomial.X - Polynomial.C c)).coeff n = f.coeff n := by
  rw [Polynomial.comp_eq_sum_left, Polynomial.coeff_sum, Polynomial.sum_def]
  simp only [Polynomial.coeff_C_mul]
  rw [Finset.sum_eq_single n]
  · rw [coeff_X_sub_C_pow_self, mul_one]
  · intro e he hne
    rw [coeff_X_sub_C_pow_eq_zero c
      (lt_of_le_of_ne ((Polynomial.le_natDegree_of_mem_supp e he).trans hn) hne), mul_zero]
  · intro hnmem
    rw [Polynomial.mem_support_iff] at hnmem
    rw [not_not.mp hnmem, zero_mul]

end Commons.Algebra.Polynomial