import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Data.Matrix.Mul

namespace Commons.Algebra.Matrix

theorem coeff_mul_monomial_ite {A : Type*} [Semiring A] (p : Polynomial A) (b n : ℕ) (c : A) :
    (p * Polynomial.monomial b c).coeff n
      = (if b ≤ n then p.coeff (n - b) else 0) * c := by
  rw [← Polynomial.C_mul_X_pow_eq_monomial, ← mul_assoc, Polynomial.coeff_mul_X_pow',
    Polynomial.coeff_mul_C]
  by_cases h : b ≤ n
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h, zero_mul]

theorem mulVec_sum_monomial_coeff {A : Type*} [CommRing A] {R S : Type*} [Fintype R] [Fintype S]
    (e : ℕ) (M : Matrix R S (Polynomial A)) (z : S × Fin (e + 1) → A) (i : R) (n : ℕ) :
    ((Matrix.mulVec M fun j => ∑ b : Fin (e + 1), Polynomial.monomial (b : ℕ) (z (j, b))) i).coeff n
      = ∑ p : S × Fin (e + 1),
          (if (p.2 : ℕ) ≤ n then (M i p.1).coeff (n - (p.2 : ℕ)) else 0) * z p := by
  rw [Matrix.mulVec_apply_eq_sum]
  simp only [Polynomial.finsetSum_coeff, Finset.mul_sum]
  simp_rw [coeff_mul_monomial_ite]
  rw [Fintype.sum_prod_type]

end Commons.Algebra.Matrix