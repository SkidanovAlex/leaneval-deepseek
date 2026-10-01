import Mathlib

namespace Work.LinnikBurgess

/-- The `n`-th power of the linear polynomial `C c * X` is `C (c^n) * X^n`. -/
lemma C_mul_X_pow_eq (c : ℤ) (n : ℕ) :
    (Polynomial.C c * Polynomial.X : Polynomial ℤ) ^ n = Polynomial.C (c ^ n) * Polynomial.X ^ n := by
  rw [mul_pow, Polynomial.C_pow]

lemma cftCoeffCompMulX (G : Polynomial ℤ) (c : ℤ) (i : ℕ) :
    (G.comp (Polynomial.C c * Polynomial.X)).coeff i = G.coeff i * c ^ i := by
  induction G using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [Polynomial.add_comp, Polynomial.coeff_add, Polynomial.coeff_add, hp, hq]
      ring
  | monomial n a =>
      rw [Polynomial.monomial_comp, C_mul_X_pow_eq]
      rw [← mul_assoc, ← Polynomial.C_mul, Polynomial.C_mul_X_pow_eq_monomial,
        Polynomial.coeff_monomial, Polynomial.coeff_monomial]
      by_cases h : n = i <;> simp [h]

end Work.LinnikBurgess
