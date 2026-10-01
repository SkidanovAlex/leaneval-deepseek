import Mathlib
import Submission.Work.LinnikBurgess.lf_defs
import Submission.Work.LinnikBurgess.critN_content_iff

/-!
# The Wronskian `critN a b` has degree at most `4`

For a triple `a : Fin 3 → ℕ` let `f_a = ∏_l (X + a_l) = cubicZ a` be the corresponding monic
cubic.  The Wronskian `critN a b = f_a' f_b - f_a f_b'` is *a priori* a difference of two
polynomials of degree `≤ 2 + 3 = 5`; the `X^5`-terms cancel because `f_a` and `f_b` are both
monic, so `critN a b` has degree at most `4`.

Concretely, writing `f_a = X^3 + A₁X^2 + A₂X + A₃` and `f_b = X^3 + B₁X^2 + B₂X + B₃`
(`A_k = esymm3 a (k-1)`, `B_k = esymm3 b (k-1)`) a direct expansion gives

`critN a b = C(B₁-A₁)X⁴ + 2C(B₂-A₂)X³ + C(-A₂B₁ + A₁B₂ + 3(B₃-A₃))X²
              + 2C(A₁B₃ - B₁A₃)X + C(A₂B₃ - B₂A₃)`,

an expansion with no terms in degree `≥ 5`; comparing coefficients at every degree `n ≥ 5`
(they all vanish) yields the degree bound.
-/

namespace Work.LinnikBurgess

open Polynomial

/-- The monic cubic `cubicZ a = ∏_l (X + a_l)` written as a polynomial in `X`, with the
elementary symmetric functions of `a` as coefficients. -/
private lemma cubicZ_eq_pow_expand (a : Fin 3 → ℕ) :
    cubicZ a = X^3 + C (esymm3 a 0) * X^2 + C (esymm3 a 1) * X + C (esymm3 a 2) := by
  rw [cubicZ, Fin.prod_univ_three]
  simp [esymm3]
  ring

/-- Explicit expansion of the Wronskian `critN a b` into powers of `X`: no term of degree `≥ 5`
occurs, because the `X⁵`-terms of `f_a' f_b` and `f_a f_b'` (both equal to `3X⁵`) cancel. -/
private lemma critN_eq_pow_expand (a b : Fin 3 → ℕ) :
    critN a b
      = C (esymm3 b 0 - esymm3 a 0) * X^4
        + C (2 * (esymm3 b 1 - esymm3 a 1)) * X^3
        + C (-esymm3 a 1 * esymm3 b 0 + esymm3 a 0 * esymm3 b 1
              + 3 * (esymm3 b 2 - esymm3 a 2)) * X^2
        + C (2 * esymm3 a 0 * esymm3 b 2 - 2 * esymm3 b 0 * esymm3 a 2) * X
        + C (esymm3 a 1 * esymm3 b 2 - esymm3 b 1 * esymm3 a 2) := by
  rw [critN, cubicZ_eq_pow_expand a, cubicZ_eq_pow_expand b]
  simp only [derivative_add, derivative_mul, derivative_C, derivative_X, derivative_pow,
    C_mul, C_add, C_sub, C_neg, C_eq_natCast, map_ofNat, mul_one]
  ring

/-- Every coefficient of degree `≥ 5` of an expansion in degrees `≤ 4` vanishes. -/
private lemma coeff_eq_zero_of_five_le {c4 c3 c2 c1 c0 : ℤ} {n : ℕ} (hn : 5 ≤ n) :
    (C c4 * X^4 + C c3 * X^3 + C c2 * X^2 + C c1 * X + C c0 : ℤ[X]).coeff n = 0 := by
  simp only [coeff_add, coeff_C_mul, coeff_X_pow, coeff_X, coeff_C]
  rw [if_neg (by omega : ¬ (n = 4)), if_neg (by omega : ¬ (n = 3)),
      if_neg (by omega : ¬ (n = 2)), if_neg (by omega : ¬ (1 = n)),
      if_neg (by omega : ¬ (n = 0))]
  ring

/-- A polynomial given by an expansion in degrees `≤ 4` has degree at most `4`. -/
private lemma natDegree_quart_expansion_le (c4 c3 c2 c1 c0 : ℤ) :
    (C c4 * X^4 + C c3 * X^3 + C c2 * X^2 + C c1 * X + C c0 : ℤ[X]).natDegree ≤ 4 := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro n hn
  exact coeff_eq_zero_of_five_le hn

/-- The Wronskian `critN a b = f_a' f_b - f_a f_b'` of two monic cubics has degree at most `4`. -/
theorem natDegree_critN_le_four (a b : Fin 3 → ℕ) : (critN a b).natDegree ≤ 4 := by
  rw [critN_eq_pow_expand]
  exact natDegree_quart_expansion_le _ _ _ _ _

end Work.LinnikBurgess
