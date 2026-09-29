import Mathlib
import Submission.Commons.Algebra.Polynomial.dnum_def
import Submission.Commons.Algebra.WeylOps.opOf_def

namespace Commons.Algebra.Polynomial

open Classical
open Commons.Algebra.Polynomial

/-- Quotient rule, in the form suited to the induction: for a derivation `D` on `K(X)` that
extends the polynomial derivative, and `n ≥ 1`,
`D (A/q^n) = (A'·q − n·A·q')/q^{n+1}`.

This is exactly the recurrence defining `dnum`, read on `RatFunc K`. -/
lemma deriv_div_pow {K : Type*} [Field K]
    (D : Derivation K (RatFunc K) (RatFunc K))
    (hd : ∀ p : Polynomial K, D (algebraMap (Polynomial K) (RatFunc K) p)
      = algebraMap (Polynomial K) (RatFunc K) p.derivative)
    {q : Polynomial K} (hq : q ≠ 0) (A : Polynomial K) {n : ℕ} (hn : 1 ≤ n) :
    D (algebraMap (Polynomial K) (RatFunc K) A
        / (algebraMap (Polynomial K) (RatFunc K) q) ^ n)
      = algebraMap (Polynomial K) (RatFunc K)
          (A.derivative * q - Polynomial.C (n : K) * (A * q.derivative))
        / (algebraMap (Polynomial K) (RatFunc K) q) ^ (n + 1) := by
  set aq : RatFunc K := algebraMap (Polynomial K) (RatFunc K) q with haq
  set aA : RatFunc K := algebraMap (Polynomial K) (RatFunc K) A with haA
  have hq0 : aq ≠ 0 := by rw [haq]; exact RatFunc.algebraMap_ne_zero hq
  have hDq : D aq = algebraMap (Polynomial K) (RatFunc K) q.derivative := by
    rw [haq]; exact hd q
  have hDA : D aA = algebraMap (Polynomial K) (RatFunc K) A.derivative := by
    rw [haA]; exact hd A
  rw [Derivation.leibniz_div, hDA, Derivation.leibniz_pow, hDq]
  simp only [smul_eq_mul, nsmul_eq_mul]
  rw [show algebraMap (Polynomial K) (RatFunc K)
        (A.derivative * q - Polynomial.C (n : K) * (A * q.derivative))
      = algebraMap (Polynomial K) (RatFunc K) A.derivative * aq
        - (n : RatFunc K) * (aA * algebraMap (Polynomial K) (RatFunc K) q.derivative) from by
    simp only [map_sub, map_mul]
    rw [haq, haA]
    simp]
  have hbpow : aq ^ n = aq * aq ^ (n - 1) := by rw [← pow_succ']; congr 1; omega
  field_simp
  rw [pow_succ, sq, hbpow]
  ring

/-- The iterated derivative of a quotient of polynomials: for the derivative `D` on `K(X)`,
`D^j (p/q) = C_j / q^{j+1}` where `C_j = dnum p q j` is the recursively defined numerator. -/
theorem iterate_deriv_div_dnum {K : Type*} [Field K]
    (D : Derivation K (RatFunc K) (RatFunc K))
    (hd : ∀ p : Polynomial K, D (algebraMap (Polynomial K) (RatFunc K) p)
      = algebraMap (Polynomial K) (RatFunc K) p.derivative)
    (p q : Polynomial K) (hq : q ≠ 0) (j : ℕ) :
    (D : RatFunc K → RatFunc K)^[j]
        (algebraMap (Polynomial K) (RatFunc K) p / algebraMap (Polynomial K) (RatFunc K) q)
      = algebraMap (Polynomial K) (RatFunc K) (dnum p q j)
        / (algebraMap (Polynomial K) (RatFunc K) q) ^ (j + 1) := by
  induction j with
  | zero => simp [dnum]
  | succ j ih =>
      rw [Function.iterate_succ_apply', ih]
      rw [deriv_div_pow D hd hq (dnum p q j) (by omega : 1 ≤ j + 1)]
      rw [dnum_def]

end Commons.Algebra.Polynomial
