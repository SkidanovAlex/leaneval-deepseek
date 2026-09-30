import Mathlib
import Submission.Work.BW.DefsAC

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

theorem pderiv_succ_aeval_scaled {r : ℕ} (i : Fin r) (a c : ℂ) (q : Polynomial ℚ) :
    (MvPolynomial.pderiv i.succ)
        (Polynomial.aeval (MvPolynomial.C a * MvPolynomial.X 0 + MvPolynomial.C c) q) = 0 := by
  -- `∂/∂Y_i` kills the affine linear form `a·Y₀ + c`, since `i.succ ≠ 0`.
  have hX : MvPolynomial.pderiv i.succ
      (MvPolynomial.C a * MvPolynomial.X 0 + MvPolynomial.C c) = 0 := by
    rw [map_add, MvPolynomial.pderiv_C, add_zero, MvPolynomial.pderiv_C_mul,
      MvPolynomial.pderiv_X_of_ne (Fin.succ_ne_zero i).symm, mul_zero]
  -- `q(a·Y₀ + c)` is a sum of terms `C b * (a·Y₀ + c)^n`; differentiate termwise.
  induction q using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [Polynomial.aeval_add, map_add, hp, hq, add_zero]
  | monomial n b =>
      rw [Polynomial.aeval_monomial, MvPolynomial.algebraMap_apply, MvPolynomial.pderiv_C_mul,
        MvPolynomial.pderiv_pow, hX]
      simp

end Work.BW
