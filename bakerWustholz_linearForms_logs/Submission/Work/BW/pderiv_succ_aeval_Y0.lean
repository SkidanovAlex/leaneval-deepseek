import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- A polynomial in `Y₀` alone (here `q(Y₀ + c)` with `q ∈ ℚ[X]`) is killed by `∂/∂Y_i` for
`i ≠ 0`, i.e. by `pderiv i.succ` for `i : Fin r`. -/
theorem pderiv_succ_aeval_Y0 {r : ℕ} (i : Fin r) (c : ℂ) (q : Polynomial ℚ) :
    (MvPolynomial.pderiv i.succ)
        (Polynomial.aeval (MvPolynomial.X 0 + MvPolynomial.C c) q) = 0 := by
  -- `∂/∂Y_i` kills `Y₀ + c`, since `i.succ ≠ 0`.
  have hX : MvPolynomial.pderiv i.succ (MvPolynomial.X 0 + MvPolynomial.C c) = 0 := by
    rw [map_add, MvPolynomial.pderiv_C, add_zero]
    exact MvPolynomial.pderiv_X_of_ne (Fin.succ_ne_zero i).symm
  -- `q(Y₀ + c)` is a sum of terms `C a * (Y₀ + c)^n`; differentiate termwise.
  induction q using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [Polynomial.aeval_add, map_add, hp, hq, add_zero]
  | monomial n a =>
      rw [Polynomial.aeval_monomial, MvPolynomial.algebraMap_apply, MvPolynomial.pderiv_C_mul,
        MvPolynomial.pderiv_pow, hX]
      simp

end Work.BW
