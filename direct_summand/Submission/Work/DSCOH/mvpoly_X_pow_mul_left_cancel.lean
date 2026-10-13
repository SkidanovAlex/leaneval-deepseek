import Mathlib
import Submission.Work.DSCOH.Basic

namespace Work.DSCOH

theorem mvpoly_X_pow_mul_left_cancel {A : Type*} [CommRing A] {n : ℕ} (i : Fin n) (a : ℕ)
    {p q : Poly A n}
    (h : (MvPolynomial.X i : Poly A n) ^ a * p = (MvPolynomial.X i : Poly A n) ^ a * q) :
    p = q := by
  -- `X i ^ a` is a regular element of `MvPolynomial (Fin n) A`: multiplication by it on the
  -- left is injective (`MvPolynomial.isRegular_X_pow`).
  exact (MvPolynomial.isRegular_X_pow (R := A) (n := i) a).left h

end Work.DSCOH
