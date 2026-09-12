import Mathlib
import Submission.Commons.LorentzianPolynomials.hessian_aeval_eq

open Finsupp Matrix MvPolynomial

set_option autoImplicit false

namespace Commons.LorentzianPolynomials

theorem hessian_aeval_eq_challenge (n : ℕ) (f : H n 2) (z : Fin n → ℂ) :
    2 * MvPolynomial.aeval z f.1 =
      ∑ i : Fin n, ∑ j : Fin n, f.hessian i j * z i * z j := by
  exact hessian_aeval_eq n f z

end Commons.LorentzianPolynomials
