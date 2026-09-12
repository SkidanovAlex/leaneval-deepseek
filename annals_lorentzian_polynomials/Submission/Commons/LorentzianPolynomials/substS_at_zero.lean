import Mathlib
import Submission.Commons.LorentzianPolynomials.hessian_aeval_eq

namespace Commons.LorentzianPolynomials

open Finsupp MvPolynomial BigOperators
set_option autoImplicit false

theorem substS_at_zero (n d : ℕ) (f : Commons.LorentzianPolynomials.H n d) :
    MvPolynomial.aeval (fun j : Fin n =>
      MvPolynomial.C (1 - (0 : ℝ)) * MvPolynomial.X j +
        MvPolynomial.C (0 : ℝ) * (∑ i : Fin n, MvPolynomial.X i)) f.1 = f.1 := by
  have hfun : (fun j : Fin n =>
      MvPolynomial.C (1 - (0 : ℝ)) * MvPolynomial.X j +
        MvPolynomial.C (0 : ℝ) * (∑ i : Fin n, MvPolynomial.X i)) =
      (fun j : Fin n => MvPolynomial.X j) := by
    funext j
    simp
  rw [hfun]
  exact MvPolynomial.aeval_X_left_apply f.1

end Commons.LorentzianPolynomials
