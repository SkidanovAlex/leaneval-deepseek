import Mathlib
import Submission.Commons.LorentzianPolynomials.hessian_aeval_eq
import Submission.Commons.LorentzianPolynomials.strict_lorentzian_quadratic_stable
import Submission.Commons.LorentzianPolynomials.S_closed
import Submission.Commons.LorentzianPolynomials.strict_subset_L
import Submission.Commons.LorentzianPolynomials.strict_hessian_nonsing_and_index

namespace Commons.LorentzianPolynomials

open Finsupp Matrix MvPolynomial UpperHalfPlane Topology Set

set_option autoImplicit false

/-- Theorem 2.16(2) of Br&auml;nd&eacute;n--Huh, strict version: for a strictly Lorentzian
polynomial `g` of degree `d ≥ 2` (with `n ≥ 1` variables), the Hessian matrix
`(∂a∂b g(w))` evaluated at any strictly positive point `w` has at most one positive
real eigenvalue, i.e. the characteristic polynomial has at most one positive real root
(counted with multiplicity). -/
theorem strict_L_hessian_index_le_one (n d : ℕ) (hn : 0 < n) (hd : 2 ≤ d) :
    ∀ (g : Commons.LorentzianPolynomials.H n d),
      g ∈ Commons.LorentzianPolynomials.Ŀ n d → ∀ (w : Fin n → ℝ), (∀ k : Fin n, 0 < w k) →
      ((Matrix.of (fun a b : Fin n => MvPolynomial.eval w
          (MvPolynomial.pderiv a (MvPolynomial.pderiv b g.1)))).charpoly.roots.filter
            (fun r : ℝ => 0 < r)).card ≤ 1 := by
  intro g hg w hw
  exact (strict_hessian_nonsing_and_index n d hn hd).2 g hg w hw

end Commons.LorentzianPolynomials
