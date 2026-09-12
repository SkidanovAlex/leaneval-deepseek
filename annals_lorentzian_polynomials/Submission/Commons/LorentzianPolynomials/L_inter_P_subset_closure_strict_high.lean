import Mathlib
import Submission.Commons.LorentzianPolynomials.lp_density_core

namespace Commons.LorentzianPolynomials

open Finsupp Matrix MvPolynomial UpperHalfPlane Topology Set

set_option autoImplicit false

theorem L_inter_P_subset_closure_strict_high (n d : ℕ) (hn2 : 2 ≤ n) (hd : 3 ≤ d) :
    (Commons.LorentzianPolynomials.L n d ∩ Commons.LorentzianPolynomials.P n d) ⊆
      closure (Commons.LorentzianPolynomials.Ŀ n d) := by
  exact lp_density_core n d hn2 hd

end Commons.LorentzianPolynomials
