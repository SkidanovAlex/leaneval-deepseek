import Mathlib
import Submission.Commons.LorentzianPolynomials.lp_density_asm

open Finsupp Matrix MvPolynomial UpperHalfPlane Topology Set

set_option autoImplicit false

namespace Commons.LorentzianPolynomials

/-- Interior density for the strictly Lorentzian polynomials (degree ≥ 3, n ≥ 2),
assembled from the Nuij-type smoothing `nuij_smoothing` by sending the smoothing
parameter to zero. -/
theorem lp_density_core (n d : ℕ) (hn2 : 2 ≤ n) (hd : 3 ≤ d) :
    (Commons.LorentzianPolynomials.L n d ∩ Commons.LorentzianPolynomials.P n d) ⊆
      closure (Commons.LorentzianPolynomials.Ŀ n d) := by
  exact lp_density_asm n d hn2 hd

end Commons.LorentzianPolynomials
