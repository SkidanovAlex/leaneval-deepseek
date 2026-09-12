import Mathlib
import Submission.Commons.LorentzianPolynomials.cubic_directional_deriv_stable

open Finsupp Matrix MvPolynomial UpperHalfPlane Topology Set
open scoped BigOperators

set_option autoImplicit false

namespace Commons.LorentzianPolynomials

/-- The degree-three base case of closure of `L` under nonnegative directional
derivatives: if `f` is a cubic in `L n 3`, then the nonnegative directional
derivative `Σⱼ uⱼ ∂ⱼ f` lies in `L n 2` (equivalently in the stable class `S n 2`). -/
theorem directional_deriv_three_mem_L (n : ℕ) (hn : 0 < n)
    (f : Commons.LorentzianPolynomials.H n 3) (hf : f ∈ Commons.LorentzianPolynomials.L n 3)
    (u : Fin n → ℝ) (hu : ∀ j : Fin n, 0 ≤ u j) :
    ∃ g : Commons.LorentzianPolynomials.H n 2,
      g ∈ Commons.LorentzianPolynomials.L n 2 ∧
        g.1 = ∑ j : Fin n, MvPolynomial.C (u j) * MvPolynomial.pderiv j f.1 := by
  exact cubic_directional_deriv_stable n hn f hf u hu

end Commons.LorentzianPolynomials
