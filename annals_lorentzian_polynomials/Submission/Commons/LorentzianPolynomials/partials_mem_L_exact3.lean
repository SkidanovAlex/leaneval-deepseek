import Mathlib
import Submission.Commons.LorentzianPolynomials.partials_mem_L

namespace Commons.LorentzianPolynomials

open Finsupp Matrix MvPolynomial
open Commons.Combinatorics.MvPolynomial

set_option autoImplicit false

/-- Exact-length version of `partials_mem_L` for the degree-three target: if
`f ∈ L n d` with `d ≥ 3` and `l` has exactly `d - 3` elements then the iterated
partial `pderivL l f.1` is the polynomial part of an element of `L n 3`. -/
theorem partials_mem_L_exact3 {n d : ℕ} (hd : 3 ≤ d) (l : List (Fin n))
    (hl : l.length = d - 3) (f : Commons.LorentzianPolynomials.H n d)
    (hf : f ∈ Commons.LorentzianPolynomials.L n d) :
    ∃ u : Commons.LorentzianPolynomials.H n 3,
      u ∈ Commons.LorentzianPolynomials.L n 3 ∧
        u.1 = Commons.Combinatorics.MvPolynomial.pderivL l f.1 := by
  have hd2 : 2 ≤ d := by omega
  have hle : l.length ≤ d - 2 := by omega
  have hdeg : 3 = d - l.length := by omega
  rw [hdeg]
  exact partials_mem_L hd2 l hle f hf

end Commons.LorentzianPolynomials
