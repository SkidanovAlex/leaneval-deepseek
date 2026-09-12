import Mathlib
import Submission.Commons.LorentzianPolynomials.partials_mem_L

namespace Commons.LorentzianPolynomials

open Finsupp Matrix MvPolynomial
open Commons.Combinatorics.MvPolynomial

set_option autoImplicit false
set_option linter.unusedVariables false

/-- Exact-length version of `partials_mem_L` for the degree-two target: if
`f ∈ L n d` and `l` has exactly `d - 2` elements then the iterated partial
`pderivL l f.1` is the polynomial part of an element of `S n 2` (= `L n 2`). -/
theorem partials_mem_L_exact2 {n d : ℕ} (hd : 2 ≤ d) (l : List (Fin n))
    (hl : l.length = d - 2) (f : Commons.LorentzianPolynomials.H n d)
    (hf : f ∈ Commons.LorentzianPolynomials.L n d) :
    ∃ u : Commons.LorentzianPolynomials.H n 2,
      u ∈ Commons.LorentzianPolynomials.S n 2 ∧
        u.1 = Commons.Combinatorics.MvPolynomial.pderivL l f.1 := by
  classical
  induction l generalizing d with
  | nil =>
      simp at hl
      have hd2 : d = 2 := by omega
      subst d
      refine ⟨f, ?_, ?_⟩
      · simpa [L] using hf
      · simp
  | cons i l' ih =>
      have hlen : l'.length + 1 = d - 2 := by simpa using hl
      have hle1 : ([i] : List (Fin n)).length ≤ d - 2 := by simp; omega
      rcases partials_mem_L (n := n) (d := d) hd [i] hle1 f hf with ⟨u, hu, hu_eq⟩
      have hu' : u.1 = pderiv i f.1 := by
        rw [hu_eq]
        simp [pderivL_cons]
      have hd' : 2 ≤ d - 1 := by omega
      have hl' : l'.length = (d - 1) - 2 := by omega
      rcases ih (d := d - 1) hd' hl' u hu with ⟨v, hv, hv_eq⟩
      refine ⟨v, hv, ?_⟩
      calc
        v.1 = pderivL l' u.1 := hv_eq
        _ = pderivL l' (pderiv i f.1) := by rw [hu']
        _ = pderivL (i :: l') f.1 := by rw [pderivL_cons]

end Commons.LorentzianPolynomials
