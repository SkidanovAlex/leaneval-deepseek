import Mathlib
import Submission.Commons.LorentzianPolynomials.strict_subset_L
import Submission.Commons.Combinatorics.MvPolynomial.interval_convex_of_rayleigh

namespace Commons.LorentzianPolynomials

open Finsupp Matrix MvPolynomial
open Commons.Combinatorics.MvPolynomial

set_option autoImplicit false
set_option linter.unusedVariables false

/-- Peeling off one partial derivative from a member of `L n d` of degree at least `3`
produces a member of the next lower `L`: this is exactly the recursive clause in the
definition of `L`. -/
private lemma deriv_mem_L {n d : ℕ} (hd : 3 ≤ d) (i : Fin n) (f : H n d) (hf : f ∈ L n d) :
    (⟨f.1.pderiv i, f.2.pderiv⟩ : H n (d - 1)) ∈ L n (d - 1) := by
  cases d with
  | zero => omega
  | succ d0 =>
      cases d0 with
      | zero => omega
      | succ d1 =>
          cases d1 with
          | zero => omega
          | succ d2 =>
              simp [L] at hf
              exact hf.2 i

/-- Iterated partial derivatives of a member of `L n d`, along any list of at most
`d - 2` indices, stay in the appropriate lower `L`. -/
theorem partials_mem_L {n d : ℕ} (hd : 2 ≤ d) (l : List (Fin n)) (hl : l.length ≤ d - 2)
    (f : Commons.LorentzianPolynomials.H n d)
    (hf : f ∈ Commons.LorentzianPolynomials.L n d) :
    ∃ u : Commons.LorentzianPolynomials.H n (d - l.length),
      u ∈ Commons.LorentzianPolynomials.L n (d - l.length) ∧
        u.1 = Commons.Combinatorics.MvPolynomial.pderivL l f.1 := by
  induction l generalizing d with
  | nil =>
      have hdeg : d - ([] : List (Fin n)).length = d := by simp
      rw [hdeg]
      refine ⟨f, hf, ?_⟩
      rfl
  | cons i l' ih =>
      have hlen : (i :: l').length = l'.length + 1 := by simp
      have hl1 : l'.length + 1 ≤ d - 2 := by simpa [hlen] using hl
      have hd3 : 3 ≤ d := by omega
      have hl2 : l'.length ≤ (d - 1) - 2 := by omega
      have hd2 : 2 ≤ d - 1 := by omega
      let g : H n (d - 1) := ⟨f.1.pderiv i, f.2.pderiv⟩
      have hg : g ∈ L n (d - 1) := deriv_mem_L hd3 i f hf
      have hdeg : (d - 1) - l'.length = d - (i :: l').length := by
        rw [hlen]
        omega
      rw [← hdeg]
      rcases ih (d := d - 1) hd2 hl2 g hg with ⟨v, hv, hv_eq⟩
      refine ⟨v, hv, ?_⟩
      rw [pderivL_cons]
      simpa [g] using hv_eq

end Commons.LorentzianPolynomials
