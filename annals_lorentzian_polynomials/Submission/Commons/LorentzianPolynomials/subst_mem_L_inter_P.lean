import Mathlib
import Submission.Commons.LorentzianPolynomials.hessian_aeval_eq
import Submission.Commons.LorentzianPolynomials.strict_lorentzian_quadratic_stable
import Submission.Commons.LorentzianPolynomials.S_closed
import Submission.Commons.LorentzianPolynomials.strict_subset_L
import Submission.Commons.LorentzianPolynomials.closure_strict_eq_L_of_degree_le_two
import Submission.Commons.LorentzianPolynomials.L_mem_nonneg
import Submission.Commons.Algebra.MvPolynomial.subst_coeff_pos
import Submission.Commons.LorentzianPolynomials.substS_flow_mem_L

open Finsupp Matrix MvPolynomial UpperHalfPlane Topology Set
open scoped BigOperators

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Commons.LorentzianPolynomials

noncomputable section

/-- Substituting `X ⱼ ↦ (1−θ)·X ⱼ + θ·(Σᵢ Xᵢ)` maps a nonzero `f ∈ L n d` into `P n d`
whenever `0 < θ ≤ 1`: every monomial of degree `d` receives a strictly positive coefficient. -/
private lemma substS_mem_P_of_mem_L {n d : ℕ} (f : H n d) (hf : f ∈ L n d)
    (hf0 : f ≠ 0) {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) :
    substS (n := n) (d := d) θ f ∈ P n d := by
  intro m hm
  change 0 < (MvPolynomial.aeval (fun j : Fin n =>
      MvPolynomial.C (1 - θ) * MvPolynomial.X j +
        MvPolynomial.C θ * (∑ i : Fin n, MvPolynomial.X i)) f.1).coeff m
  exact Commons.Algebra.MvPolynomial.subst_coeff_pos n d f.1
    (L_mem_nonneg n d f hf) (by
      intro hz
      apply hf0
      apply Subtype.ext
      exact hz) f.2 hθ0 hθ1 m hm

/-- For `f ∈ L n d` and `0 < θ ≤ 1`, the substituted polynomial
`g = f((1−θ)·X + θ·(Σᵢ Xᵢ))` belongs to `L n d ∩ P n d`; it realises the same underlying
polynomial as the substitution. -/
theorem subst_mem_L_inter_P (n d : ℕ) (hn : 0 < n)
    (f : Commons.LorentzianPolynomials.H n d)
    (hf : f ∈ Commons.LorentzianPolynomials.L n d) (hf0 : f ≠ 0)
    {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) :
    ∃ g : Commons.LorentzianPolynomials.H n d,
      g ∈ Commons.LorentzianPolynomials.L n d ∧
        g ∈ Commons.LorentzianPolynomials.P n d ∧
          g.1 = MvPolynomial.aeval (fun j : Fin n =>
            MvPolynomial.C (1 - θ) * MvPolynomial.X j +
              MvPolynomial.C θ * (∑ i : Fin n, MvPolynomial.X i)) f.1 := by
  refine ⟨substS (n := n) (d := d) θ f, ?_, ?_, ?_⟩
  · exact substS_flow_mem_L n d hn f hf θ (le_of_lt hθ0) hθ1
  · exact substS_mem_P_of_mem_L f hf hf0 hθ0 hθ1
  · rfl

end

end Commons.LorentzianPolynomials
