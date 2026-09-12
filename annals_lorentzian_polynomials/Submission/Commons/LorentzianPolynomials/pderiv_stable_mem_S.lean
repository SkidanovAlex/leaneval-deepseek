import Mathlib
import Submission.Commons.LorentzianPolynomials.S_closed
import Submission.Commons.LorentzianPolynomials.hessian_aeval_eq
import Submission.Commons.LorentzianPolynomials.strict_lorentzian_quadratic_stable
import Submission.Commons.Analysis.MvPolynomial.pderiv_stable

open Finsupp Matrix MvPolynomial UpperHalfPlane Topology Set

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Commons.LorentzianPolynomials

/-- Partial derivatives preserve the set `S n d` of degree-`d` homogeneous stable
polynomials with nonnegative coefficients: if `f ∈ S n d` with `1 ≤ d`, then
`∂ᵢf ∈ S n (d - 1)` for every index `i`.  Stability of the derivative is the
multivariate Gauss--Lucas statement `Commons.Analysis.MvPolynomial.pderiv_stable`;
nonnegativity of the coefficients follows from the explicit coefficient formula
`MvPolynomial.coeff_pderiv`. -/
theorem pderiv_stable_mem_S {n d : ℕ} (hd : 1 ≤ d)
    (f : H n d) (hf : f ∈ S n d) (i : Fin n) :
    ⟨f.1.pderiv i, f.2.pderiv⟩ ∈ S n (d - 1) := by
  rcases hf with ⟨hstab, hnonneg⟩
  change IsStable (f.1.pderiv i) ∧ ∀ m : Fin n →₀ ℕ, 0 ≤ (f.1.pderiv i).coeff m
  constructor
  · change (f.1.pderiv i = 0 ∨ ∀ z : Fin n → UpperHalfPlane,
        MvPolynomial.aeval (R := ℝ) (fun j : Fin n => ((z j : UpperHalfPlane) : ℂ))
          (f.1.pderiv i) ≠ 0)
    exact Commons.Analysis.MvPolynomial.pderiv_stable f.1 i (by
      change (f.1 = 0 ∨ ∀ z : Fin n → UpperHalfPlane,
        MvPolynomial.aeval (R := ℝ) (fun j : Fin n => ((z j : UpperHalfPlane) : ℂ)) f.1 ≠ 0)
      exact hstab)
  · intro m
    rw [MvPolynomial.coeff_pderiv]
    exact mul_nonneg (hnonneg (m + Finsupp.single i 1)) (by positivity)

end Commons.LorentzianPolynomials
