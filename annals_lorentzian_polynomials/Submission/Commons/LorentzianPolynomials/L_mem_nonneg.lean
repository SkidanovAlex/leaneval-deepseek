import Mathlib
import Submission.Commons.LorentzianPolynomials.hessian_aeval_eq
import Submission.Commons.LorentzianPolynomials.strict_lorentzian_quadratic_stable
import Submission.Commons.LorentzianPolynomials.S_closed
import Submission.Commons.LorentzianPolynomials.strict_subset_L

namespace Commons.LorentzianPolynomials

theorem L_mem_nonneg (n d : ℕ) (f : Commons.LorentzianPolynomials.H n d)
    (hf : f ∈ Commons.LorentzianPolynomials.L n d) :
    ∀ m : Fin n →₀ ℕ, 0 ≤ f.1.coeff m := by
  cases d with
  | zero =>
      have hS : f ∈ Commons.LorentzianPolynomials.S n 0 := by
        simpa [L] using hf
      exact hS.2
  | succ d0 =>
      cases d0 with
      | zero =>
          have hS : f ∈ Commons.LorentzianPolynomials.S n 1 := by
            simpa [L] using hf
          exact hS.2
      | succ d1 =>
          cases d1 with
          | zero =>
              have hS : f ∈ Commons.LorentzianPolynomials.S n 2 := by
                simpa [L] using hf
              exact hS.2
          | succ k =>
              have hM := hf.1
              simpa [M] using hM.2

end Commons.LorentzianPolynomials
