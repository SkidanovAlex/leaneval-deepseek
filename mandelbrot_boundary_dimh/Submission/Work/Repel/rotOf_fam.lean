import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Repel.Basic

namespace Work.Repel

open MandelDim Complex Set Metric Filter Topology
open LeanEval.Dynamics.MandelbrotBoundary

/-- The derivative of `fam α` at its fixed point `0` is the multiplier `lam α`. -/
lemma deriv_fam (α : ℂ) : deriv (fam α) 0 = lam α := by
  have h1 : HasDerivAt (fun x : ℂ => lam α * x) (lam α) 0 := by
    simpa using (hasDerivAt_id (0 : ℂ)).const_mul (lam α)
  have h2 : HasDerivAt (fun x : ℂ => x ^ 2) 0 0 := by
    simpa using hasDerivAt_pow 2 (0 : ℂ)
  have h : deriv ((fun x : ℂ => lam α * x) + (fun x : ℂ => x ^ 2)) 0 = lam α := by
    simpa using (h1.add h2).deriv
  change deriv ((fun x : ℂ => lam α * x) + (fun x : ℂ => x ^ 2)) 0 = lam α
  exact h

/-- `lam α = exp (2πi α)` lies in the principal branch range of `log`
whenever `-1/2 < Re α ≤ 1/2`. -/
lemma log_lam (α : ℂ) (h₁ : -(1 / 2) < α.re) (h₂ : α.re ≤ 1 / 2) :
    Complex.log (lam α) = 2 * Real.pi * I * α := by
  unfold lam
  apply Complex.log_exp
  · rw [show (2 * Real.pi * I * α).im = 2 * Real.pi * α.re by
      simp [Complex.mul_im, Complex.mul_re]]
    nlinarith [Real.pi_pos]
  · rw [show (2 * Real.pi * I * α).im = 2 * Real.pi * α.re by
      simp [Complex.mul_im, Complex.mul_re]]
    nlinarith [Real.pi_pos]

theorem rotOf_fam (α : ℂ) (h₁ : -(1 / 2) < α.re) (h₂ : α.re ≤ 1 / 2) :
    rotOf (Work.Repel.fam α) = α := by
  rw [rotOf, deriv_fam, log_lam α h₁ h₂]
  field_simp

end Work.Repel
