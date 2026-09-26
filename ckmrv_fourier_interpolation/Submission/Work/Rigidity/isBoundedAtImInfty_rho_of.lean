import Mathlib
import Submission.Work.Rigidity.LambdaDerivDefs
import Submission.Work.Rigidity.lamC_add_one

namespace Work.Rigidity

open Work.Kernels Work.Kernels.LogLambda
open scoped UpperHalfPlane

/-- Pointwise `ρ = (λ'/λ) · (θ₀₁)⁻⁴`.  The quartic identity `θ₀₀⁴ = θ₀₁⁴ + θ₁₀⁴` turns the
factor `1 - λ = λ_S` into `θ₀₁⁴/θ₀₀⁴`, so that the denominator
`λ (1 - λ) θ₀₀⁴` of `ρC` collapses to `λ θ₀₁⁴`. -/
lemma rho_eq_mul (τ : ℍ) :
    rho τ = (deriv lamC (τ : ℂ) / lamC (τ : ℂ)) * ((theta01Fun τ) ^ 4)⁻¹ := by
  have hz : 0 < (τ : ℂ).im := τ.im_pos
  have hsc : theta01Fun τ ^ 4 / theta00Fun τ ^ 4 = 1 - lamC (τ : ℂ) := by
    have h := lamSC_eq_one_sub_lamC (τ : ℂ) hz
    simpa only [lamSC, thetaC01, thetaC00, theta01Fun, theta00Fun] using h
  have h00 : theta00Fun τ ^ 4 ≠ 0 := pow_ne_zero 4 (theta00Fun_ne_zero τ)
  have hkey : lamC (τ : ℂ) * (1 - lamC (τ : ℂ)) * theta00Fun τ ^ 4
      = lamC (τ : ℂ) * theta01Fun τ ^ 4 := by
    rw [← hsc, mul_assoc, div_mul_cancel₀ _ h00]
  show deriv lamC (τ : ℂ) / (lamC (τ : ℂ) * (1 - lamC (τ : ℂ)) * theta00Fun τ ^ 4)
      = deriv lamC (τ : ℂ) / lamC (τ : ℂ) * (theta01Fun τ ^ 4)⁻¹
  rw [hkey, div_eq_mul_inv, mul_inv_rev, div_eq_mul_inv]
  ring

theorem isBoundedAtImInfty_rho_of
    (hb : UpperHalfPlane.IsBoundedAtImInfty (fun τ : UpperHalfPlane =>
      deriv Work.Kernels.LogLambda.lamC (τ : ℂ) / Work.Kernels.LogLambda.lamC (τ : ℂ)))
    (hc : UpperHalfPlane.IsBoundedAtImInfty (fun τ : UpperHalfPlane =>
      ((Work.Kernels.theta01Fun τ) ^ 4)⁻¹)) :
    UpperHalfPlane.IsBoundedAtImInfty Work.Rigidity.rho := by
  have hrhs : Work.Rigidity.rho
      = (fun τ : ℍ => deriv lamC (τ : ℂ) / lamC (τ : ℂ))
        * (fun τ : ℍ => ((theta01Fun τ) ^ 4)⁻¹) := by
    funext τ
    exact rho_eq_mul τ
  rw [hrhs]
  exact hb.mul hc

end Work.Rigidity
