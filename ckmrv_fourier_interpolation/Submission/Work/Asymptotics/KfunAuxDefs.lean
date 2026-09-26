/-
# Auxiliary definitions for the principal part of the kernel at the translate pole

This file introduces the *cleared value* function

  `AfunFun ℓ d τ z = (AfunPlus d z τ + AfunMinus ℓ d z τ)/2`

(the average of the two `Work.Residues.Afun*` functions, evaluated at the kernel variables
`(τ,z)`), together with the master identity

  `Kfun ℓ d τ z * (j τ - j z) = AfunFun ℓ d τ z`  (`j τ ≠ j z`)

and the derivative dictionary `deriv (j ∘ ofComplex) z = jprime z`.
-/
import Mathlib
import Submission.Work.Kernels.Kernels
import Submission.Work.Residues.ResidueKernel
import Submission.Work.Residues.ResidueTheoremMinus
import Submission.Work.Residues.normalizedDeriv_jInvariantFun

noncomputable section

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups ModularForm Modular Manifold Bundle

namespace Work.Asymptotics

open Work.Kernels Work.Residues

/-- The average of the two cleared kernels `AfunPlus`, `AfunMinus`, evaluated at the kernel
variables `(τ, z)`, i.e. `AfunFun ℓ d τ z = (AfunPlus d z τ + AfunMinus ℓ d z τ)/2`. -/
def AfunFun (ℓ : LogLambdaData) (d : ℕ) (τ z : ℍ) : ℂ :=
  (AfunPlus d z τ + AfunMinus ℓ d z τ) / 2

/-- The master identity: off the divisor, `K^{(d)}(τ,z)·(j τ - j z) = AfunFun τ z`. -/
lemma Kfun_mul_slope_eq_AfunFun (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (τ z : ℍ) (h : jInvariantFun τ ≠ jInvariantFun z) :
    Kfun ℓ d τ z * (jInvariantFun τ - jInvariantFun z) = AfunFun ℓ d τ z := by
  have h1 := mul_slope_eq_AfunPlus d hd z τ h
  have h2 := mul_slope_eq_AfunMinus ℓ d hd z τ h
  have hk : Kfun ℓ d τ z = (KPlus d τ z + KMinus ℓ d τ z) / 2 := rfl
  rw [hk, AfunFun]
  linear_combination (1/2) * h1 + (1/2) * h2

/-- The value identity at the pole `z₀ = τ - 1` (the `T⁻¹` translate). -/
lemma AfunFun_vadd_one (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) (z : ℍ) :
    AfunFun ℓ d ((1 : ℝ) +ᵥ z) z = -(1 / (2 * Real.pi)) * jprime z := by
  have h1 := AfunPlus_vadd_one_eq d hd z
  have h2 := AfunMinus_vadd_one_eq ℓ d hd z
  rw [AfunFun, h1, h2, jprime_vadd_one]
  ring

/-- The derivative of the lift of `j` is `jprime = -2πiE₄²E₆/Δ`. -/
lemma deriv_jInvariantFun_ofComplex (z : ℍ) :
    deriv (jInvariantFun ∘ UpperHalfPlane.ofComplex) (z : ℂ) = jprime z := by
  have h := Work.Residues.normalizedDeriv_jInvariantFun
  have h2 : deriv (jInvariantFun ∘ UpperHalfPlane.ofComplex) (z : ℂ)
      = (2 * (Real.pi : ℂ) * Complex.I) *
          Derivative.normalizedDerivOfComplex jInvariantFun z := by
    rw [Derivative.normalizedDerivOfComplex, mul_inv_cancel_left₀]
    exact mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
      Complex.I_ne_zero
  rw [h2, h]
  simp only [jprime]
  ring

end Work.Asymptotics
