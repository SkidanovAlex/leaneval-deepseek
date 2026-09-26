import Mathlib
import Submission.Work.Asymptotics.KhatE1Core.KdevA4
import Submission.Work.Asymptotics.KhatE1Defs

/-!
# The `K₊`-half of the `E(z)^4` read-off

`3456π · tailC⁻¹ · Phi4 τ z` is the `K₊`-contribution to the `e⁴`-coefficient of the residual,
after the two substitutions `ψ₄ → Φ + P` and `j(τ)·Φ → E1combo8 - 1152E₄(τ) + 576ψ₄` (the
definition of `E1combo8`); `3456π·tailC⁻¹ = -96 i π³`.  The RHS below is engine-generated from the
same reduction that produced `Phi4` (`.kdevdir/a4leanA.txt`). -/

namespace Work.Asymptotics.KhatE1Core

open UpperHalfPlane

noncomputable section

open Work.Kernels

/-- `3456π · tailC⁻¹ = -96 i π³`. -/
theorem tailC_scalar : ((3456 : ℂ) * (Real.pi : ℂ)) * (Work.Asymptotics.Compact.tailC)⁻¹
    = -96 * Complex.I * (Real.pi : ℂ) ^ 3 := by
  rw [show Work.Asymptotics.Compact.tailC
      = 36 * (((Real.pi : ℂ)) ^ 2)⁻¹ * Complex.I by
    rw [Work.Asymptotics.Compact.tailC, show (-2 : ℤ) = -((2 : ℤ)) by norm_num, zpow_neg,
      zpow_ofNat]]
  have hpi : ((Real.pi : ℂ)) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hI : (Complex.I : ℂ) ≠ 0 := Complex.I_ne_zero
  field_simp
  rw [show (Complex.I : ℂ) ^ 2 = -1 from Complex.I_sq]
  ring

theorem Kplus4_eq (ℓ : Work.Kernels.LogLambdaData) (τ z : UpperHalfPlane)
    (hΔ : DeltaFun τ ≠ 0) (hE4 : E4Fun τ ≠ 0) :
    ((3456 : ℂ) * (Real.pi : ℂ)) * (Work.Asymptotics.Compact.tailC)⁻¹
        * Work.Asymptotics.KhatE1Core.Phi4 τ z
      =
    - (67392 : ℂ) * (-96 * Complex.I * (Real.pi : ℂ) ^ 3) * ((z : ℂ) * (z : ℂ) * E6Fun τ * (τ : ℂ))
    + (122256 : ℂ) * (-96 * Complex.I * (Real.pi : ℂ) ^ 3) * ((z : ℂ) * E6Fun τ * (6 * Complex.I / (Real.pi : ℂ)) * (τ : ℂ))
    + (834624 : ℂ) * (-96 * Complex.I * (Real.pi : ℂ) ^ 3) * ((z : ℂ) * (z : ℂ) * E4Fun τ * (τ : ℂ) * E2Fun τ)
    - (417312 : ℂ) * (-96 * Complex.I * (Real.pi : ℂ) ^ 3) * ((z : ℂ) * (z : ℂ) * E4Fun τ * (6 * Complex.I / (Real.pi : ℂ)))
    + (744 : ℂ) * (-96 * Complex.I * (Real.pi : ℂ) ^ 3) * ((z : ℂ) * (z : ℂ) * (E14Fun τ / DeltaFun τ) * (τ : ℂ) * E2Fun τ * E2Fun τ)
    - (744 : ℂ) * (-96 * Complex.I * (Real.pi : ℂ) ^ 3) * ((z : ℂ) * (z : ℂ) * (E14Fun τ / DeltaFun τ) * (6 * Complex.I / (Real.pi : ℂ)) * E2Fun τ)
    - (55440 : ℂ) * (-96 * Complex.I * (Real.pi : ℂ) ^ 3) * (E6Fun τ * (6 * Complex.I / (Real.pi : ℂ)) * (6 * Complex.I / (Real.pi : ℂ)) * (τ : ℂ))
    - (787536 : ℂ) * (-96 * Complex.I * (Real.pi : ℂ) ^ 3) * ((z : ℂ) * E4Fun τ * (6 * Complex.I / (Real.pi : ℂ)) * (τ : ℂ) * E2Fun τ)
    + (393768 : ℂ) * (-96 * Complex.I * (Real.pi : ℂ) ^ 3) * ((z : ℂ) * E4Fun τ * (6 * Complex.I / (Real.pi : ℂ)) * (6 * Complex.I / (Real.pi : ℂ)))
    - (1 : ℂ) * (-96 * Complex.I * (Real.pi : ℂ) ^ 3) * ((z : ℂ) * (z : ℂ) * jInvariantFun τ * (E14Fun τ / DeltaFun τ) * (τ : ℂ) * E2Fun τ * E2Fun τ)
    + (1 : ℂ) * (-96 * Complex.I * (Real.pi : ℂ) ^ 3) * ((z : ℂ) * (z : ℂ) * jInvariantFun τ * (E14Fun τ / DeltaFun τ) * (6 * Complex.I / (Real.pi : ℂ)) * E2Fun τ)
    + (1032 : ℂ) * (-96 * Complex.I * (Real.pi : ℂ) ^ 3) * ((z : ℂ) * (z : ℂ) * E6Fun τ * jInvariantFun τ * (τ : ℂ))
    - (2016 : ℂ) * (-96 * Complex.I * (Real.pi : ℂ) ^ 3) * ((z : ℂ) * E6Fun τ * jInvariantFun τ * (6 * Complex.I / (Real.pi : ℂ)) * (τ : ℂ))
    + (984 : ℂ) * (-96 * Complex.I * (Real.pi : ℂ) ^ 3) * (E6Fun τ * jInvariantFun τ * (6 * Complex.I / (Real.pi : ℂ)) * (6 * Complex.I / (Real.pi : ℂ)) * (τ : ℂ))
    - (3504 : ℂ) * (-96 * Complex.I * (Real.pi : ℂ) ^ 3) * ((z : ℂ) * (z : ℂ) * E4Fun τ * jInvariantFun τ * (τ : ℂ) * E2Fun τ)
    + (3456 : ℂ) * (-96 * Complex.I * (Real.pi : ℂ) ^ 3) * ((z : ℂ) * E4Fun τ * jInvariantFun τ * (6 * Complex.I / (Real.pi : ℂ)) * (τ : ℂ) * E2Fun τ)
    + (1752 : ℂ) * (-96 * Complex.I * (Real.pi : ℂ) ^ 3) * ((z : ℂ) * (z : ℂ) * E4Fun τ * jInvariantFun τ * (6 * Complex.I / (Real.pi : ℂ)))
    - (1728 : ℂ) * (-96 * Complex.I * (Real.pi : ℂ) ^ 3) * ((z : ℂ) * E4Fun τ * jInvariantFun τ * (6 * Complex.I / (Real.pi : ℂ)) * (6 * Complex.I / (Real.pi : ℂ)))
    - (1 : ℂ) * (-96 * Complex.I * (Real.pi : ℂ) ^ 3) * ((z : ℂ) * (z : ℂ) * E6Fun τ * jInvariantFun τ * jInvariantFun τ * (τ : ℂ))
    + (2 : ℂ) * (-96 * Complex.I * (Real.pi : ℂ) ^ 3) * ((z : ℂ) * E6Fun τ * jInvariantFun τ * jInvariantFun τ * (6 * Complex.I / (Real.pi : ℂ)) * (τ : ℂ))
    - (1 : ℂ) * (-96 * Complex.I * (Real.pi : ℂ) ^ 3) * (E6Fun τ * jInvariantFun τ * jInvariantFun τ * (6 * Complex.I / (Real.pi : ℂ)) * (6 * Complex.I / (Real.pi : ℂ)) * (τ : ℂ))
    + (2 : ℂ) * (-96 * Complex.I * (Real.pi : ℂ) ^ 3) * ((z : ℂ) * (z : ℂ) * E4Fun τ * jInvariantFun τ * jInvariantFun τ * (τ : ℂ) * E2Fun τ)
    - (2 : ℂ) * (-96 * Complex.I * (Real.pi : ℂ) ^ 3) * ((z : ℂ) * E4Fun τ * jInvariantFun τ * jInvariantFun τ * (6 * Complex.I / (Real.pi : ℂ)) * (τ : ℂ) * E2Fun τ)
    - (1 : ℂ) * (-96 * Complex.I * (Real.pi : ℂ) ^ 3) * ((z : ℂ) * (z : ℂ) * E4Fun τ * jInvariantFun τ * jInvariantFun τ * (6 * Complex.I / (Real.pi : ℂ)))
    + (1 : ℂ) * (-96 * Complex.I * (Real.pi : ℂ) ^ 3) * ((z : ℂ) * E4Fun τ * jInvariantFun τ * jInvariantFun τ * (6 * Complex.I / (Real.pi : ℂ)) * (6 * Complex.I / (Real.pi : ℂ))) := by
  rw [Work.Asymptotics.KhatE1Core.tailC_scalar, Work.Asymptotics.KhatE1Core.Phi4]
  ring

end

end Work.Asymptotics.KhatE1Core
