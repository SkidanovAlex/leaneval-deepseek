import Mathlib
import Submission.Work.Asymptotics.funnelTailBasic
import Submission.Work.Asymptotics.KPlusXiDefs
import Submission.Work.Asymptotics.Compact.kminus_tail_core

/-!
# The `E(z)⁰`-coefficient `B0` of the funnel bracket and its cleared form

`B0 ℓ τ = -iτ·E₆(τ)·(j(τ)-240) + (3456π)⁻¹·(cuspC·R8_q1 ℓ τ + R8_p1 ℓ τ)` is the
`z⁰`-coefficient of `Kdev8BracketE2` (the `E(z)²`-coefficient of the funnel bracket
`Kdev8Bracket = 2·KdevRem`).

Clearing the denominators `Δτ·j(τ) = E₄(τ)³` gives the *analytic* form used for the
estimate: `Δ·B0 = NONPSI + (3456π)⁻¹·Ψ` with

* `NONPSI = -iτE₆E₄³ + 240iτΔE₆ + (3456π)⁻¹cuspC(3400704E₄Δ - 3456E₄⁴) - (3456π)⁻¹41472E₄Δ`,
* `Ψ = 1152ψ₂E₁₄ + 576E₄³ψ₄ - 373248Δψ₄`.
-/

namespace Work.Asymptotics.KhatE1

open UpperHalfPlane

noncomputable section

/-- `Λ₀ τ = πiτ + cuspC ℓ`. -/
def Lam0 (ℓ : Work.Kernels.LogLambdaData) (τ : ℍ) : ℂ :=
  (Real.pi : ℂ) * Complex.I * (τ : ℂ) + Work.Asymptotics.Compact.cuspC ℓ

/-- The `E(z)⁰`-coefficient of the funnel bracket. -/
def B0 (ℓ : Work.Kernels.LogLambdaData) (τ : ℍ) : ℂ :=
  -Complex.I * (τ : ℂ) * Work.Kernels.E6Fun τ * (Work.Kernels.jInvariantFun τ - 240)
    + ((3456 : ℂ) * (Real.pi : ℂ))⁻¹ *
        (Work.Asymptotics.Compact.cuspC ℓ * Work.Asymptotics.Compact.R8_q1 ℓ τ
          + Work.Asymptotics.Compact.R8_p1 ℓ τ)

/-- **The cleared form of `Δ·B0`.** -/
theorem Delta_mul_B0 (ℓ : Work.Kernels.LogLambdaData) (τ : ℍ) :
    Work.Kernels.DeltaFun τ * B0 ℓ τ
      = - Complex.I * (τ : ℂ) * Work.Kernels.E6Fun τ * (Work.Kernels.E4Fun τ) ^ 3
        + 240 * Complex.I * (τ : ℂ) * Work.Kernels.DeltaFun τ * Work.Kernels.E6Fun τ
        + ((3456 : ℂ) * (Real.pi : ℂ))⁻¹ * Work.Asymptotics.Compact.cuspC ℓ
            * (3400704 * Work.Kernels.E4Fun τ * Work.Kernels.DeltaFun τ
                - 3456 * (Work.Kernels.E4Fun τ) ^ 4)
        - ((3456 : ℂ) * (Real.pi : ℂ))⁻¹ * 41472 * Work.Kernels.E4Fun τ
            * Work.Kernels.DeltaFun τ
        + ((3456 : ℂ) * (Real.pi : ℂ))⁻¹ *
            (1152 * (Work.Kernels.psi2 ℓ τ * Work.Kernels.E14Fun τ)
              + 576 * (Work.Kernels.E4Fun τ) ^ 3 * Work.Kernels.psi4 ℓ τ
              - 373248 * Work.Kernels.DeltaFun τ * Work.Kernels.psi4 ℓ τ) := by
  have hD : Work.Kernels.DeltaFun τ ≠ 0 := Work.Kernels.ClassicalFacts.DeltaFun_ne_zero τ
  have hj : Work.Kernels.DeltaFun τ * Work.Kernels.jInvariantFun τ
      = (Work.Kernels.E4Fun τ) ^ 3 :=
    Work.Kernels.ClassicalFacts.DeltaFun_mul_jInvariantFun τ
  rw [B0, Work.Asymptotics.Compact.R8_q1, Work.Asymptotics.Compact.R8_p1]
  rw [mul_add, mul_add, mul_add]
  field_simp
  ring

end

end Work.Asymptotics.KhatE1
