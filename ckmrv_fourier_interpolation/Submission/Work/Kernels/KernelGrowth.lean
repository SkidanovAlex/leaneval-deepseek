/-
# Theorem 4.9(4): growth of the kernels with the poles cleared

CKMRV Theorem 4.9(4) asserts that `Δ(τ)Δ(z)(j(τ)−j(z))K^{(8)}_±(τ,z)` and
`Δ(τ)Δ(z)²(j(τ)−j(z))K^{(24)}_±(τ,z)` lie in the class `𝒫`, in each variable.

The kernels `K_±` have simple poles exactly where `j(τ) = j(z)`, so the *product* form is not
holomorphic under Lean's convention `0⁻¹ = 0`: at `j(τ) = j(z)` the product evaluates to `0`
while its limit is generically non-zero.  The mathematically correct formulation is therefore
the one used here: the paper's products are computed *explicitly*, with the factor
`j(τ)−j(z)` multiplied into the numerators (`Work.Kernels.UpsilonPlusClear`,
`Work.Kernels.UpsilonMinusClear`), giving the holomorphic kernels
`Work.Kernels.KPlusClear` and `Work.Kernels.KMinusClear`.

## Main results

* `Work.Kernels.KernelGrowth.KPlusClear_growth_tau`, `KPlusClear_growth_z`,
  `KMinusClear_growth_tau`, `KMinusClear_growth_z` : the four halves of Theorem 4.9(4).
* `Work.Kernels.KernelClear_growth_tau`, `KernelClear_growth_z` : the same for
  `K = (K_+ + K_-)/2` and `K̂ = (K_+ − K_-)/2`.
-/
import Mathlib
import Submission.Work.Kernels.Kernels
import Submission.Work.Kernels.KernelGrowth.KPlusClear_growth_tau
import Submission.Work.Kernels.KernelGrowth.KPlusClear_growth_z
import Submission.Work.Kernels.KernelGrowth.KMinusClear_growth_tau
import Submission.Work.Kernels.KernelGrowth.KMinusClear_growth_z

noncomputable section

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups ModularForm Modular Manifold Bundle

namespace Work.Kernels

/-- `K` with the poles cleared, `Δ(τ)Δ(z)^e(j(τ)−j(z))K^{(d)}(τ,z)`. -/
def KfunClear (ℓ : LogLambdaData) (d : ℕ) (τ z : ℍ) : ℂ :=
  (KPlusClear d τ z + KMinusClear ℓ d τ z) / 2

/-- `K̂` with the poles cleared, `Δ(τ)Δ(z)^e(j(τ)−j(z))K̂^{(d)}(τ,z)`. -/
def KhatClear (ℓ : LogLambdaData) (d : ℕ) (τ z : ℍ) : ℂ :=
  (KPlusClear d τ z - KMinusClear ℓ d τ z) / 2

/-- Theorem 4.9(4) for `K` and `K̂` in the `τ` variable. -/
theorem KernelClear_growth_tau (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) (z : ℍ) :
    InP (fun τ : ℍ => KfunClear ℓ d τ z) ∧ InP (fun τ : ℍ => KhatClear ℓ d τ z) := by
  have h1 := KernelGrowth.KPlusClear_growth_tau d hd z
  have h2 := KernelGrowth.KMinusClear_growth_tau ℓ d hd z
  refine ⟨?_, ?_⟩
  · have h3 : (fun τ : ℍ => KfunClear ℓ d τ z)
        = fun τ => (2 : ℂ)⁻¹ • KPlusClear d τ z + (2 : ℂ)⁻¹ • KMinusClear ℓ d τ z := by
      funext τ; simp [KfunClear]; ring
    rw [h3]
    exact (h1.const_mul _).add (h2.const_mul _)
  · have h3 : (fun τ : ℍ => KhatClear ℓ d τ z)
        = fun τ => (2 : ℂ)⁻¹ • KPlusClear d τ z + (-(2 : ℂ)⁻¹) • KMinusClear ℓ d τ z := by
      funext τ; simp [KhatClear]; ring
    rw [h3]
    exact (h1.const_mul _).add (h2.const_mul _)

/-- Theorem 4.9(4) for `K` and `K̂` in the `z` variable. -/
theorem KernelClear_growth_z (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) (τ : ℍ) :
    InP (fun z : ℍ => KfunClear ℓ d τ z) ∧ InP (fun z : ℍ => KhatClear ℓ d τ z) := by
  have h1 := KernelGrowth.KPlusClear_growth_z d hd τ
  have h2 := KernelGrowth.KMinusClear_growth_z ℓ d hd τ
  refine ⟨?_, ?_⟩
  · have h3 : (fun z : ℍ => KfunClear ℓ d τ z)
        = fun z => (2 : ℂ)⁻¹ • KPlusClear d τ z + (2 : ℂ)⁻¹ • KMinusClear ℓ d τ z := by
      funext z; simp [KfunClear]; ring
    rw [h3]
    exact (h1.const_mul _).add (h2.const_mul _)
  · have h3 : (fun z : ℍ => KhatClear ℓ d τ z)
        = fun z => (2 : ℂ)⁻¹ • KPlusClear d τ z + (-(2 : ℂ)⁻¹) • KMinusClear ℓ d τ z := by
      funext z; simp [KhatClear]; ring
    rw [h3]
    exact (h1.const_mul _).add (h2.const_mul _)

end Work.Kernels
