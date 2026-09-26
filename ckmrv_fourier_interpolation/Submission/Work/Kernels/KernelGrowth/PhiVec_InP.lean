import Mathlib
import Submission.Work.Kernels.Kernels
import Submission.Work.Kernels.ClassicalFacts.E2Fun_mem_InP

namespace Work.Kernels.KernelGrowth

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups ModularForm Modular Manifold Bundle

/-- The coordinate function `τ ↦ (τ : ℂ)` lies in `𝒫`: it is holomorphic and
`‖τ‖ ≤ 1 · ((im τ)⁻¹ + ‖τ‖)`. -/
lemma InP_coe : Work.Kernels.InP (fun τ : UpperHalfPlane => (τ : ℂ)) := by
  refine ⟨UpperHalfPlane.mdifferentiable_coe, ?_⟩
  refine ⟨1, 1, 1, by norm_num, by norm_num, by norm_num, fun τ _ => ?_⟩
  simp only [Real.rpow_one, one_mul]
  have h : 0 ≤ (τ.im)⁻¹ := inv_nonneg.mpr τ.im_pos.le
  linarith [norm_nonneg (τ : ℂ)]

/-- `φ_{-2}(τ) = τ` lies in `𝒫`. -/
lemma phiNeg2_InP : Work.Kernels.InP Work.Kernels.phiNeg2 := by
  change Work.Kernels.InP (fun τ : UpperHalfPlane => (τ : ℂ))
  exact InP_coe

/-- `φ_0(τ) = τE₂(τ) - 3i/π` lies in `𝒫`. -/
lemma phi0_InP : Work.Kernels.InP Work.Kernels.phi0 := by
  change Work.Kernels.InP (fun τ : UpperHalfPlane =>
    (τ : ℂ) * Work.Kernels.E2Fun τ - 3 * Complex.I / (Real.pi : ℂ))
  exact (InP_coe.mul Work.Kernels.ClassicalFacts.E2Fun_mem_InP).sub
    (Work.Kernels.InP.const (3 * Complex.I / (Real.pi : ℂ)))

/-- `φ_2(τ) = τE₂(τ)² - (6i/π)E₂(τ)` lies in `𝒫`. -/
lemma phi2_InP : Work.Kernels.InP Work.Kernels.phi2 := by
  change Work.Kernels.InP (fun τ : UpperHalfPlane =>
    (τ : ℂ) * Work.Kernels.E2Fun τ ^ 2 - (6 * Complex.I / (Real.pi : ℂ)) * Work.Kernels.E2Fun τ)
  exact (InP_coe.mul (Work.Kernels.ClassicalFacts.E2Fun_mem_InP.pow 2)).sub
    (Work.Kernels.InP.const_mul (6 * Complex.I / (Real.pi : ℂ))
      Work.Kernels.ClassicalFacts.E2Fun_mem_InP)

/-- Each coordinate of the basis vector `φ⃗ = (φ_{-2}, φ_0, φ_2)` of Proposition 4.2
lies in the class `𝒫`. -/
theorem PhiVec_InP (i : Fin 3) :
    Work.Kernels.InP (fun τ : UpperHalfPlane => Work.Kernels.phiVec τ i) := by
  fin_cases i
  · change Work.Kernels.InP Work.Kernels.phiNeg2
    exact phiNeg2_InP
  · change Work.Kernels.InP Work.Kernels.phi0
    exact phi0_InP
  · change Work.Kernels.InP Work.Kernels.phi2
    exact phi2_InP

end Work.Kernels.KernelGrowth
