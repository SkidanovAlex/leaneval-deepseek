import Mathlib
import Submission.Work.Kernels.Classical
import Submission.Work.Kernels.Kernels
import Submission.Work.Kernels.LogLambda.LogNormalisation
import Submission.Work.Kernels.LogLambda.LogLaws
import Submission.Work.Kernels.LogLambda.LogAssembly
import Submission.Work.Kernels.LogLambda.LogGrowth.Lfun_sub_pi_I_bound
import Submission.Work.Kernels.LogLambda.ThetaLower.ratio_estimate
import Submission.Work.Analysis.DiscreteValues.eq_const_of_isPreconnected
import Submission.Work.Residues.ThetaEpt
import Submission.Work.Residues.ThetaAux
import Submission.Work.Residues.DeltaExpansion
import Submission.Work.Residues.LamSExpansion

namespace Work.Residues

open UpperHalfPlane ModularGroup Matrix
open scoped MatrixGroups Manifold Modular ModularForm

/-- The second-order cusp expansions of the atoms, with `E = e^{πiτ}` (`‖E‖ = e^{-π Im τ}`):
`U = 1 + 8E + O(‖E‖²)`, `V = 16E + O(‖E‖³)`, `Δ = E² + O(‖E‖⁴)` and `𝓛_S = -16E + O(‖E‖³)`.
The stated order is exactly what the explicit theta series give; the branch of `𝓛_S` is pinned
by `𝓛_S(τ+1) = -𝓛_S(τ)`. -/
theorem ThetaExpansion :
    (∃ C : ℝ, 0 < C ∧ ∀ τ : UpperHalfPlane, 1 ≤ τ.im →
        ‖Work.Kernels.UFun τ - 1 - 8 * Complex.exp (Real.pi * Complex.I * (τ : ℂ))‖ ≤
          C * ‖Complex.exp (Real.pi * Complex.I * (τ : ℂ))‖ ^ 2) ∧
    (∃ C : ℝ, 0 < C ∧ ∀ τ : UpperHalfPlane, 1 ≤ τ.im →
        ‖Work.Kernels.VFun τ - 16 * Complex.exp (Real.pi * Complex.I * (τ : ℂ))‖ ≤
          C * ‖Complex.exp (Real.pi * Complex.I * (τ : ℂ))‖ ^ 3) ∧
    (∃ C : ℝ, 0 < C ∧ ∀ τ : UpperHalfPlane, 1 ≤ τ.im →
        ‖Work.Kernels.DeltaFun τ - (Complex.exp (Real.pi * Complex.I * (τ : ℂ))) ^ 2‖ ≤
          C * ‖Complex.exp (Real.pi * Complex.I * (τ : ℂ))‖ ^ 4) ∧
    (∀ ℓ : Work.Kernels.LogLambdaData, ∃ C : ℝ, 0 < C ∧ ∀ τ : UpperHalfPlane, 1 ≤ τ.im →
        ‖ℓ.L_S τ + 16 * Complex.exp (Real.pi * Complex.I * (τ : ℂ))‖ ≤
          C * ‖Complex.exp (Real.pi * Complex.I * (τ : ℂ))‖ ^ 3) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · obtain ⟨C, hC, h⟩ := UFun_expansion
    exact ⟨C, hC, fun τ hτ => by simpa only [Ept] using h τ hτ⟩
  · obtain ⟨C, hC, h⟩ := VFun_expansion
    exact ⟨C, hC, fun τ hτ => by simpa only [Ept] using h τ hτ⟩
  · obtain ⟨C, hC, h⟩ := DeltaExpansion
    exact ⟨C, hC, fun τ hτ => by simpa only [Ept] using h τ hτ⟩
  · intro ℓ
    obtain ⟨C, hC, h⟩ := LamSExpansion
    refine ⟨C, hC, fun τ hτ => ?_⟩
    rw [LogLambdaData_LS_eq_LamS ℓ τ (by linarith)]
    simpa only [Ept] using h τ hτ

end Work.Residues
