import Submission.Work.Section8P.InPExpansion
import Submission.Work.CKFinal.Shadow.Util
import Submission.Work.CKFinal.Shadow.Basic
import Submission.Work.CKFinal.Shadow.BasisCoeffsDelta
import Submission.Work.CKFinal.Shadow.BasisCoeffsDeltaAux
import Submission.Work.CKFinal.Shadow.Coefficients
import Submission.Work.CKFinal.Shadow.DecayExpansionDifference
import Submission.Work.CKFinal.Shadow.Defs
import Submission.Work.CKFinal.Shadow.DeltaGen
import Submission.Work.CKFinal.Shadow.DifferenceExpansionF
import Submission.Work.CKFinal.Shadow.DifferenceExpansionFtilde
import Submission.Work.CKFinal.Shadow.ExpansionData
import Submission.Work.CKFinal.Shadow.ExpansionDataShiftTwo
import Submission.Work.CKFinal.Shadow.ExpansionDataTwoOfDecay
import Submission.Work.CKFinal.Shadow.ExpansionFromFunctionalEquations
import Submission.Work.CKFinal.Shadow.FourierDataExtraction
import Submission.Work.CKFinal.Shadow.FourierExpansionSatisfiesFE
import Submission.Work.CKFinal.Shadow.FunctionCoefficients
import Submission.Work.CKFinal.Shadow.FunctionDerivExpansion
import Submission.Work.CKFinal.Shadow.FunctionExpansion
import Submission.Work.CKFinal.Shadow.Gap
import Submission.Work.CKFinal.Shadow.Gen
import Submission.Work.CKFinal.Shadow.HasDerivAtParametricIntegral
import Submission.Work.CKFinal.Shadow.Main
import Submission.Work.CKFinal.Shadow.MainGen
import Submission.Work.CKFinal.Shadow.ParametricDerivBounds
import Submission.Work.CKFinal.Shadow.ReconstructionCLM
import Submission.Work.CKFinal.Shadow.ReconstructionCLMGen
import Submission.Work.CKFinal.Shadow.ReconstructionGaussian
import Submission.Work.CKFinal.Shadow.ReconstructionGaussianGen
import Submission.Work.CKFinal.Shadow.Reduction
import Submission.Work.CKFinal.Shadow.Section8ValueDataOfRigidity
import Submission.Work.CKFinal.Shadow.SummableExpansionTerms
import Submission.Work.CKFinal.Shadow.TauDiffSetup
import Submission.Work.CKFinal.Shadow.TauDifferenceExpansionF
import Submission.Work.CKFinal.Shadow.TauDifferenceExpansionFtilde
import Submission.Work.CKFinal.Shadow.Thm31Adapter
import Submission.Work.CKFinal.Shadow.ValuePatternGen
import Submission.Work.CKFinal.Shadow.growth_combination
import Submission.Work.CKFinal.Shadow.kernel_isSchwartz
import Submission.Work.CKFinal.Shadow.psi_deriv_bound
import Submission.Work.CKFinal.Shadow.psi_smooth

open scoped ContDiff
set_option linter.dupNamespace false

namespace Work.CKFinal.Shadow

namespace Work.Section8P
export _root_.Work.Section8P (dirichletExpansion)
end Work.Section8P
namespace Work.Section8P
export _root_.Work.Section8P (InP_of_eq_dirichletExpansion)
end Work.Section8P
namespace Work.Section8P
export _root_.Work.Section8P (rate_bound_of)
end Work.Section8P

/-
# `𝒫`-membership of the Section 8 difference pairs

**Why this file exists.**  Section 8 of CKMRV deduces the Kronecker-delta pattern of the
interpolation basis from the uniqueness lemma `lem:noPsolutions`.  The paper-faithful form
of that lemma, `Work.Rigidity.HomogeneousRigidityP n c`
(`Submission/Work/Rigidity/ModerateGrowth.lean`), carries the moderate-growth hypothesis
`g(τ,·), g̃(τ,·) ∈ 𝒫` (`Work.Kernels.InP`) which the `InP`-free variant drops (and which,
as `Submission/Work/Rigidity/Counterexample.lean` shows, cannot be dropped).

The pairs to which Section 8 applies the lemma are differences of the generating functions
from their Fourier expansions:

* `τ ↦ F(τ,√(2m)) − e^{2πimτ}` and `τ ↦ F̃(τ,√(2m))`,
* `τ ↦ D F(τ,√(2m)) − 2πi√(2m)τ e^{2πimτ}` and `τ ↦ D F̃(τ,√(2m))`,
* `τ ↦ F(τ,x) − 𝓕_x F̃(τ,x)` and `τ ↦ F̃(τ,x) − 𝓕_x F(τ,x)`.

Every one of these is a Dirichlet series of the shape `A(τ) + 2πiτ·B(τ)` with
polynomially bounded coefficients, so `Work.Rigidity.InP_of_dirichletExpansion` gives
membership in `𝒫`.  This file packages that shape and the four discharges needed by the
Section 8 arguments.

## Main definitions

* `Work.Section8P.dirichletExpansion k₀ a b` : the shape `A + 2πiτ·B` of the paper's
  generating functions, with `A = Σ aₙ e^{2πinτ}` and `B = Σ bₙ e^{2πinτ}`.

## Main results

* `Work.Section8P.InP_dirichletExpansion` : `dirichletExpansion k₀ a b ∈ 𝒫` when
  `‖a n‖, ‖b n‖` grow at most polynomially.
* `Work.Section8P.InP_of_eq_dirichletExpansion` : transfer along an equality on `ℍ`.
* `Work.Section8P.InP_of_eq_dirichletExpansion_sub` : the same, minus a `𝒫` correction
  (the single Dirichlet term which is normalised away).
* `Work.Section8P.rate_bound_of` : multiplication by `rate m = √(2m)` costs one power.
* `Work.Section8P.InP_fourierExpansionGen`, `…TildeGen` : the crossed Fourier expansions of
  Section 8 lie in `𝒫`.
-/

namespace Work.Section8P

open LeanEval.Analysis.CKMRVInterpolation Work.Core Work.FE Work.FunctionalEquations
open Filter Topology
open scoped FourierTransform SchwartzMap UpperHalfPlane

noncomputable section

/-! ## The four expansions of Section 8 lie in `𝒫` -/

/-- The expansion of `F` at a point, and hence `τ ↦ F(τ,x₀)`, lies in `𝒫`. -/
theorem InP_F_at {n : ℕ} [NeZero n] {k₀ : ℕ} {S : FunctionalEquationSolution n}
    {basis : SampleIdx k₀ → RSch n} {x₀ : E n} {C₀ : ℝ} {N₀ : ℕ} {C₂ : ℝ} {N₂ : ℕ}
    (hC₀ : 0 ≤ C₀)
    (h₀ : ∀ m : Set.Ici k₀, ‖(basis (m, 0)).1 x₀‖ ≤ C₀ * ((m.1 : ℝ) + 1) ^ N₀)
    (hC₂ : 0 ≤ C₂)
    (h₂ : ∀ m : Set.Ici k₀, ‖(basis (m, 2)).1 x₀‖ ≤ C₂ * ((m.1 : ℝ) + 1) ^ N₂)
    (hF : ∀ τ : ℂ, 0 < τ.im → S.F τ x₀ = dirichletExpansion k₀
      (fun m : Set.Ici k₀ => (basis (m, 0)).1 x₀)
      (fun m : Set.Ici k₀ => (rate m.1 : ℂ) * (basis (m, 2)).1 x₀) τ) :
    Work.Kernels.InP (fun τ : ℍ => S.F (τ : ℂ) x₀) :=
  InP_of_eq_dirichletExpansion (k₀ := k₀)
    (a := fun m : Set.Ici k₀ => (basis (m, 0)).1 x₀)
    (b := fun m : Set.Ici k₀ => (rate m.1 : ℂ) * (basis (m, 2)).1 x₀)
    hC₀ h₀ hC₂ (fun m => rate_bound_of hC₂ h₂ m) (f := fun τ => S.F τ x₀) hF

/-- The expansion of `F̃` at a point, and hence `τ ↦ F̃(τ,x₀)`, lies in `𝒫`. -/
theorem InP_Ftilde_at {n : ℕ} [NeZero n] {k₀ : ℕ} {S : FunctionalEquationSolution n}
    {basis : SampleIdx k₀ → RSch n} {x₀ : E n} {C₁ : ℝ} {N₁ : ℕ} {C₃ : ℝ} {N₃ : ℕ}
    (hC₁ : 0 ≤ C₁)
    (h₁ : ∀ m : Set.Ici k₀, ‖(basis (m, 1)).1 x₀‖ ≤ C₁ * ((m.1 : ℝ) + 1) ^ N₁)
    (hC₃ : 0 ≤ C₃)
    (h₃ : ∀ m : Set.Ici k₀, ‖(basis (m, 3)).1 x₀‖ ≤ C₃ * ((m.1 : ℝ) + 1) ^ N₃)
    (hFt : ∀ τ : ℂ, 0 < τ.im → S.Ftilde τ x₀ = dirichletExpansion k₀
      (fun m : Set.Ici k₀ => (basis (m, 1)).1 x₀)
      (fun m : Set.Ici k₀ => (rate m.1 : ℂ) * (basis (m, 3)).1 x₀) τ) :
    Work.Kernels.InP (fun τ : ℍ => S.Ftilde (τ : ℂ) x₀) :=
  InP_of_eq_dirichletExpansion (k₀ := k₀)
    (a := fun m : Set.Ici k₀ => (basis (m, 1)).1 x₀)
    (b := fun m : Set.Ici k₀ => (rate m.1 : ℂ) * (basis (m, 3)).1 x₀)
    hC₁ h₁ hC₃ (fun m => rate_bound_of hC₃ h₃ m) (f := fun τ => S.Ftilde τ x₀) hFt

/-- The radial derivative of the expansion of `F` at a point lies in `𝒫`. -/
theorem InP_radialDeriv_F_at {n : ℕ} [NeZero n] {k₀ : ℕ} {S : FunctionalEquationSolution n}
    {basis : SampleIdx k₀ → RSch n} {x₀ : E n} {C₀ : ℝ} {N₀ : ℕ} {C₂ : ℝ} {N₂ : ℕ}
    (hC₀ : 0 ≤ C₀)
    (h₀ : ∀ m : Set.Ici k₀, ‖radialDeriv 1 (⇑(basis (m, 0)).1) x₀‖ ≤ C₀ * ((m.1 : ℝ) + 1) ^ N₀)
    (hC₂ : 0 ≤ C₂)
    (h₂ : ∀ m : Set.Ici k₀, ‖radialDeriv 1 (⇑(basis (m, 2)).1) x₀‖ ≤ C₂ * ((m.1 : ℝ) + 1) ^ N₂)
    (hDF : ∀ τ : ℂ, 0 < τ.im → radialDeriv 1 (S.F τ) x₀ = dirichletExpansion k₀
      (fun m : Set.Ici k₀ => radialDeriv 1 (⇑(basis (m, 0)).1) x₀)
      (fun m : Set.Ici k₀ => (rate m.1 : ℂ) * radialDeriv 1 (⇑(basis (m, 2)).1) x₀) τ) :
    Work.Kernels.InP (fun τ : ℍ => radialDeriv 1 (S.F (τ : ℂ)) x₀) :=
  InP_of_eq_dirichletExpansion (k₀ := k₀)
    (a := fun m : Set.Ici k₀ => radialDeriv 1 (⇑(basis (m, 0)).1) x₀)
    (b := fun m : Set.Ici k₀ => (rate m.1 : ℂ) * radialDeriv 1 (⇑(basis (m, 2)).1) x₀)
    hC₀ h₀ hC₂ (fun m => rate_bound_of hC₂ h₂ m) (f := fun τ => radialDeriv 1 (S.F τ) x₀) hDF

/-- The radial derivative of the expansion of `F̃` at a point lies in `𝒫`. -/
theorem InP_radialDeriv_Ftilde_at {n : ℕ} [NeZero n] {k₀ : ℕ} {S : FunctionalEquationSolution n}
    {basis : SampleIdx k₀ → RSch n} {x₀ : E n} {C₁ : ℝ} {N₁ : ℕ} {C₃ : ℝ} {N₃ : ℕ}
    (hC₁ : 0 ≤ C₁)
    (h₁ : ∀ m : Set.Ici k₀, ‖radialDeriv 1 (⇑(basis (m, 1)).1) x₀‖ ≤ C₁ * ((m.1 : ℝ) + 1) ^ N₁)
    (hC₃ : 0 ≤ C₃)
    (h₃ : ∀ m : Set.Ici k₀, ‖radialDeriv 1 (⇑(basis (m, 3)).1) x₀‖ ≤ C₃ * ((m.1 : ℝ) + 1) ^ N₃)
    (hDFt : ∀ τ : ℂ, 0 < τ.im → radialDeriv 1 (S.Ftilde τ) x₀ = dirichletExpansion k₀
      (fun m : Set.Ici k₀ => radialDeriv 1 (⇑(basis (m, 1)).1) x₀)
      (fun m : Set.Ici k₀ => (rate m.1 : ℂ) * radialDeriv 1 (⇑(basis (m, 3)).1) x₀) τ) :
    Work.Kernels.InP (fun τ : ℍ => radialDeriv 1 (S.Ftilde (τ : ℂ)) x₀) :=
  InP_of_eq_dirichletExpansion (k₀ := k₀)
    (a := fun m : Set.Ici k₀ => radialDeriv 1 (⇑(basis (m, 1)).1) x₀)
    (b := fun m : Set.Ici k₀ => (rate m.1 : ℂ) * radialDeriv 1 (⇑(basis (m, 3)).1) x₀)
    hC₁ h₁ hC₃ (fun m => rate_bound_of hC₃ h₃ m) (f := fun τ => radialDeriv 1 (S.Ftilde τ) x₀) hDFt

end

end Work.Section8P


end Work.CKFinal.Shadow
