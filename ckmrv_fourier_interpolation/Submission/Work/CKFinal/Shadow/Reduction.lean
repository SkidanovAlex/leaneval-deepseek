import Submission.Work.FunctionalEquations.Reduction
import Submission.Work.CKFinal.Shadow.Util
import Submission.Work.CKFinal.Shadow.Basic
import Submission.Work.CKFinal.Shadow.BasisCoeffsDelta
import Submission.Work.CKFinal.Shadow.BasisCoeffsDeltaAux
import Submission.Work.CKFinal.Shadow.DeltaGen
import Submission.Work.CKFinal.Shadow.Gap
import Submission.Work.CKFinal.Shadow.Gen
import Submission.Work.CKFinal.Shadow.Main
import Submission.Work.CKFinal.Shadow.MainGen
import Submission.Work.CKFinal.Shadow.ReconstructionCLM
import Submission.Work.CKFinal.Shadow.ReconstructionCLMGen
import Submission.Work.CKFinal.Shadow.ReconstructionGaussian
import Submission.Work.CKFinal.Shadow.ReconstructionGaussianGen
import Submission.Work.CKFinal.Shadow.SummableExpansionTerms
import Submission.Work.CKFinal.Shadow.ValuePatternGen

open scoped ContDiff
set_option linter.dupNamespace false

namespace Work.CKFinal.Shadow


/-!
# The complete input list for the interpolation basis

These two theorems record exactly what a caller must supply to obtain
`Work.Core.InterpolationBasis n k₀`: a solution of the functional equations (hypotheses
(i)--(v)) together with, for a named coefficient family `basis : SampleIdx k₀ → RSch n`,

* the Fourier expansions of Steps 1--2 and the polynomial growth of the radial seminorms
  (`Work.FE.ExpansionDataGen` / `Work.FE.ExpansionData`), and
* the Section 8 normalisations (`Work.FE.Section8DataGen` / `Work.FE.Section8Data`).

For a fixed solution the first item is now a theorem:
`Work.FE.expansionData_of_functionalEquations` produces a `basis` with
`ExpansionData`; what remains in general is the Section 8 half.
-/

namespace Work.FE

open LeanEval.Analysis.CKMRVInterpolation
open Work.Core
open scoped FourierTransform SchwartzMap

/-- **The `k₀ = 1` reduction.**  Steps 1--2 plus the Section 8 normalisations for a named
coefficient family produce the interpolation basis starting at `m = 1`. -/
theorem interpolationBasis_of_data {n : ℕ} [NeZero n] (S : FunctionalEquationSolution n)
    (basis : SampleIdx 1 → RSch n) (hExp : ExpansionData n S basis)
    (h8 : Section8Data n S basis) :
    Nonempty (Work.Core.InterpolationBasis n 1) := by
  obtain ⟨hF, hFt, hDF, hDFt, hG⟩ := hExp
  obtain ⟨hfb, hfb', hvF, hvFt, hvdF, hvdFt⟩ := h8
  exact ⟨interpolationBasis_of_functionalEquations n
    { toFunctionalEquationSolution := S
      basis := basis
      expansion_F := hF
      expansion_Ftilde := hFt
      expansion_F_radialDeriv := hDF
      expansion_Ftilde_radialDeriv := hDFt
      fourier_basis := hfb
      fourier_basis' := hfb'
      value_F := hvF
      value_Ftilde := hvFt
      value_radialDeriv_F := hvdF
      value_radialDeriv_Ftilde := hvdFt
      growth_radial := hG }⟩

/-- **The general-`k₀` reduction**, which is what the Leech lattice (`d = 24`, `k₀ = 2`)
needs: Steps 1--2 plus the Section 8 normalisations indexed from `k₀ ≥ 1`. -/
theorem interpolationBasis_of_data_gen {n : ℕ} [NeZero n] {k₀ : ℕ} (hk : 1 ≤ k₀)
    (S : FunctionalEquationSolution n) (basis : SampleIdx k₀ → RSch n)
    (hExp : ExpansionDataGen n k₀ S basis) (h8 : Section8DataGen n k₀ S basis) :
    Nonempty (Work.Core.InterpolationBasis n k₀) := by
  obtain ⟨hF, hFt, hDF, hDFt, hG⟩ := hExp
  obtain ⟨hfb, hfb', hvF, hvFt, hvdF, hvdFt⟩ := h8
  exact ⟨interpolationBasis_of_functionalEquations_gen hk
    { toFunctionalEquationSolution := S
      basis := basis
      expansion_F := hF
      expansion_Ftilde := hFt
      expansion_F_radialDeriv := hDF
      expansion_Ftilde_radialDeriv := hDFt
      fourier_basis := hfb
      fourier_basis' := hfb'
      value_F := hvF
      value_Ftilde := hvFt
      value_radialDeriv_F := hvdF
      value_radialDeriv_Ftilde := hvdFt
      growth_radial := hG }⟩

end Work.FE


end Work.CKFinal.Shadow
