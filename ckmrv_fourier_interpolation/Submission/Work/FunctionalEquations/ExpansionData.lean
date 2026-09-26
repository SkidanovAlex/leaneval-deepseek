import Mathlib
import Submission.Work.FunctionalEquations.Coefficients
import Submission.Work.FunctionalEquations.Gap
import Submission.Work.FunctionalEquations.FunctionCoefficients
import Submission.Work.FunctionalEquations.FunctionExpansion
import Submission.Work.FunctionalEquations.FunctionDerivExpansion

/-!
# Steps 1--2 of the proof of Theorem 3.1

From hypotheses (i)--(v) alone, the generating functions have the Fourier expansions
(3.1), (3.2) with coefficients the contour integrals of `Work.FE.Coefficients`, and those
coefficients are radial Schwartz functions whose radial seminorms grow at most
polynomially in the index.

This is the analytic half (`Work.FE.ExpansionData`) of the remaining gap
`Work.FE.ExpansionDataExists`; the Section 8 half is `Work.FE.Section8Data`.
-/

namespace Work.FE

open LeanEval.Analysis.CKMRVInterpolation
open Work.Core
open scoped FourierTransform SchwartzMap

/-- **Paper Steps 1--2, assembled.**  From hypotheses (i)--(v), the coefficient functions
`aCoeff`, `aTildeCoeff`, `bCoeff`, `bTildeCoeff` are the radial Schwartz coefficient
families of two Fourier expansions of `F` and `F̃`, differentiable termwise in `x`, with
polynomially growing radial seminorms: the analytic half of the gap between
`FunctionalEquationSolution n` and `InterpolationSolution n`. -/
theorem expansionData_of_functionalEquations {n : ℕ} [NeZero n]
    (S : FunctionalEquationSolution n) :
    ∃ basis : SampleIdx 1 → RSch n, ExpansionData n S basis := by
  obtain ⟨basis, h0, h1, h2, h3, hgrow⟩ :=
    Work.FunctionalEquations.FunctionCoefficients S
  obtain ⟨hF, hFt⟩ := Work.FunctionalEquations.FunctionExpansion S
  obtain ⟨hDF, hDFt⟩ := Work.FunctionalEquations.FunctionDerivExpansion S
  refine ⟨basis, ?_, ?_, ?_, ?_, ?_⟩
  · intro τ x hτ
    rw [hF τ x hτ]
    congr 1
    · exact tsum_congr fun m => by rw [h0 m x]
    · congr 1
      exact tsum_congr fun m => by rw [h2 m x]
  · intro τ x hτ
    rw [hFt τ x hτ]
    congr 1
    · exact tsum_congr fun m => by rw [h1 m x]
    · congr 1
      exact tsum_congr fun m => by rw [h3 m x]
  · intro ℓ τ x hτ
    rw [hDF ℓ τ x hτ]
    congr 1
    · exact tsum_congr fun m => by rw [show ⇑(basis (m, 0)).1 = aCoeff S m from funext (h0 m)]
    · congr 1
      exact tsum_congr fun m => by rw [show ⇑(basis (m, 2)).1 = bCoeff S m from funext (h2 m)]
  · intro ℓ τ x hτ
    rw [hDFt ℓ τ x hτ]
    congr 1
    · exact tsum_congr fun m => by rw [show ⇑(basis (m, 1)).1 = aTildeCoeff S m from funext (h1 m)]
    · congr 1
      exact tsum_congr fun m => by rw [show ⇑(basis (m, 3)).1 = bTildeCoeff S m from funext (h3 m)]
  · exact hgrow

end Work.FE
