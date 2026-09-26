import Mathlib
import Submission.Work.FunctionalEquations.Gap
import Submission.Work.FunctionalEquations.ExpansionData
import Submission.Work.FunctionalEquations.Reduction
import Submission.Work.FunctionalEquations.Section8ValueDataOfRigidity
import Submission.Work.FunctionalEquations.Section8FourierDataOfRigidity
import Submission.Work.FunctionalEquations.ExpansionDataTwoOfDecay

/-!
# The paper's uniqueness input implies the interpolation basis

Section 8 of the paper deduces the Kronecker-delta pattern of the interpolation basis from
the uniqueness lemma `lem:noPsolutions`: applied to the pair
`(F - 𝓕_x F̃, F̃ - 𝓕_x F)` it gives `F̃ = 𝓕_x F` (hence `ã = â`, `b̃ = b̂`), and applied to
the pointwise differences at the sample radii it gives the normalisations
`F(τ,√(2m)) = e^{2πimτ}`, `F̃(τ,√(2m)) = 0` and their radial derivatives.

This file records that reduction.  `Work.FE.HomogeneousRigidity n c` is the uniqueness input
(`c = 0` is the weight `4` statement used in dimension `8`, `c = 1` the weight `12` statement
used in dimension `24`), and the theorems below produce the interpolation basis from it.
-/

namespace Work.FE

open LeanEval.Analysis.CKMRVInterpolation
open Work.Core
open scoped FourierTransform SchwartzMap

/-- **Section 8 from the uniqueness input.**  The value normalisations and the
Fourier-transform relations of Section 8 follow from `HomogeneousRigidity` and the Fourier
expansions of Steps 1--2. -/
theorem section8Data_of_rigidity {n : ℕ} [NeZero n] {k₀ : ℕ} {c : ℝ} (hk : 1 ≤ k₀)
    (hc : (k₀ : ℝ) - 1 = c) (hR : HomogeneousRigidity n c) (S : FunctionalEquationSolution n)
    (basis : SampleIdx k₀ → RSch n) (hExp : ExpansionDataGen n k₀ S basis) :
    Section8DataGen n k₀ S basis := by
  rw [← hc] at hR
  exact section8DataGen_of
    (Work.FunctionalEquations.Section8ValueDataOfRigidity hk hR S basis hExp)
    (Work.FunctionalEquations.Section8FourierDataOfRigidity hk hR S basis hExp)

/-- **The `E₈` case.**  A solution of the functional equations, together with the paper's
uniqueness input at weight `4` (`c = 0`), yields the interpolation basis starting at
`m = 1`.  The Fourier expansions of Steps 1--2 are a theorem
(`Work.FE.expansionData_of_functionalEquations`), so `HomogeneousRigidity n 0` is the only
remaining input. -/
theorem interpolationBasis_of_functionalEquations_of_rigidity {n : ℕ} [NeZero n]
    (hR : HomogeneousRigidity n 0) (S : FunctionalEquationSolution n) :
    Nonempty (Work.Core.InterpolationBasis n 1) := by
  obtain ⟨basis, hExp⟩ := expansionData_of_functionalEquations S
  exact interpolationBasis_of_data S basis hExp
    (section8Data_of_rigidity (c := 0) (by norm_num) (by norm_num) hR S basis hExp)

/-- **The Leech case.**  If in addition the generating functions decay like
`o(e^{-2π Im τ})`, the `m = 1` coefficients vanish, the expansions start at `m = 2`, and
the uniqueness input at weight `12` (`c = 1`) yields the interpolation basis starting at
`m = 2`. -/
theorem interpolationBasis_two_of_rigidity_and_decay {n : ℕ} [NeZero n]
    (hR : HomogeneousRigidity n 1) (S : FunctionalEquationSolution n)
    (basis : SampleIdx 1 → RSch n) (hExp : ExpansionData n S basis)
    (hdec : TendsToZeroInStrip n 1 S.F) (hdecT : TendsToZeroInStrip n 1 S.Ftilde) :
    Nonempty (Work.Core.InterpolationBasis n 2) := by
  obtain ⟨basis₂, hExp₂⟩ := Work.FunctionalEquations.ExpansionDataTwoOfDecay S basis hExp hdec hdecT
  exact interpolationBasis_of_data_gen (by norm_num) S basis₂ hExp₂
    (section8Data_of_rigidity (c := 1) (by norm_num) (by norm_num) hR S basis₂ hExp₂)

end Work.FE
