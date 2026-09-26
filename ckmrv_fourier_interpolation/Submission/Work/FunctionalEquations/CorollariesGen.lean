import Mathlib
import Submission.Work.FunctionalEquations.MainGen

/-!
# The conclusions of Theorem 3.1, general `k₀`

The `k₀`-indexed analogue of `Work.FE.Corollaries`, plus the `k₀ = 2` instance of
`Work.Core.InterpolationBasis` which is what the Leech lattice (`d = 24`) needs.
-/

namespace Work.FE

open LeanEval.Analysis.CKMRVInterpolation
open Work.Core
open scoped FourierTransform SchwartzMap

/-- **The interpolation formula**, basis starting at `k₀`. -/
theorem interpolationFormula_gen {n : ℕ} [NeZero n] {k₀ : ℕ} (hk : 1 ≤ k₀)
    (S : InterpolationSolutionGen n k₀) (f : RSch n) (x : E n) :
    f.1 x = ∑' i : SampleIdx k₀, (coeffs n k₀ f.1 i) * (S.basis i).1 x :=
  (interpolationBasis_of_functionalEquations_gen hk S).formula f x

/-- **The Kronecker delta pattern**, basis starting at `k₀`. -/
theorem basisSamplesDelta_gen {n : ℕ} [NeZero n] {k₀ : ℕ} (hk : 1 ≤ k₀)
    (S : InterpolationSolutionGen n k₀) (i : SampleIdx k₀) :
    coeffs n k₀ (S.basis i).1 = fun j => if j = i then (1 : ℂ) else 0 :=
  (interpolationBasis_of_functionalEquations_gen hk S).delta i

/-- **Polynomial growth of the basis**, basis starting at `k₀`. -/
theorem basisSeminormGrowth_gen {n : ℕ} [NeZero n] {k₀ : ℕ} (hk : 1 ≤ k₀)
    (S : InterpolationSolutionGen n k₀) (k l : ℕ) :
    ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧ ∀ i : SampleIdx k₀,
      (SchwartzMap.seminorm ℂ k l) (S.basis i).1 ≤ C * ((i.1.1 : ℝ) + 1) ^ N :=
  (interpolationBasis_of_functionalEquations_gen hk S).growth k l

/-- **The Leech case.**  An `InterpolationSolutionGen n 2`, i.e. the generating functions
with Fourier expansions and Section 8 normalisations starting at `m = 2`, produces an
interpolation basis indexed from `k₀ = 2`; this is the `d = 24` case of CKMRV
Theorem 1.9. -/
noncomputable def interpolationBasis_two {n : ℕ} [NeZero n]
    (S : InterpolationSolutionGen n 2) : Work.Core.InterpolationBasis n 2 :=
  interpolationBasis_of_functionalEquations_gen (by norm_num) S

/-- The interpolation formula in the Leech case. -/
theorem interpolationFormula_two {n : ℕ} [NeZero n]
    (S : InterpolationSolutionGen n 2) (f : RSch n) (x : E n) :
    f.1 x = ∑' i : SampleIdx 2, (coeffs n 2 f.1 i) * (S.basis i).1 x :=
  (interpolationBasis_two S).formula f x

end Work.FE

namespace Work.FunctionalEquations

open LeanEval.Analysis.CKMRVInterpolation

/-- Alias of `Work.FE.interpolationBasis_two`. -/
noncomputable def interpolationBasis_two {n : ℕ} [NeZero n]
    (S : Work.FE.InterpolationSolutionGen n 2) : Work.Core.InterpolationBasis n 2 :=
  Work.FE.interpolationBasis_two S

end Work.FunctionalEquations
