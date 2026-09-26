import Mathlib
import Submission.Work.FunctionalEquations.Main
import Submission.Work.FunctionalEquations.InterpolationFormulaSummable

/-!
# The conclusions of CKMRV Theorem 3.1, named

The three conclusions of the assembled theorem
`Work.FE.interpolationBasis_of_functionalEquations`, exposed under their own names so
that a caller does not have to unfold a `Work.Core.InterpolationBasis`.
-/

namespace Work.FE

open LeanEval.Analysis.CKMRVInterpolation
open Work.Core
open scoped FourierTransform SchwartzMap

/-- **The interpolation formula** (CKMRV Theorem 3.1, second conclusion): every radial
Schwartz function is the sum of its four sample sequences against the basis. -/
theorem interpolationFormula {n : ℕ} [NeZero n] (S : InterpolationSolution n)
    (f : RSch n) (x : E n) :
    f.1 x = ∑' i : SampleIdx 1, (coeffs n 1 f.1 i) * (S.basis i).1 x :=
  (interpolationBasis_of_functionalEquations n S).formula f x

/-- **The Kronecker delta pattern** (CKMRV Section 8): the samples of the `i`-th basis
function form the `i`-th standard basis vector. -/
theorem basisSamplesDelta {n : ℕ} [NeZero n] (S : InterpolationSolution n)
    (i : SampleIdx 1) :
    coeffs n 1 (S.basis i).1 = fun j => if j = i then (1 : ℂ) else 0 :=
  (interpolationBasis_of_functionalEquations n S).delta i

/-- **Polynomial growth of the basis** (CKMRV Theorem 3.1, third conclusion): every
Schwartz seminorm of the basis grows at most polynomially in the index. -/
theorem basisSeminormGrowth {n : ℕ} [NeZero n] (S : InterpolationSolution n)
    (k l : ℕ) :
    ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧ ∀ i : SampleIdx 1,
      (SchwartzMap.seminorm ℂ k l) (S.basis i).1 ≤ C * ((i.1.1 : ℝ) + 1) ^ N :=
  (interpolationBasis_of_functionalEquations n S).growth k l

/-- The terms of the interpolation formula are summable: the right side of the
interpolation formula converges absolutely, as stated in CKMRV Theorem 3.1. -/
theorem interpolationFormula_summable {n : ℕ} [NeZero n] (S : InterpolationSolution n)
    (f : RSch n) (x : E n) :
    Summable fun i : SampleIdx 1 => (coeffs n 1 f.1 i) * (S.basis i).1 x :=
  Work.FunctionalEquations.InterpolationFormulaSummable S f x

end Work.FE
