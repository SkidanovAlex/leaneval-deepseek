import Mathlib
import Submission.Work.FunctionalEquations.Basic
import Submission.Work.FunctionalEquations.DensityOfGaussians

/-!
# Density of the complex Gaussians (paper Lemma 3.3)

`Work.FE.GaussiansDense n` is the density statement in the form in which Step 3 of the
proof of Theorem 3.1 uses it: a continuous linear functional on the complex Schwartz
space that annihilates every Gaussian `x ↦ e^{π i τ ‖x‖²}` with a fixed `Im τ = y > 0`
annihilates every radial Schwartz function.

`Work.FunctionalEquations.DensityOfGaussians` proves it, so it is a theorem and not a
hypothesis of the functional-equation structures.
-/

namespace Work.FE

open LeanEval.Analysis.CKMRVInterpolation
open Work.Core
open scoped FourierTransform SchwartzMap

/-- **Paper Lemma 3.3.**  This is a theorem, not a hypothesis: see
`Work.FunctionalEquations.DensityOfGaussians`. -/
theorem gaussiansDense (n : ℕ) [NeZero n] : GaussiansDense n :=
  fun y hy Λ h => Work.FunctionalEquations.DensityOfGaussians n y hy Λ h

end Work.FE

namespace Work.FunctionalEquations

open LeanEval.Analysis.CKMRVInterpolation

/-- Alias of `Work.FE.gaussiansDense`. -/
theorem gaussiansDense (n : ℕ) [NeZero n] : Work.FE.GaussiansDense n :=
  Work.FE.gaussiansDense n

end Work.FunctionalEquations
