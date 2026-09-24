import Submission.RiemannSurface
import Submission.Holomorphic
import Submission.GreenData
import Submission.GreenInterface
import Submission.MaxPrincipleX
import Submission.SubharmonicAlgebra
import Submission.BarrierComparison

/-!
# Shared vocabulary for the potential-theory lemmas

A pure re-export module: it makes the project's notions `Submission.HarmonicOnX`,
`Submission.HarmonicOnXAt`, `Submission.SubharmonicOnX`, `Submission.SuperharmonicOnX`,
`Submission.HolomorphicOnX`, `Submission.HasLogPoleAt`, `Submission.HasGreenFunctionWeak`,
`Submission.HasGreenFunctionE`, `Submission.LogCoefficientInput`, `Submission.RemovableInput`
available to modules (and to delegated lemma statements) that live under `Submission/Work/`.
-/

open LeanEval.Geometry
open scoped Manifold ContDiff

namespace Work.Potential

end Work.Potential
