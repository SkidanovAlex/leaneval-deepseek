import Submission.Work.Final.Final
import Submission.Klingenberg

/-!
# The topological sphere theorem (Berger–Klingenberg–Rauch), assembled

This is the final wiring: `Submission.Klingenberg.sphere_theorem_of_klingenberg` reduces the
topological sphere theorem to Klingenberg's diameter estimate `Submission.Klingenberg.KlingenbergBound`,
and that estimate is now the theorem `Work.Final.klingenbergBound_proved`
(`Submission/Work/Final/Final.lean`).

## Main result

* `Work.Final.sphere_theorem_proved` — a compact, simply connected Riemannian manifold of dimension
  `≥ 2` with strictly quarter-pinched sectional curvature is homeomorphic to a sphere.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]

namespace Work.Final

/-- **The topological sphere theorem.**  A compact, simply connected Riemannian manifold of
dimension `≥ 2` whose sectional curvature is strictly quarter-pinched (`QuarterPinched cov`, i.e.
`1 < sec ≤ 4` for the project's normalisation) is homeomorphic to the sphere of the same dimension.

This is `Submission.sphere_theorem`'s statement, with Klingenberg's diameter estimate supplied by
`Work.Final.klingenbergBound_proved` rather than assumed. -/
theorem sphere_theorem_proved
    [I.Boundaryless] [T2Space M] [CompactSpace M] [SimplyConnectedSpace M]
    (hdim : 2 ≤ Module.finrank ℝ E)
    (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    [ContMDiffCovariantDerivative cov ∞]
    (htor : cov.torsion = 0) (hmet : IsMetricCompatible cov) (hpinch : QuarterPinched cov) :
    Nonempty
      (M ≃ₜ sphere (0 : EuclideanSpace ℝ (Fin (Module.finrank ℝ E + 1))) 1) := by
  haveI : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) (by linarith)
  exact Submission.Klingenberg.sphere_theorem_of_klingenberg (I := I) (cov := cov)
    hdim htor hmet hpinch (hK := klingenbergBound_proved (I := I) (M := M) cov)

end Work.Final
