/-
# `Final/`: the Riemannian framework of the project, bundled

The areas `LeviCivita`, `Curvature`, `CartanHadamard` and `Space` all work in the same Riemannian
variable block

```
{E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
{H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
{M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
[RiemannianBundle (fun x : M ↦ TangentSpace I x)]
[IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
{cov : CovariantDerivative I E (TangentSpace I (M := M))}
[ContMDiffCovariantDerivative cov ∞]
```

Writing it out in a *statement* is fragile (the `∞` of `WithTop ℕ∞` is a scoped notation, the
implicit instance arguments of `ContMDiffCovariantDerivative` need the Riemannian structure to be
in scope, ...).  This file bundles the block into two classes, `Work.Final.ChartedRiem` and
`Work.Final.ChartedRiemConn`, specialised to the model `E4 = EuclideanSpace ℝ (Fin 4)` of the
project, plus the named smoothness grade `Work.Final.smoothGrade`; a statement can then be written
without any scoped notation.
-/
import Mathlib
import ChallengeDeps
import Submission.Work.Space.Main
import Submission.Work.Space.Split
import Submission.Work.Space.Split.retrB_homotopyEquiv
import Submission.Work.Space.Split.retrA_homotopyEquiv
import Submission.Work.Space.Split.retrAB_homotopyEquiv
import Submission.Work.Space.Split.retrAB_compat
import Submission.Work.Space.Split.retrA_compat
import Submission.Work.Space.Data.slope_norm_ge
import Submission.Work.Curvature.Main
import Submission.Work.Curvature.Bridge
import Submission.Work.RiemLib.ChartCurv
import Submission.Work.RiemLib.ChartConnection
import Submission.Work.LeviCivita.Defs
import Submission.Work.LeviCivita.Koszul

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

namespace Work.Final

noncomputable section

/-- The smoothness grade `∞` of the framework (`((⊤ : ℕ∞) : WithTop ℕ∞)`), named so that
statements need no scoped notation. -/
abbrev smoothGrade : WithTop ℕ∞ := ((⊤ : ℕ∞) : WithTop ℕ∞)

/-- **The Riemannian framework of the project**: a manifold charted on `E4`, with the `∞`-smooth
structure and the tangent bundle as a `C^∞` Riemannian bundle. -/
class ChartedRiem (M : Type*) [TopologicalSpace M] [T2Space M] [ChartedSpace Work.Space.E4 M] where
  /-- `M` is a smooth manifold in the model `I4`. -/
  [manifold : IsManifold Work.Space.I4 smoothGrade M]
  /-- The tangent bundle is a Riemannian bundle. -/
  [riemann : RiemannianBundle (fun x : M ↦ TangentSpace Work.Space.I4 x)]
  /-- The Riemannian metric is `C^∞`. -/
  [smoothMetric : IsContMDiffRiemannianBundle Work.Space.I4 smoothGrade Work.Space.E4
    (fun x : M ↦ TangentSpace Work.Space.I4 x)]

attribute [instance] ChartedRiem.manifold ChartedRiem.riemann ChartedRiem.smoothMetric

namespace ChartedRiem

variable {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace Work.Space.E4 M]
  [ChartedRiem M]

example : IsManifold Work.Space.I4 smoothGrade M := inferInstance
example : RiemannianBundle (fun x : M ↦ TangentSpace Work.Space.I4 x) := inferInstance
example : IsContMDiffRiemannianBundle Work.Space.I4 smoothGrade Work.Space.E4
    (fun x : M ↦ TangentSpace Work.Space.I4 x) := inferInstance

end ChartedRiem

/-- **A smooth torsion-free metric-compatible connection** on a charted Riemannian manifold: the
remaining "connection" part of the framework variable block. -/
class ChartedRiemConn (M : Type*) [TopologicalSpace M] [T2Space M]
    [ChartedSpace Work.Space.E4 M] [ChartedRiem M] where
  /-- The covariant derivative. -/
  cov : CovariantDerivative Work.Space.I4 Work.Space.E4
    (TangentSpace Work.Space.I4 (M := M))
  /-- It is `C^∞`. -/
  [smooth : CovariantDerivative.ContMDiffCovariantDerivative cov smoothGrade]
  /-- It is compatible with the metric. -/
  compat : LeanEval.Geometry.SphereTheorem.IsMetricCompatible cov
  /-- It is torsion free. -/
  torsion : cov.torsion = 0

attribute [instance] ChartedRiemConn.smooth

namespace ChartedRiemConn

variable {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace Work.Space.E4 M]
  [ChartedRiem M] (C : ChartedRiemConn M)

example : CovariantDerivative.ContMDiffCovariantDerivative C.cov smoothGrade := inferInstance

end ChartedRiemConn

example : smoothGrade = (((⊤ : ℕ∞) : WithTop ℕ∞)) := rfl
example [D : Work.Space.RTData] :
    IsManifold Work.Space.I4 (((⊤ : ℕ∞) : WithTop ℕ∞)) D.Mhat := inferInstance
example [D : Work.Space.RTData] : IsManifold Work.Space.I4 smoothGrade D.Mhat := inferInstance

/-- The Riemannian norm of a tangent vector, named so that statements need no scoped notation
(the instance is the one opened by `open scoped Bundle`). -/
noncomputable abbrev riemNorm {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace Work.Space.E4 M] [ChartedRiem M] (x : M)
    (u : TangentSpace Work.Space.I4 x) : ℝ :=
  ‖u‖

/-- The Riemannian inner product of two tangent vectors, named so that statements need no scoped
notation. -/
noncomputable abbrev riemInner {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace Work.Space.E4 M] [ChartedRiem M] (x : M)
    (u v : TangentSpace Work.Space.I4 x) : ℝ :=
  inner ℝ u v

/-- The framework of `M̂` itself, from the assembled space `Work.Space.RTData`. -/
instance instChartedRiemMhat [D : Work.Space.RTData] : ChartedRiem D.Mhat where
  manifold := inferInstance
  riemann := inferInstance
  smoothMetric := inferInstance

/-- **The Levi-Civita connection of `M̂`**, as a `ChartedRiemConn`. -/
def mhatRiemConn [D : Work.Space.RTData]
    [CovariantDerivative.ContMDiffCovariantDerivative
      (Work.LeviCivita.lcConn (I := Work.Space.I4) (M := D.Mhat)) smoothGrade] :
    ChartedRiemConn D.Mhat where
  cov := Work.LeviCivita.lcConn (I := Work.Space.I4) (M := D.Mhat)
  compat := Work.LeviCivita.lcConn_compat
  torsion := Work.LeviCivita.lcConn_torsion

end

end Work.Final
