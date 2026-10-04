import Submission.HingeClosed
import Submission.Commons.Geometry.Sphere.modelDist_trig_symm_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The concavity of the distance function outside the `π/2`-ball (midpoint form)

Let `sec ≥ 1` and `p : M`.  The classical "Berger comparison" says that `f = d(p,·)` is *concave*
on `M \ B_{π/2}(p)`: along a geodesic of `M \ B_{π/2}(p)`, `f` lies above its chords.  In the
midpoint (Jensen) form, and expressed intrinsically:

if `x = GExp m (a • ux)`, `y = GExp m (a • (-ux))` are the two ends of a geodesic through `m` and
`p = GExp m (r • up)` with `r = d(m,p) ≥ π/2`, all three sides being minimising, then

`d(x,p) + d(y,p) ≤ 2 r = 2 d(m,p)`.

The proof is the hinge comparison at `m` applied to the two hinges `(x,p)` and `(y,p)`: the hinge
angles are `α` and `π - α`, so the two model distances are governed by
`Commons.Geometry.Sphere.modelDist_trig_symm_le`.
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 2000000

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal InnerProductSpace
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open Submission.Geodesic
open Submission.GlobalExp
open Submission.HingeGlobal
open Submission.HingeKey
open Submission.HingePiece
open Submission.HingeClosed

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]

namespace Submission.GSConcave

noncomputable section

variable [I.Boundaryless] [Nontrivial E] [CompactSpace M]
variable {cov : CovariantDerivative I E (TangentSpace I (M := M))}
variable [ContMDiffCovariantDerivative cov ∞]

/-- **The midpoint concavity of the distance function outside the `π/2`-ball.**  For the two ends
`x = GExp m (a • ux)`, `y = GExp m (a • (-ux))` of a geodesic through `m` and a point
`p = GExp m (r • up)` at distance `r ≥ π/2` from `m` (all sides minimising),
`d(x,p) + d(y,p) ≤ 2 d(m,p)`. -/
theorem edist_add_midpoint_le
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) (hpinch : QuarterPinched cov)
    [PathConnectedSpace M] [RegularSpace M]
    {m p : M} {a r : ℝ} {ux up : TangentSpace I m}
    (ha : 0 < a) (hr : 0 < r) (har : a + r ≤ Real.pi) (hr2 : Real.pi / 2 ≤ r)
    (hux : ‖ux‖ = 1) (hup : ‖up‖ = 1)
    (hminx : Manifold.riemannianEDist I m (GExp (cov := cov) hmet m (a • ux))
      = ENNReal.ofReal a)
    (hminy : Manifold.riemannianEDist I m (GExp (cov := cov) hmet m (a • (-ux)))
      = ENNReal.ofReal a)
    (hminp : Manifold.riemannianEDist I m (GExp (cov := cov) hmet m (r • up))
      = ENNReal.ofReal r) :
    Manifold.riemannianEDist I (GExp (cov := cov) hmet m (a • ux))
        (GExp (cov := cov) hmet m (r • up))
      + Manifold.riemannianEDist I (GExp (cov := cov) hmet m (a • (-ux)))
        (GExp (cov := cov) hmet m (r • up))
      ≤ ENNReal.ofReal (2 * r) := by
  have hrπ : r ≤ Real.pi := by linarith [har, ha]
  have hux' : ‖(-ux : TangentSpace I m)‖ = 1 := by rw [norm_neg]; exact hux
  have h1 := gcompHolds_pi_le (cov := cov) hmet htor hpinch (z := m) ha hr har hux hup hminx hminp
  have h2 := gcompHolds_pi_le (cov := cov) hmet htor hpinch (z := m) ha hr har hux' hup hminy hminp
  have hα0 : 0 ≤ hingeAngle ux up := Real.arccos_nonneg _
  have hαπ : hingeAngle ux up ≤ Real.pi := Real.arccos_le_pi _
  have hsum : modelDist1 (hingeAngle ux up) a r + modelDist1 (hingeAngle (-ux) up) a r
      ≤ 2 * r := by
    have hcos : Real.cos (hingeAngle (-ux) up) = Real.cos (Real.pi - hingeAngle ux up) := by
      have e1 : Real.cos (hingeAngle (-ux) up) = inner ℝ (-ux) up := cos_hingeAngle hux' hup
      have e2 : inner ℝ (-ux) up = - inner ℝ ux up := inner_neg_left _ _
      have e3 : Real.cos (Real.pi - hingeAngle ux up) = - Real.cos (hingeAngle ux up) :=
        Real.cos_pi_sub _
      have e4 : Real.cos (hingeAngle ux up) = inner ℝ ux up := cos_hingeAngle hux hup
      rw [e1, e2, e3, e4]
    rw [modelDist1, modelDist1, hcos]
    exact Commons.Geometry.Sphere.modelDist_trig_symm_le ha.le har hr2 hrπ hα0 hαπ
  calc Manifold.riemannianEDist I (GExp (cov := cov) hmet m (a • ux))
          (GExp (cov := cov) hmet m (r • up))
        + Manifold.riemannianEDist I (GExp (cov := cov) hmet m (a • (-ux)))
          (GExp (cov := cov) hmet m (r • up))
      ≤ ENNReal.ofReal (modelDist1 (hingeAngle ux up) a r)
        + ENNReal.ofReal (modelDist1 (hingeAngle (-ux) up) a r) := add_le_add h1 h2
    _ = ENNReal.ofReal (modelDist1 (hingeAngle ux up) a r
          + modelDist1 (hingeAngle (-ux) up) a r) :=
        (ENNReal.ofReal_add (Real.arccos_nonneg _) (Real.arccos_nonneg _)).symm
    _ ≤ ENNReal.ofReal (2 * r) := ENNReal.ofReal_le_ofReal hsum

end

end Submission.GSConcave
