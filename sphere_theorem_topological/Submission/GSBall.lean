import Submission.HingeClosed
import Submission.Commons.Geometry.Sphere.modelDist_trig_le_pi_div_two

/-!
# The `π/2`-ball lemma: a first consequence of Toponogov for Grove–Shiohama

Let `sec ≥ 1` (the project normalisation, via the strict quarter-pinching).  If `x : M`, `U V ∈ T_xM`
are unit vectors enclosing an angle `≤ π/2` (i.e. `⟪U,V⟫ ≥ 0`) and `l₁, l₂ ∈ (0, π/2]` with
`l₁ + l₂ < π`, then the two points `GExp x (l₁•U)` and `GExp x (l₂•V)` are at distance at most `π/2`.

This is the "case 3" of the classical Grove–Shiohama argument (both legs in the `π/2`-ball and the
angle at the apex `≤ π/2` force the opposite side `≤ π/2`), derived here from the global hinge
comparison `Submission.HingePiece.gcompHolds_pi` and the pure trigonometry lemma
`Commons.Geometry.Sphere.modelDist_trig_le_pi_div_two`.

The hypothesis is `l₁ + l₂ ≤ π` (the closed-range form `Submission.HingeClosed.gcompHolds_pi_le` of
the hinge comparison).
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 1000000

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal InnerProductSpace
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open Submission.Geodesic
open Submission.GlobalExp
open Submission.HingeGlobal
open Submission.HingeKey
open Submission.HingePiece

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]

namespace Submission.GSBall

noncomputable section

variable [I.Boundaryless] [Nontrivial E] [CompactSpace M]
variable {cov : CovariantDerivative I E (TangentSpace I (M := M))}
variable [ContMDiffCovariantDerivative cov ∞]

/-- **The `π/2`-ball lemma.**  For unit `U V ∈ T_xM` with `⟪U,V⟫ ≥ 0` (angle `≤ π/2`) and
`l₁, l₂ ∈ (0, π/2]` with `l₁ + l₂ < π`, the endpoints of the two short geodesic rays are at
distance `≤ π/2`. -/
theorem edist_le_pi_div_two_of_hinge
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) (hpinch : QuarterPinched cov)
    [PathConnectedSpace M] [RegularSpace M]
    {x : M} {l₁ l₂ : ℝ} {U V : TangentSpace I x}
    (h1 : 0 < l₁) (h2 : 0 < l₂) (hU : ‖U‖ = 1) (hV : ‖V‖ = 1)
    (hsum : l₁ + l₂ ≤ Real.pi)
    (hl₁ : l₁ ≤ Real.pi / 2) (hl₂ : l₂ ≤ Real.pi / 2)
    (hα : 0 ≤ inner ℝ U V)
    (hminp : Manifold.riemannianEDist I x (GExp (cov := cov) hmet x (l₁ • U))
      = ENNReal.ofReal l₁)
    (hminq : Manifold.riemannianEDist I x (GExp (cov := cov) hmet x (l₂ • V))
      = ENNReal.ofReal l₂) :
    Manifold.riemannianEDist I (GExp (cov := cov) hmet x (l₁ • U))
        (GExp (cov := cov) hmet x (l₂ • V))
      ≤ ENNReal.ofReal (Real.pi / 2) := by
  have h := Submission.HingeClosed.gcompHolds_pi_le (cov := cov) hmet htor hpinch (z := x)
    h1 h2 hsum hU hV hminp hminq
  have hmodel : modelDist1 (hingeAngle U V) l₁ l₂ ≤ Real.pi / 2 := by
    have htrig := Commons.Geometry.Sphere.modelDist_trig_le_pi_div_two (l₁ := l₁) (l₂ := l₂)
      (α := hingeAngle U V) h1.le hl₁ h2.le hl₂ (Real.arccos_nonneg _)
      (Real.arccos_le_pi_div_two.mpr hα)
    rw [modelDist1]
    exact htrig
  exact h.trans (ENNReal.ofReal_le_ofReal hmodel)
end

end Submission.GSBall
