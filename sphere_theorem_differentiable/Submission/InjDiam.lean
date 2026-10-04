import Submission.CutTime
import Submission.ChartBounds
import Submission.CornerStrict

set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open Submission.Geodesic
open Submission.GlobalExp
open Submission.InjRadius

namespace Submission.InjDiam

noncomputable section

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]

variable [I.Boundaryless] [Nontrivial E] [CompactSpace M]
variable {cov : CovariantDerivative I E (TangentSpace I (M := M))}
variable [ContMDiffCovariantDerivative cov ∞]

/-- **The cut point of a unit direction is at distance at least the injectivity radius.**  For a unit
`ξ` at `p` and `InjAtLeast hmet p m`, the point at the cut time `τ(ξ)` is at distance `τ(ξ) ≥ m`
from `p`.  In particular the diameter of `M` is at least `m`. -/
theorem le_edist_cutPoint (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    [PathConnectedSpace M] [RegularSpace M]
    {p : M} {m : ℝ} (hinj : InjAtLeast hmet p m) (hm : 0 < m)
    {ξ : TangentSpace I p} (hξ : ‖ξ‖ = 1) :
    ENNReal.ofReal m ≤ Manifold.riemannianEDist I p
      (GExp (cov := cov) hmet p
        ((Submission.CutTime.cutTime (I := I) hmet p ξ) • ξ)) := by
  have hmτ : m ≤ Submission.CutTime.cutTime (I := I) hmet p ξ :=
    Submission.CutTime.injAtLeast_le_cutTime (cov := cov) hmet htor hinj hξ
  have hcut : 0 ≤ Submission.CutTime.cutTime (I := I) hmet p ξ := le_trans hm.le hmτ
  have hmem : Submission.CutTime.cutTime (I := I) hmet p ξ
      ∈ Submission.CutTime.minimisingSet (I := I) hmet p ξ :=
    (Submission.CutTime.mem_minimisingSet_iff (cov := cov) hmet htor hξ).mpr ⟨hcut, le_rfl⟩
  rw [hmem.2]
  exact ENNReal.ofReal_le_ofReal hmτ

/-- **A non-zero tangent vector at every point** (from `Nontrivial E`). -/
theorem exists_ne_zero_tangent (p : M) : ∃ v : TangentSpace I p, v ≠ 0 := by
  obtain ⟨e, he⟩ := exists_ne (0 : E)
  refine ⟨frameVector (I := I) p p e, fun h0 => he ?_⟩
  exact (Submission.ChartBounds.frameVector_eq_zero_iff (I := I) (x₀ := p) (p := p)
    (mem_chart_source H p) e).mp h0

/-- **The diameter dominates the injectivity radius.**  If `GExp` is injective on the ball of radius
`m > 0` at `p`, then there is a point of `M` at distance at least `m` from `p`. -/
theorem exists_edist_ge_inj (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    [PathConnectedSpace M] [RegularSpace M]
    {p : M} {m : ℝ} (hinj : InjAtLeast hmet p m) (hm : 0 < m) :
    ∃ q : M, ENNReal.ofReal m ≤ Manifold.riemannianEDist I p q := by
  obtain ⟨w, hw⟩ := exists_ne_zero_tangent (I := I) (M := M) p
  refine ⟨_, le_edist_cutPoint (cov := cov) hmet htor hinj hm (ξ := unitOf w hw) (unitOf_norm w hw)⟩

end

end Submission.InjDiam
