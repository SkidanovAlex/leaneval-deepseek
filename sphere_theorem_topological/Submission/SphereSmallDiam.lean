import Submission.GSRestricted
import Submission.GlobalBM

/-!
# The target theorem modulo the diameter lower bound `diam > π/2`

`Submission.SphereSmallDiam.sphere_theorem_of_diam_gt`: **the target theorem
`Submission.sphere_theorem`, restricted to diameters `> π/2`**, in exactly the language of the
target (`QuarterPinched cov`, boundaryless compact `T2Space`, `ContMDiffCovariantDerivative`,
`IsMetricCompatible`, `torsion = 0`).

The only extra hypothesis is the existence of a *diameter pair* `(p,q)` at distance `D > π/2`
(the bound `D < π` is *derived*, from the strict Bonnet–Myers theorem
`Submission.GlobalBM.riemannianEDist_lt_pi`: under `QuarterPinched cov` all sectional curvatures
are `> 1` **strictly**, which makes the Bonnet–Myers test-field inequality strict, so every
distance is `< π`).

So the whole target reduces to **`diam(M) > π/2`** — which is Klingenberg's injectivity-radius
estimate (see Roadmap §65.5). -/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal InnerProductSpace
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]

namespace Submission.SphereSmallDiam

/-- **The target theorem for diameters `> π/2`.** -/
theorem sphere_theorem_of_diam_gt
    [I.Boundaryless] [T2Space M] [CompactSpace M] [SimplyConnectedSpace M]
    (hdim : 2 ≤ Module.finrank ℝ E)
    (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    [ContMDiffCovariantDerivative cov ∞]
    (htor : cov.torsion = 0) (hmet : IsMetricCompatible cov) (hpinch : QuarterPinched cov)
    {D : ℝ}
    (hdiam : ∀ r s : M, Manifold.riemannianEDist I r s ≤ ENNReal.ofReal D)
    (hpq : ∃ p q : M, Manifold.riemannianEDist I p q = ENNReal.ofReal D)
    (hDgt : Real.pi / 2 < D) :
    Nonempty (M ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin (Module.finrank ℝ E + 1))) 1) := by
  haveI : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) (by linarith)
  haveI : PathConnectedSpace M := inferInstance
  haveI : RegularSpace M := inferInstance
  -- the bound `D < π`, from the strict Bonnet–Myers theorem
  have hDlt : D < Real.pi := by
    obtain ⟨p, q, hpq'⟩ := hpq
    have h1 : Manifold.riemannianEDist I p q < ENNReal.ofReal Real.pi :=
      Submission.GlobalBM.riemannianEDist_lt_pi (cov := cov) hmet htor hpinch hdim p q
    rw [hpq'] at h1
    exact (ENNReal.ofReal_lt_ofReal_iff Real.pi_pos).mp h1
  exact Submission.GSRestricted.restricted_sphere_theorem (cov := cov) hmet htor hpinch
    hdiam hDgt hDlt hpq

end Submission.SphereSmallDiam
