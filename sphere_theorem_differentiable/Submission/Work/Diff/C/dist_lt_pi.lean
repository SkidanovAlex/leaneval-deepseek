import Mathlib
import Submission.Work.Diff.C.Lib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

set_option linter.style.haveILetI false

namespace Work.Diff.C

open scoped Manifold ContDiff Bundle Topology
open Bundle Set VectorField CovariantDerivative Metric
open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg Work.Diff.C

/-- Global Bonnet–Myers gives `riemannianEDist p x < ENNReal.ofReal π`; converting the extended
distance to the real-valued `rdist` yields the strict bound. -/
theorem dist_lt_pi
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [T2Space M] [CompactSpace M] [SimplyConnectedSpace M]
    (hdim : 2 ≤ Module.finrank ℝ E)
    (cov : CovariantDerivative I E (TangentSpace I (M := M))) [ContMDiffCovariantDerivative cov ∞]
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) (hpinch : Pinched cov 1 4)
    (p x : M) : rdist (I := I) p x < Real.pi := by
  -- The ambient manifold is compact and simply connected, hence path connected and regular.
  haveI : Nontrivial E := Module.nontrivial_of_finrank_pos (by linarith)
  haveI : PathConnectedSpace M := inferInstance
  haveI : RegularSpace M := inferInstance
  -- `Pinched cov 1 4` is the challenge's `QuarterPinched`.
  have hpinch' : QuarterPinched cov := hpinch
  have h := Submission.GlobalBM.riemannianEDist_lt_pi (cov := cov) hmet htor hpinch' hdim p x
  have hne : Manifold.riemannianEDist I p x ≠ ⊤ := ne_top_of_lt h
  rw [rdist]
  rw [← ENNReal.toReal_ofReal Real.pi_pos.le]
  exact (ENNReal.toReal_lt_toReal hne (ENNReal.ofReal_ne_top)).mpr h

end Work.Diff.C
