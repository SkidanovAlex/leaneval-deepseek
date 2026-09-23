import Mathlib
import Submission.Work.OddBound.Assembly
import Submission.Work.OddBound.uniformPinch.exists_uniform_lt_curvVec_of_lt
import Submission.Work.ValueClosed.ValueClosed
import Submission.XuReduction

/-!
# The odd-dimensional Klingenberg bound, pointwise strictly quarter-pinched

`Submission/Work/OddBound/OddBound.lean` proves the odd length bound with the hypothesis
`K/4 + ε ≤ sec ≤ K` — the form in which *uniform* strict pinching is supplied by
`Submission.PinchUniform`.  This module records the equivalent form closest to the literature
(Abresch–Meyer, Theorem 1.6: *strictly* `1/4`-pinched), in which the pinching is only required
**pointwise strictly**: `K/4 < sec ≤ K` at every orthonormal pair.  Compactness of `M` upgrades the
pointwise strict inequality to a uniform margin
(`Work.OddBound.uniformPinch.exists_uniform_lt_curvVec_of_lt`), which is what the theorems of
`OddBound.lean` consume.

Also here: `diameter_gt_half_pi_odd_of_lt`, the pointwise version of the odd half of Klingenberg's
diameter estimate (the uniform version is `Work.OddBound.diameter_gt_half_pi_odd`, in
`Submission/Work/OddBound/OddDiameter.lean`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open MeasureTheory
open scoped MeasureTheory Interval
open Submission.Geodesic Submission.JacobiGlobal Submission.GlobalExp Submission.Length
open Submission.InjRadius Submission.IndexIntrinsic Submission.CurvatureVec

namespace Work.OddBound

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

/-- **Klingenberg's length bound in odd dimensions, pointwise strictly quarter-pinched.**

For a compact, connected, simply connected odd-dimensional Riemannian manifold with
`K/4 < sec ≤ K` at every orthonormal pair and `0 < K < 4`, every closed geodesic loop has length
`≥ 2π/√K`.  This is Klingenberg 1961 (Abresch–Meyer Theorem 1.6) with the pinching stated
pointwise; compactness of `M` supplies the uniform margin consumed by
`Work.OddBound.klingenberg_length_bound_odd_strict`. -/
theorem klingenberg_length_bound_odd_of_lt
    [PathConnectedSpace M] [RegularSpace M] [SimplyConnectedSpace M]
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    (hDim : 3 ≤ Module.finrank ℝ E)
    {K : ℝ} (hK : 0 < K) (hK4 : K < 4)
    (hcurv : Submission.RauchK.CurvLe cov K)
    (hpinch : ∀ (p : M) (u v : TangentSpace I p), ‖u‖ = 1 → ‖v‖ = 1 → inner ℝ u v = 0 →
      K / 4 < inner ℝ (curvVec cov p u v v) u) :
    ∀ {p : M} {T : ℝ} {γ : ℝ → M},
      Submission.KlingenbergLemma.IsClosedGeodesicLoopAt (I := I) hmet p T γ →
      2 * Real.pi / Real.sqrt K ≤ T := by
  haveI : Nonempty M := PathConnectedSpace.nonempty
  obtain ⟨ε, hεpos, hε⟩ :=
    Work.OddBound.uniformPinch.exists_uniform_lt_curvVec_of_lt (I := I) (cov := cov) hmet htor
      (d := K / 4) hpinch
  intro p T γ hloop
  exact Work.OddBound.klingenberg_length_bound_odd_strict_of_minimaxInput (I := I) (cov := cov)
    hmet htor hDim hK hεpos hcurv hε
    (minimaxInput_of_lhl (I := I) (cov := cov) hmet htor hK hcurv) hloop

/-- **The odd-dimensional Klingenberg diameter estimate `(K2)`, pointwise strictly quarter-pinched.**
This is `Work.OddBound.diameter_gt_half_pi_odd` with the uniform margin replaced by the pointwise
strict inequality `K/4 < sec`. -/
theorem diameter_gt_half_pi_odd_of_lt
    [PathConnectedSpace M] [RegularSpace M] [SimplyConnectedSpace M]
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    (hDim : 3 ≤ Module.finrank ℝ E)
    {K : ℝ} (hK : 0 < K) (hK4 : K < 4)
    (hcurv : Submission.RauchK.CurvLe cov K)
    (hpinch : ∀ (p : M) (u v : TangentSpace I p), ‖u‖ = 1 → ‖v‖ = 1 → inner ℝ u v = 0 →
      K / 4 < inner ℝ (curvVec cov p u v v) u) :
    ∃ p q : M, ENNReal.ofReal (Real.pi / 2) < Manifold.riemannianEDist I p q := by
  refine Submission.KlingenbergXu.diameter_gt_half_pi_of_klingenberg_loop (I := I) (cov := cov)
    hmet htor hK hK4 hcurv
    (fun p m hm hinj hmax hcon u v huv hu hv hG =>
      Submission.XuReduction.klingenbergLoopStep (I := I) (cov := cov) hmet htor hcurv hK
        p hm hinj hmax hcon u v huv hu hv hG) ?_
  intro p T γ hloop
  exact Work.ValueClosed.pinched_loop_length_lower_bound_core (I := I) (cov := cov) hmet htor hK
    hcurv
    (fun p T γ hl =>
      klingenberg_length_bound_odd_of_lt (I := I) (cov := cov) hmet htor hDim hK hK4 hcurv
        hpinch hl) hloop

end

end Work.OddBound
