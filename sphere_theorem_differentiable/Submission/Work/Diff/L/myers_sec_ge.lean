import Mathlib
import Submission.Work.Diff.L.Deps
import Submission.Work.Diff.L.myers_sec_ge_aux

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.L

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric
open Submission.Geodesic Submission.CurvatureVec Submission.ChartCurv Submission.ChartConnection

/-- **Bonnet–Myers with a general lower sectional-curvature bound, assumed only along the geodesic.**

A unit-speed geodesic which realises the distance between its endpoints has length at most
`π / √k`, provided the sectional curvature is `> k` at every point of the geodesic, for every
orthonormal pair of tangent vectors there.

This generalises `Submission.GlobalBM.le_pi_of_minimising_geodesic` (which gives `L < π` under the
*global* hypothesis `QuarterPinched cov`, i.e. `1 < sec ≤ 4` at every point of `M`): here the
pinching is (a) only a lower bound and (b) needed only along the geodesic.

HOW TO PROVE (the pinching is consumed in exactly two places).  In `Submission/GlobalBM.lean`,
`grep hpinch` inside the proof of `le_pi_of_minimising_geodesic` (lines 699–1937) hits only the two
calls `indexIntegrand_testFieldS_pointwise` (the block defining `hpoint`) and
`indexIntegrand_testFieldS_pointwise_strict` (in the block `hmono`); every other ingredient
(`exists_chart_pieces`, `exists_parallel_system`, the `fam2Energy` second-derivative machinery,
`hmin`) is pinching-free.  Concretely:

* restate `indexIntegrand_testFieldS_pointwise` and
  `indexIntegrand_testFieldS_pointwise_strict` with the hypothesis
  `hpinch` replaced by the single pointwise bound
  `k ≤ inner ℝ (frameVector (I := I) x₀ ((extChartAt I x₀).symm (u t)) (Y t))
        (curvVec cov ((extChartAt I x₀).symm (u t))
          (frameVector (I := I) x₀ ((extChartAt I x₀).symm (u t)) (Y t))
          (frameVector (I := I) x₀ ((extChartAt I x₀).symm (u t)) (w t))
          (frameVector (I := I) x₀ ((extChartAt I x₀).symm (u t)) (w t)))`
  (the shape produced by `Submission.Pinch.one_le_inner_curvVec`), and with the conclusions
  `k * Real.sin (Real.pi * (a + t) / L) ^ 2 - (Real.pi / L * Real.cos (Real.pi * (a + t) / L)) ^ 2
     ≤ indexIntegrand …`   and the same with `<` in the strict version;
* copy the body of `le_pi_of_minimising_geodesic` verbatim, replacing the `ff` of the tail by
  `fun t => k * Real.sin (Real.pi * t / L) ^ 2 - (Real.pi / L * Real.cos (Real.pi * t / L)) ^ 2`
  (so `hffint` becomes `(k * L ^ 2 - Real.pi ^ 2) / (2 * L)`: the integral of `sin²` is `L/2`,
  multiplied by `k`), supplying the new hypothesis at each of the two call sites from `hsec`
  (rewrite the point with the local `have hsymm : (extChartAt I (x k)).symm (up k s) = γ (c k + s)`
  and get orthonormality from `hYunit`/`horth`/`hwunit` via `chartGram_apply`), and
* `by_contra hcon` now assumes `Real.pi / Real.sqrt k < L`, so the final `hpi` becomes
  `0 ≤ (k * L ^ 2 - Real.pi ^ 2) / (2 * L)` (from `Real.pi ^ 2 < k * L ^ 2`); the conclusion is the
  non-strict `L ≤ Real.pi / Real.sqrt k` (the strict pointwise step may be dropped if convenient,
  but the tail's `Finset.sum_lt_sum` argument is already there). -/
theorem myers_sec_ge
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [I.Boundaryless]
    [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [ContMDiffCovariantDerivative cov ∞]
    {k : ℝ} (hk : 0 < k)
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    (hdim : 2 ≤ Module.finrank ℝ E)
    {γ : ℝ → M} {V : Set ℝ} (hV : IsOpen V) {L : ℝ} (hL : 0 < L)
    (hVab : Icc 0 L ⊆ V) (hγ : ContMDiffOn 𝓘(ℝ) I ∞ γ V)
    (hgeo0 : ∀ t ∈ V, IsGeodesicAt (I := I) cov γ t)
    (hunit : ∀ t ∈ V, ‖curveVelocity (I := I) γ t‖ = 1)
    (hsec : ∀ t ∈ Icc 0 L, ∀ u v : TangentSpace I (γ t),
      inner ℝ u u = 1 → inner ℝ v v = 1 → inner ℝ u v = 0 →
      k < inner ℝ (curvVec cov (γ t) u v v) u)
    (hmin : Manifold.riemannianEDist I (γ 0) (γ L) = ENNReal.ofReal L) :
    L ≤ Real.pi / Real.sqrt k :=
  Work.Diff.L.Aux.myers_sec_ge_aux hk hmet htor hdim hV hL hVab hγ hgeo0 hunit hsec hmin

end Work.Diff.L
