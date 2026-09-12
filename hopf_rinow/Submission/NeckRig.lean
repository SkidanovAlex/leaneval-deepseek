import ChallengeDeps
import Submission.NeckCore2
import Mathlib

/-!
# Tail (neck) rigidity: locally linear curves converging to `q` at `b⁻` are radial arcs

Assembly module: `Submission.neck_rigidity` re-exports the verified theorem
`Submission.NeckCore2.neck_rigidity` (the tail-rigidity core, proven in Submission/NeckCore2.lean):
at every point `q` and speed `c > 0` the normal-coordinate data at `q` (radial identity, the
two-sided arc identity for metric-unit `W`) can be built so that every locally linear curve
`γ` of speed `c` on `(a,b)` which converges to `q` at `b⁻` coincides, on a whole left neck
`(b-δ₀,b)`, with the radial exponential arc `t ↦ ExpM ((b-t)•V)` for a fixed vector `V` with
metric norm `c`.
-/

open scoped Manifold ENNReal ContDiff Topology
open Set Filter Metric
open Bundle

namespace Submission

set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 4000000

theorem neck_rigidity {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
    (M : Type*) [EMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [Bundle.RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M => TangentSpace I x)]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M]
    (q : M) (c : NNReal) (hc : 0 < c) :
    ∃ ρ₀ > 0, ∃ ge : E → E →L[ℝ] E →L[ℝ] ℝ,
      ContDiff ℝ 3 ge ∧
      (∀ y u v : E, (ge y) u v = (ge y) v u) ∧
      (∀ y : E, ∀ v : E, v ≠ 0 → 0 < (ge y) v v) ∧
      (∀ y ∈ ball (extChartAt I q q) ρ₀, ∀ u v : E,
         (ge y) u v = (Bundle.RiemannianBundle.g (E := fun x : M => TangentSpace I x)).inner
                       ((extChartAt I q).symm y)
                       ((mfderiv[range I] (extChartAt I q).symm y) u)
                       ((mfderiv[range I] (extChartAt I q).symm y) v)) ∧
      ∃ r > 0, ∃ ExpM : E → M, ∃ S : Set M, ∃ invM : M → E,
        ExpM 0 = q ∧ S ∈ 𝓝 q ∧
        (∀ v ∈ ball (0 : E) r, ExpM v ∈ S) ∧
        ContinuousOn ExpM (ball (0 : E) r) ∧
        Function.Injective (fun v : {v : E // v ∈ ball (0 : E) r} => ExpM v.1) ∧
        Set.SurjOn ExpM (ball (0 : E) r) S ∧
        (∀ y ∈ S, invM y ∈ ball (0 : E) r ∧ ExpM (invM y) = y) ∧
        (∀ v ∈ ball (0 : E) r, invM (ExpM v) = v) ∧
        (∀ v ∈ ball (0 : E) r,
           edist q (ExpM v) = ENNReal.ofReal (Real.sqrt ((ge (extChartAt I q q)) v v))) ∧
        ∃ ρa : ℝ, 0 < ρa ∧ ρa ≤ r ∧
          (∀ (W : E), Real.sqrt ((ge (extChartAt I q q)) W W) = 1 →
            ∀ ⦃s t : ℝ⦄, s ≤ t → |s| < ρa → |t| < ρa →
              edist (ExpM (s • W)) (ExpM (t • W)) = ENNReal.ofReal (t - s)) ∧
          ∀ (a b : ℝ) (hab : a < b) (γ : ℝ → M),
            Metric.IsLocLinear a b c γ →
            Tendsto γ (𝓝[Iio b] b) (𝓝 q) →
            ∃ δ₀ > 0, ∃ V : E, Real.sqrt ((ge (extChartAt I q q)) V V) = c ∧
              ∀ t ∈ Ioo (b - δ₀) b, γ t = ExpM ((b - t) • V) := by
  exact Submission.NeckCore2.neck_rigidity (E := E) (I := I) (M := M) q c hc

end Submission
