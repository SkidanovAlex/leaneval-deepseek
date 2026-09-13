import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Commons.Measure.Kernel.setAverage_abs_integral_mul_kernel_le2

namespace Commons.Measure.Kernel

open MeasureTheory Metric Set Filter Function in
open scoped Topology ENNReal in
theorem aemeasurable_integral_closedBall_abs {n : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {x₀ : EuclideanSpace ℝ (Fin n)} {ε : ℝ}
    (hf : LocallyIntegrable f volume) :
    AEMeasurable (fun z : EuclideanSpace ℝ (Fin n) =>
      ∫ τ in Metric.closedBall (x₀ + z) ε, |f τ|) volume := by
  classical
  let g : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) → ℝ :=
    fun p => if ‖p.2 - (x₀ + p.1)‖ ≤ ε then |f p.2| else 0
  have hs : MeasurableSet {p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) |
      ‖p.2 - (x₀ + p.1)‖ ≤ ε} :=
    (isClosed_le (by fun_prop :
        Continuous fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
          ‖p.2 - (x₀ + p.1)‖) continuous_const).measurableSet
  have h1 : AEStronglyMeasurable
      (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) => f p.2)
      (volume.prod volume) :=
    hf.aestronglyMeasurable.comp_snd
  have h2 : AEStronglyMeasurable
      (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) => |f p.2|)
      (volume.prod volume) := by
    simpa only [Real.norm_eq_abs] using h1.norm
  have hg : AEStronglyMeasurable g (volume.prod volume) := by
    have hgg : g = {p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) |
        ‖p.2 - (x₀ + p.1)‖ ≤ ε}.indicator (fun p => |f p.2|) := by
      funext p
      by_cases hp : ‖p.2 - (x₀ + p.1)‖ ≤ ε
      · simp [g, hp]
      · simp [g, hp]
    rw [hgg]
    exact h2.indicator hs
  have hF : AEStronglyMeasurable
      (fun z : EuclideanSpace ℝ (Fin n) => ∫ τ, g (z, τ) ∂volume) volume :=
    hg.integral_prod_right'
  have heq : (fun z : EuclideanSpace ℝ (Fin n) => ∫ τ, g (z, τ) ∂volume)
      =ᵐ[volume] (fun z : EuclideanSpace ℝ (Fin n) =>
        ∫ τ in Metric.closedBall (x₀ + z) ε, |f τ|) := by
    filter_upwards with z
    have hfun : (fun τ : EuclideanSpace ℝ (Fin n) => g (z, τ)) =
        (fun τ : EuclideanSpace ℝ (Fin n) =>
          (Metric.closedBall (x₀ + z) ε).indicator (fun τ => |f τ|) τ) := by
      funext τ
      by_cases hp : ‖τ - (x₀ + z)‖ ≤ ε
      · have hmem : τ ∈ Metric.closedBall (x₀ + z) ε := by
          rw [mem_closedBall, dist_eq_norm]; exact hp
        simp [g, hp, Set.indicator_of_mem hmem]
      · have hmem : τ ∉ Metric.closedBall (x₀ + z) ε := by
          rw [mem_closedBall, dist_eq_norm]; exact hp
        simp [g, hp, Set.indicator_of_notMem hmem]
    rw [hfun]
    exact integral_indicator Metric.isClosed_closedBall.measurableSet
  exact (aemeasurable_congr heq).mp hF.aemeasurable

end Commons.Measure.Kernel