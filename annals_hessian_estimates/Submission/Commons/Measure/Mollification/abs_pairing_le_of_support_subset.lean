import Mathlib
import Submission.Commons.Measure.VectorMeasure.pairing_abs_le

namespace Commons.Measure.Mollification

open MeasureTheory Metric Set Filter Function in
open scoped Topology ENNReal RealInnerProductSpace InnerProductSpace Convolution in
theorem abs_pairing_le_of_support_subset {n : ℕ} {k : EuclideanSpace ℝ (Fin n) → ℝ} {ε C : ℝ}
    (hk : ∀ t, 0 ≤ k t) (hC : ∀ t, k t ≤ C) (hC0 : 0 ≤ C)
    (hks : ∀ t, k t ≠ 0 → t ∈ Metric.closedBall 0 ε)
    (ν : SignedMeasure (EuclideanSpace ℝ (Fin n))) (z : EuclideanSpace ℝ (Fin n)) :
    |∫ᵛ t, k (z - t) ∂•ν| ≤ C * (ν.totalVariation (Metric.closedBall z ε)).toReal := by
  set μ : Measure (EuclideanSpace ℝ (Fin n)) := ν.totalVariation with hμ
  have h1 := _root_.Commons.Measure.VectorMeasure.pairing_abs_le ν (fun t => k (z - t))
  refine h1.trans ?_
  have hpt : ∀ x, |k (z - x)| ≤ (Metric.closedBall z ε).indicator (fun _ => C) x := by
    intro x
    by_cases hx : x ∈ Metric.closedBall z ε
    · rw [Set.indicator_of_mem hx]
      rw [abs_le]
      exact ⟨by linarith [hk (z - x), hC0], hC (z - x)⟩
    · rw [Set.indicator_of_notMem hx]
      have hk0 : k (z - x) = 0 := by
        by_contra hne
        have hzx : dist (z - x) 0 ≤ ε := Metric.mem_closedBall.mp (hks (z - x) hne)
        apply hx
        rw [Metric.mem_closedBall, dist_eq_norm, norm_sub_rev]
        rwa [dist_eq_norm, sub_zero] at hzx
      rw [hk0, abs_zero]
  have hgi : Integrable (fun x => (Metric.closedBall z ε).indicator (fun _ => C) x) μ :=
    (integrable_const C).indicator measurableSet_closedBall
  have key := integral_mono_of_nonneg (μ := μ)
      (f := fun x => |k (z - x)|)
      (g := fun x => (Metric.closedBall z ε).indicator (fun _ => C) x)
      (Filter.Eventually.of_forall (fun x => abs_nonneg _)) hgi
      (Filter.Eventually.of_forall hpt)
  rw [integral_indicator_const C measurableSet_closedBall] at key
  simpa [hμ, measureReal_def, smul_eq_mul, mul_comm] using key

end Commons.Measure.Mollification
