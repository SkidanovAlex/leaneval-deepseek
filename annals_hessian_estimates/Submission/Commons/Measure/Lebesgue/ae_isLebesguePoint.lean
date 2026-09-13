import Mathlib

namespace Commons.Measure.Lebesgue

open MeasureTheory Metric Set Filter Function in
open scoped BigOperators ENNReal Topology RealInnerProductSpace InnerProductSpace Convolution in
theorem ae_isLebesguePoint {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : LocallyIntegrable f volume) :
    ∀ᵐ x ∂volume,
      Tendsto (fun r : ℝ => ⨍ y in ball x r, |f y - f x|) (𝓝[>] (0:ℝ)) (𝓝 0) := by
  -- First, the Lebesgue differentiation theorem along *closed* balls centred at `x`, which is
  -- available for uniformly locally doubling measures.
  have hclosed : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      Tendsto (fun r : ℝ => ⨍ y in closedBall x r, |f y - f x|) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    filter_upwards [IsUnifLocDoublingMeasure.ae_tendsto_average_norm_sub (μ := volume) hf 1]
      with x hx
    have hx' := hx (fun _ : ℝ => x) (fun r : ℝ => r)
      (tendsto_id : Tendsto (fun r : ℝ => r) (𝓝[>] (0:ℝ)) (𝓝[>] (0:ℝ))) ?_
    · simpa only [Real.norm_eq_abs] using hx'
    · filter_upwards [self_mem_nhdsWithin] with r hr
      simp only [one_mul, mem_closedBall, dist_self]
      exact hr.le
  -- Then replace closed balls by open balls; they only differ by the sphere, which is null.
  filter_upwards [hclosed] with x hx
  refine Tendsto.congr' ?_ hx
  filter_upwards [self_mem_nhdsWithin] with r hr
  refine setAverage_congr (f := fun y => |f y - f x|) ?_
  rw [ae_eq_set]
  refine ⟨?_, ?_⟩
  · rw [closedBall_sdiff_ball, Measure.addHaar_sphere_of_ne_zero volume x hr.ne']
  · rw [Set.sdiff_eq_empty.mpr ball_subset_closedBall, measure_empty]

end Commons.Measure.Lebesgue
