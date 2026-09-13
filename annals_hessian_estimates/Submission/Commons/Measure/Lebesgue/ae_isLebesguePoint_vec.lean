import Mathlib

namespace Commons.Measure.Lebesgue

open MeasureTheory Metric Set Filter Function
open scoped BigOperators ENNReal Topology RealInnerProductSpace InnerProductSpace Convolution

/-- In Euclidean space, an open ball and the corresponding closed ball only differ by the sphere,
which has measure zero (for a nonzero radius). -/
lemma ball_ae_eq_closedBall_volume {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) {r : ℝ} (hr : r ≠ 0) :
    ball x r =ᵐ[volume] closedBall x r := by
  rw [ae_eq_set]
  refine ⟨?_, ?_⟩
  · rw [sdiff_eq_empty.mpr ball_subset_closedBall, measure_empty]
  · rw [closedBall_sdiff_ball]
    exact Measure.addHaar_sphere_of_ne_zero volume x hr

open MeasureTheory Metric Set Filter Function in
open scoped BigOperators ENNReal Topology RealInnerProductSpace InnerProductSpace Convolution in
theorem ae_isLebesguePoint_vec {n : ℕ} {G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hG : LocallyIntegrable G volume) :
    ∀ᵐ x ∂volume,
      Tendsto (fun r : ℝ => ⨍ y in ball x r, ‖G y - G x‖) (𝓝[>] (0:ℝ)) (𝓝 0) := by
  have h := (Besicovitch.vitaliFamily
    (volume : Measure (EuclideanSpace ℝ (Fin n)))).ae_tendsto_average_norm_sub hG
  filter_upwards [h] with x hx
  refine (hx.comp (Besicovitch.tendsto_filterAt volume x)).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with r hr
  show ⨍ y in (fun r => closedBall x r) r, ‖G y - G x‖ = ⨍ y in ball x r, ‖G y - G x‖
  exact (setAverage_congr (ball_ae_eq_closedBall_volume x (ne_of_gt hr))).symm

end Commons.Measure.Lebesgue
