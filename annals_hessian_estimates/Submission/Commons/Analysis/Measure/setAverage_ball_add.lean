import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Measure.Haar.OfBasis

namespace Commons.Analysis.Measure

open MeasureTheory Metric Set Filter Function
open scoped Topology ENNReal

/-- Averaging a function against a pushforward measure equals averaging the precomposition
with the map, for any measurable embedding. -/
theorem average_map_of_measurableEmbedding {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {T : α → β} (hemb : MeasurableEmbedding T) (g : β → ℝ) :
    average (μ.map T) g = average μ (fun x => g (T x)) := by
  have hvol' : (μ.map T).real univ = μ.real univ := by
    rw [Measure.real_def, Measure.real_def,
      Measure.map_apply hemb.measurable MeasurableSet.univ, preimage_univ]
  rw [average_eq, average_eq, hvol', hemb.integral_map]

open MeasureTheory Metric Set Filter Function in
open scoped Topology ENNReal in
theorem setAverage_ball_add {n : ℕ} (x₀ : EuclideanSpace ℝ (Fin n)) (r : ℝ)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) :
    (⨍ y in Metric.ball x₀ r, f y)
      = ⨍ w in Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r, f (x₀ + w) := by
  let T : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) := fun w => x₀ + w
  have hT : MeasurePreserving T volume volume := measurePreserving_add_left volume x₀
  have hemb : MeasurableEmbedding T :=
    (Homeomorph.addLeft x₀).toMeasurableEquiv.measurableEmbedding
  have hpre : T ⁻¹' ball x₀ r = ball 0 r := by
    ext w
    simp only [T, mem_preimage, mem_ball, dist_eq_norm]
    rw [add_sub_cancel_left, sub_zero]
  have hmap : (volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (ball x₀ r)
      = (volume.restrict (ball (0 : EuclideanSpace ℝ (Fin n)) r)).map T := by
    rw [← hpre, ← Measure.restrict_map hT.measurable isOpen_ball.measurableSet, hT.map_eq]
  rw [hmap]
  exact average_map_of_measurableEmbedding hemb f

end Commons.Analysis.Measure