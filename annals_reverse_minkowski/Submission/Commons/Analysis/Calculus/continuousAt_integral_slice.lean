import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis

namespace Commons.Analysis.Calculus

open MeasureTheory Set Real Filter
open scoped Real Topology InnerProductSpace

/-- Continuity of a slice integral `y ↦ ∫ z, Φ (z, y)` under a uniform integrable bound. -/
theorem continuousAt_integral_slice {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G]
    [FiniteDimensional ℝ G] [MeasurableSpace G] [BorelSpace G]
    (Φ : G × ℝ → ℝ) (y₀ : ℝ) (bound : G → ℝ)
    (hΦ : Continuous Φ) (hbound : Integrable bound)
    (hint : Integrable (fun z : G => Φ (z, y₀)))
    (hdom : ∀ z : G, ∀ y : ℝ, |y - y₀| < 1 → ‖Φ (z, y)‖ ≤ bound z) :
    ContinuousAt (fun y => ∫ z : G, Φ (z, y)) y₀ := by
  apply continuousAt_of_dominated (μ := volume) (bound := bound)
  · -- a.e.-strong measurability of each slice `z ↦ Φ (z, y)`
    filter_upwards with y
    exact (hΦ.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable
  · -- the uniform integrable bound on the neighbourhood `|y - y₀| < 1`
    filter_upwards [Metric.ball_mem_nhds y₀ one_pos] with y hy
    refine Eventually.of_forall (fun z => ?_)
    rw [Metric.mem_ball, Real.dist_eq] at hy
    exact hdom z y hy
  · exact hbound
  · -- continuity of each slice `y ↦ Φ (z, y)`
    filter_upwards with z
    exact (hΦ.comp (continuous_const.prodMk
      (continuous_id : Continuous (fun x : ℝ => x)))).continuousAt

end Commons.Analysis.Calculus