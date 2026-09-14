import Mathlib.Analysis.Calculus.BumpFunction.Convolution

namespace Commons.Measure.Mollification

open MeasureTheory Metric Set Filter Function in
open scoped Topology ENNReal RealInnerProductSpace InnerProductSpace Convolution in
theorem tendsto_integral_mul_bump {n : ℕ} {ψ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hψ : Continuous ψ)
    {ι : Type*} {k : ι → ContDiffBump (0 : EuclideanSpace ℝ (Fin n))} {l : Filter ι}
    (h : Tendsto (fun i => (k i).rOut) l (𝓝 0)) (t : EuclideanSpace ℝ (Fin n)) :
    Tendsto (fun i => ∫ z, ψ z * ((k i).normed volume) (z - t)) l (𝓝 (ψ t)) := by
  have key : ∀ i, (∫ z, ψ z * ((k i).normed volume) (z - t))
      = ((k i).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ψ) t := by
    intro i
    rw [MeasureTheory.convolution_lsmul_swap]
    apply integral_congr_ae
    filter_upwards with z
    have hneg : ((k i).normed volume) (t - z) = ((k i).normed volume) (z - t) := by
      rw [show t - z = -(z - t) by rw [neg_sub]]
      exact ContDiffBump.normed_neg (k i) (z - t)
    rw [hneg, smul_eq_mul, mul_comm]
  rw [funext key]
  exact ContDiffBump.convolution_tendsto_right_of_continuous (μ := volume) h hψ t

end Commons.Measure.Mollification