import Mathlib
import Submission.Commons.Measure.Kernel.setAverage_abs_integral_mul_kernel_le2
import Submission.Commons.Measure.Kernel.integral_measure_closedBall_le
import Submission.Commons.Measure.EuclideanSpace.volume_ball_ratio_mul_pow_le

namespace Commons.Measure.Kernel

open MeasureTheory Metric Set Filter Function in
open scoped Topology ENNReal RealInnerProductSpace InnerProductSpace Convolution in
theorem setAverage_integral_closedBall_le {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {x₀ : EuclideanSpace ℝ (Fin n)} {ε E₀ R : ℝ}
    (hf : LocallyIntegrable f volume) (hε : 0 < ε) (hR : 0 < R) (hεR : ε ≤ R)
    (hE0 : 0 ≤ E₀)
    (hE : ∀ s' ∈ Set.Ioc (0:ℝ) R, (∫ w in Metric.ball x₀ s', |f w|) ≤ E₀ * s' ^ n)
    {s : ℝ} (hs : 0 < s) (hRs : s + ε ≤ R) :
    (⨍ z in Metric.ball (0 : EuclideanSpace ℝ (Fin n)) s,
        (∫ τ in Metric.closedBall (x₀ + z) ε, |f τ|)) ≤ 2 ^ n * E₀ * ε ^ n := by
  classical
  set k : EuclideanSpace ℝ (Fin n) → ℝ :=
    (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) ε).indicator (fun _ => (1 : ℝ)) with hk_def
  set G : EuclideanSpace ℝ (Fin n) → ℝ :=
    fun z => ∫ τ, k (x₀ + z - τ) * |f τ| with hG
  have hk_nonneg : ∀ t, 0 ≤ k t := by
    intro t
    rw [hk_def]
    by_cases h : t ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) ε
    · simp [Set.indicator_of_mem h]
    · simp [Set.indicator_of_notMem h]
  have hk_le : ∀ t, k t ≤ 1 := by
    intro t
    rw [hk_def]
    by_cases h : t ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) ε
    · simp [Set.indicator_of_mem h]
    · simp [Set.indicator_of_notMem h]
  have hk_supp : ∀ t, k t ≠ 0 → t ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) ε := by
    intro t ht
    by_contra h
    exact ht (by rw [hk_def, Set.indicator_of_notMem h])
  have hg : LocallyIntegrable (fun τ : EuclideanSpace ℝ (Fin n) => |f τ|) volume := by
    have h := (hf.locallyIntegrableOn Set.univ).norm
    rw [locallyIntegrableOn_univ] at h
    simpa only [Real.norm_eq_abs] using h
  have hE' : ∀ s' ∈ Set.Ioc (0 : ℝ) R,
      (∫ w in Metric.ball x₀ s', |(|f w|)|) ≤ E₀ * s' ^ n := by
    intro s' hs'
    simpa using hE s' hs'
  have hmain : (⨍ z in Metric.ball (0 : EuclideanSpace ℝ (Fin n)) s, |G z|)
      ≤ 2 ^ n * 1 * E₀ * ε ^ n := by
    rw [hG]
    exact setAverage_abs_integral_mul_kernel_le2 (n := n) (k := k)
      (f := fun τ : EuclideanSpace ℝ (Fin n) => |f τ|) (x₀ := x₀) (ε := ε) (C := 1) (R := R)
      (E₀ := E₀) hk_nonneg hk_le (by norm_num) hε hR hεR hk_supp hg hE0 hE' hs hRs
  have hInt : ∀ z : EuclideanSpace ℝ (Fin n),
      (∫ τ, k (x₀ + z - τ) * |f τ|) = ∫ τ in Metric.closedBall (x₀ + z) ε, |f τ| := by
    intro z
    have hpt : ∀ τ : EuclideanSpace ℝ (Fin n),
        k (x₀ + z - τ) * |f τ|
          = (Metric.closedBall (x₀ + z) ε).indicator (fun τ => |f τ|) τ := by
      intro τ
      rw [hk_def]
      have hiff : (x₀ + z - τ ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) ε)
          ↔ (τ ∈ Metric.closedBall (x₀ + z) ε) := by
        simp only [Metric.mem_closedBall, dist_eq_norm, sub_zero]
        rw [show x₀ + z - τ = -(τ - (x₀ + z)) by abel, norm_neg]
      by_cases hmem : τ ∈ Metric.closedBall (x₀ + z) ε
      · rw [Set.indicator_of_mem (hiff.mpr hmem), Set.indicator_of_mem hmem]
        simp
      · rw [Set.indicator_of_notMem (fun hc => hmem (hiff.mp hc)),
          Set.indicator_of_notMem hmem]
        simp
    rw [integral_congr_ae (Eventually.of_forall hpt),
      MeasureTheory.integral_indicator measurableSet_closedBall]
  have hkey : ∀ z : EuclideanSpace ℝ (Fin n),
      |G z| = ∫ τ in Metric.closedBall (x₀ + z) ε, |f τ| := by
    intro z
    rw [hG]
    beta_reduce
    rw [hInt z]
    exact abs_of_nonneg (integral_nonneg fun τ => abs_nonneg _)
  have havg : (⨍ z in Metric.ball (0 : EuclideanSpace ℝ (Fin n)) s,
        (∫ τ in Metric.closedBall (x₀ + z) ε, |f τ|))
      = (⨍ z in Metric.ball (0 : EuclideanSpace ℝ (Fin n)) s, |G z|) := by
    refine MeasureTheory.setAverage_congr_fun Metric.isOpen_ball.measurableSet ?_
    filter_upwards with z _
    exact (hkey z).symm
  rw [havg]
  convert hmain using 1
  ring

end Commons.Measure.Kernel
