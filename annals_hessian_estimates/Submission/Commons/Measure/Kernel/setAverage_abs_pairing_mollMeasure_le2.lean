import Mathlib
import Submission.Commons.Measure.VectorMeasure.pairing_abs_le
import Submission.Commons.Measure.Mollification.abs_pairing_le_of_support_subset
import Submission.Commons.Measure.Kernel.aemeasurable_toReal_measure_closedBall
import Submission.Commons.Measure.Kernel.integral_measure_closedBall_le
import Submission.Commons.Measure.EuclideanSpace.volume_ball_ratio_mul_pow_le

namespace Commons.Measure.Kernel

open MeasureTheory Metric Set Filter Function in
open scoped Topology ENNReal RealInnerProductSpace InnerProductSpace Convolution in
theorem setAverage_abs_pairing_mollMeasure_le2 {n : ℕ}
    {k : EuclideanSpace ℝ (Fin n) → ℝ} {x₀ : EuclideanSpace ℝ (Fin n)} {ε C R E₀ : ℝ}
    (hk : ∀ t, 0 ≤ k t) (hC : ∀ t, k t ≤ C) (hC0 : 0 ≤ C)
    (hε : 0 < ε) (hR : 0 < R) (hεR : ε ≤ R)
    (hks : ∀ t, k t ≠ 0 → t ∈ Metric.closedBall 0 ε)
    (ν : SignedMeasure (EuclideanSpace ℝ (Fin n))) (hE0 : 0 ≤ E₀)
    (hE : ∀ s' ∈ Set.Ioc (0:ℝ) R,
        (ν.totalVariation (Metric.closedBall x₀ s')).toReal ≤ E₀ * s' ^ n)
    {s : ℝ} (hs : 0 < s) (hRs : s + ε ≤ R) :
    (⨍ z in Metric.ball (0 : EuclideanSpace ℝ (Fin n)) s,
        |∫ᵛ τ, k (x₀ + z - τ) ∂•ν|) ≤ 2 ^ n * C * E₀ * ε ^ n := by
  classical
  set B : Set (EuclideanSpace ℝ (Fin n)) := Metric.ball (0 : EuclideanSpace ℝ (Fin n)) s with hB
  have hBmeas : MeasurableSet B := by rw [hB]; exact Metric.isOpen_ball.measurableSet
  have hBfin : volume B ≠ ∞ := by
    rw [hB]
    exact (lt_of_le_of_lt (measure_mono Metric.ball_subset_closedBall)
      (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin n)) s).measure_lt_top).ne
  have hBpos : 0 < volume.real B := by
    rw [Measure.real_def, hB]
    exact ENNReal.toReal_pos (measure_ball_pos volume (0 : EuclideanSpace ℝ (Fin n)) hs).ne' hBfin
  have hpt : ∀ z : EuclideanSpace ℝ (Fin n),
      |∫ᵛ τ, k (x₀ + z - τ) ∂•ν|
        ≤ C * (ν.totalVariation (Metric.closedBall (x₀ + z) ε)).toReal :=
    fun z => Commons.Measure.Mollification.abs_pairing_le_of_support_subset hk hC hC0 hks ν (x₀ + z)
  have hsubset : ∀ z ∈ B, Metric.closedBall (x₀ + z) ε ⊆ Metric.closedBall x₀ (s + ε) := by
    intro z hz τ hτ
    have hz' : z ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) s := by rwa [hB] at hz
    have hz2 : ‖z‖ < s := by rwa [Metric.mem_ball, dist_zero_right] at hz'
    rw [Metric.mem_closedBall, dist_eq_norm] at hτ ⊢
    have hτ' : ‖τ - x₀ - z‖ ≤ ε := by
      rwa [show τ - (x₀ + z) = τ - x₀ - z by abel] at hτ
    have h2 : ‖τ - x₀‖ ≤ ‖τ - x₀ - z‖ + ‖z‖ := by
      calc ‖τ - x₀‖ = ‖(τ - x₀ - z) + z‖ := congrArg (fun w => ‖w‖) (by abel)
        _ ≤ ‖τ - x₀ - z‖ + ‖z‖ := norm_add_le _ _
    linarith
  have hKle : ∀ z ∈ B,
      (ν.totalVariation (Metric.closedBall (x₀ + z) ε)).toReal ≤ E₀ * (s + ε) ^ n := by
    intro z hz
    have h1 : ν.totalVariation (Metric.closedBall (x₀ + z) ε)
        ≤ ν.totalVariation (Metric.closedBall x₀ (s + ε)) := measure_mono (hsubset z hz)
    exact (ENNReal.toReal_mono (measure_ne_top _ _) h1).trans (hE (s + ε) ⟨by linarith, hRs⟩)
  rw [MeasureTheory.setAverage_eq, smul_eq_mul, inv_mul_le_iff₀ hBpos]
  by_cases hsε : s ≤ ε
  · have hbnd : ∀ z ∈ B, |∫ᵛ τ, k (x₀ + z - τ) ∂•ν| ≤ 2 ^ n * C * E₀ * ε ^ n := by
      intro z hz
      have hstep : |∫ᵛ τ, k (x₀ + z - τ) ∂•ν| ≤ C * (E₀ * (s + ε) ^ n) :=
        (hpt z).trans (mul_le_mul_of_nonneg_left (hKle z hz) hC0)
      have h2 : (s + ε) ^ n ≤ (2 * ε) ^ n := pow_le_pow_left₀ (by linarith) (by linarith) n
      calc |∫ᵛ τ, k (x₀ + z - τ) ∂•ν| ≤ C * (E₀ * (s + ε) ^ n) := hstep
        _ ≤ C * (E₀ * (2 * ε) ^ n) := by
            apply mul_le_mul_of_nonneg_left _ hC0
            exact mul_le_mul_of_nonneg_left h2 hE0
        _ = 2 ^ n * C * E₀ * ε ^ n := by rw [mul_pow]; ring
    calc ∫ z in B, |∫ᵛ τ, k (x₀ + z - τ) ∂•ν|
        ≤ ∫ z in B, (2 ^ n * C * E₀ * ε ^ n) := by
          apply integral_mono_of_nonneg
          · filter_upwards with z; exact abs_nonneg _
          · exact Measure.integrableOn_of_bounded hBfin aestronglyMeasurable_const
              (M := ‖2 ^ n * C * E₀ * ε ^ n‖) (Filter.Eventually.of_forall (fun z => le_refl _))
          · filter_upwards [MeasureTheory.ae_restrict_mem hBmeas] with z hz; exact hbnd z hz
      _ = (2 ^ n * C * E₀ * ε ^ n) * volume.real B := by
          rw [integral_const, MeasureTheory.measureReal_restrict_apply_univ, smul_eq_mul, mul_comm]
      _ = volume.real B * (2 ^ n * C * E₀ * ε ^ n) := by ring
  · rw [not_le] at hsε
    have hKae : AEMeasurable (fun z : EuclideanSpace ℝ (Fin n) =>
        (ν.totalVariation (Metric.closedBall (x₀ + z) ε)).toReal) volume :=
      Commons.Measure.Kernel.aemeasurable_toReal_measure_closedBall ν.totalVariation x₀ ε
    have hK_int : Integrable (fun z : EuclideanSpace ℝ (Fin n) =>
        (ν.totalVariation (Metric.closedBall (x₀ + z) ε)).toReal) (volume.restrict B) :=
      Measure.integrableOn_of_bounded hBfin hKae.aestronglyMeasurable (M := E₀ * (s + ε) ^ n)
        (by filter_upwards [MeasureTheory.ae_restrict_mem hBmeas] with z hz
            rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
            exact hKle z hz)
    have hKint : ∫ z in B, (ν.totalVariation (Metric.closedBall (x₀ + z) ε)).toReal ≤
        (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) ε)).toReal * (E₀ * (s + ε) ^ n) := by
      have h := integral_measure_closedBall_le (ν.totalVariation) (x₀ := x₀) hs hε
      rw [← hB] at h
      refine h.trans ?_
      exact mul_le_mul_of_nonneg_left (hE (s + ε) ⟨by linarith, hRs⟩) ENNReal.toReal_nonneg
    have hVratio := Commons.Measure.EuclideanSpace.volume_ball_ratio_mul_pow_le
      (n := n) hε hs (le_of_lt hsε)
    calc ∫ z in B, |∫ᵛ τ, k (x₀ + z - τ) ∂•ν|
        ≤ C * ∫ z in B, (ν.totalVariation (Metric.closedBall (x₀ + z) ε)).toReal := by
          rw [← MeasureTheory.integral_const_mul]
          apply integral_mono_of_nonneg
          · filter_upwards with z; exact abs_nonneg _
          · exact hK_int.const_mul C
          · filter_upwards with z; exact hpt z
      _ ≤ C * ((volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) ε)).toReal
              * (E₀ * (s + ε) ^ n)) :=
          mul_le_mul_of_nonneg_left hKint hC0
      _ ≤ volume.real B * (2 ^ n * C * E₀ * ε ^ n) := by
          calc C * ((volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) ε)).toReal
                  * (E₀ * (s + ε) ^ n))
              = C * E₀ * ((volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) ε)).toReal
                  * (s + ε) ^ n) := by ring
            _ ≤ C * E₀ * (volume.real B * (2 ^ n * ε ^ n)) :=
                mul_le_mul_of_nonneg_left hVratio (mul_nonneg hC0 hE0)
            _ = volume.real B * (2 ^ n * C * E₀ * ε ^ n) := by ring

end Commons.Measure.Kernel
