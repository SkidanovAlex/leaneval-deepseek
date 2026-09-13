import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.VectorMeasure.Decomposition.Jordan
import Submission.Commons.Measure.Kernel.setAverage_abs_pairing_mollMeasure_le2
import Submission.Commons.Measure.Kernel.integral_measure_closedBall_le
import Submission.Commons.Measure.EuclideanSpace.volume_ball_ratio_mul_pow_le

namespace Commons.Measure.Kernel

open MeasureTheory Metric Set Filter Function in
open scoped Topology ENNReal RealInnerProductSpace InnerProductSpace Convolution in
/-- Average estimate for the total variation of a signed measure on moving closed balls.

Let `ν` be a signed measure on `ℝⁿ` whose total variation grows at most like `E₀ · r ^ n` on balls
of radius `r ≤ R` centred at `x₀`.  Then, for any `s > 0` with `s + ε ≤ R`, the average over the
ball of radius `s` around the origin of the total variation of `ν` on the ball of radius `ε`
around `x₀ + z` is at most `2 ^ n · E₀ · ε ^ n`.

The proof splits according to whether `s ≤ ε`: for `s ≤ ε` every closed ball
`closedBall (x₀ + z) ε` is contained in `closedBall x₀ (s + ε) ⊆ closedBall x₀ (2ε)` and we use the
hypothesis pointwise.  For `ε < s` we use the (Fubini/Tonelli) identity
`∫_{ball 0 s} μ (closedBall (x₀ + z) ε) dz = ∫ τ, |ball 0 s ∩ ball (τ - x₀) ε| dμ τ`, whose
integrand is bounded by `ε`-ball volume and is supported in `closedBall x₀ (s + ε)`; this gives
`volume.real (ball 0 ε) · μ (closedBall x₀ (s + ε))`, and the volume ratio
`volume.real (ball 0 ε) / volume.real (ball 0 s) = (ε/s) ^ n` together with `s ≥ ε` closes the
estimate. -/
theorem setAverage_toReal_measure_closedBall_le {n : ℕ}
    (ν : SignedMeasure (EuclideanSpace ℝ (Fin n))) {x₀ : EuclideanSpace ℝ (Fin n)}
    {ε E₀ R : ℝ}
    (hε : 0 < ε) (hR : 0 < R) (hεR : ε ≤ R) (hE0 : 0 ≤ E₀)
    (hE : ∀ s' ∈ Set.Ioc (0:ℝ) R,
        (ν.totalVariation (Metric.closedBall x₀ s')).toReal ≤ E₀ * s' ^ n)
    {s : ℝ} (hs : 0 < s) (hRs : s + ε ≤ R) :
    (⨍ z in Metric.ball (0 : EuclideanSpace ℝ (Fin n)) s,
        (ν.totalVariation (Metric.closedBall (x₀ + z) ε)).toReal) ≤ 2 ^ n * E₀ * ε ^ n := by
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
  · have hbnd : ∀ z ∈ B,
        (ν.totalVariation (Metric.closedBall (x₀ + z) ε)).toReal ≤ 2 ^ n * E₀ * ε ^ n := by
      intro z hz
      have hstep : (ν.totalVariation (Metric.closedBall (x₀ + z) ε)).toReal
          ≤ E₀ * (s + ε) ^ n := hKle z hz
      have h2 : (s + ε) ^ n ≤ (2 * ε) ^ n := pow_le_pow_left₀ (by linarith) (by linarith) n
      calc (ν.totalVariation (Metric.closedBall (x₀ + z) ε)).toReal
          ≤ E₀ * (s + ε) ^ n := hstep
        _ ≤ E₀ * (2 * ε) ^ n := mul_le_mul_of_nonneg_left h2 hE0
        _ = 2 ^ n * E₀ * ε ^ n := by rw [mul_pow]; ring
    calc ∫ z in B, (ν.totalVariation (Metric.closedBall (x₀ + z) ε)).toReal
        ≤ ∫ z in B, (2 ^ n * E₀ * ε ^ n) := by
          apply integral_mono_of_nonneg
          · filter_upwards with z; exact ENNReal.toReal_nonneg
          · exact Measure.integrableOn_of_bounded hBfin aestronglyMeasurable_const
              (M := ‖2 ^ n * E₀ * ε ^ n‖) (Filter.Eventually.of_forall (fun z => le_refl _))
          · filter_upwards [MeasureTheory.ae_restrict_mem hBmeas] with z hz; exact hbnd z hz
      _ = (2 ^ n * E₀ * ε ^ n) * volume.real B := by
          rw [integral_const, MeasureTheory.measureReal_restrict_apply_univ, smul_eq_mul, mul_comm]
      _ = volume.real B * (2 ^ n * E₀ * ε ^ n) := by ring
  · rw [not_le] at hsε
    have hKint : ∫ z in B, (ν.totalVariation (Metric.closedBall (x₀ + z) ε)).toReal ≤
        (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) ε)).toReal * (E₀ * (s + ε) ^ n) := by
      have h := integral_measure_closedBall_le (ν.totalVariation) (x₀ := x₀) hs hε
      rw [← hB] at h
      refine h.trans ?_
      exact mul_le_mul_of_nonneg_left (hE (s + ε) ⟨by linarith, hRs⟩) ENNReal.toReal_nonneg
    have hVratio := Commons.Measure.EuclideanSpace.volume_ball_ratio_mul_pow_le
      (n := n) hε hs (le_of_lt hsε)
    calc ∫ z in B, (ν.totalVariation (Metric.closedBall (x₀ + z) ε)).toReal
        ≤ (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) ε)).toReal * (E₀ * (s + ε) ^ n) :=
          hKint
      _ = E₀ * ((volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) ε)).toReal * (s + ε) ^ n) := by
          ring
      _ ≤ E₀ * (volume.real B * (2 ^ n * ε ^ n)) :=
          mul_le_mul_of_nonneg_left hVratio hE0
      _ = volume.real B * (2 ^ n * E₀ * ε ^ n) := by ring

end Commons.Measure.Kernel