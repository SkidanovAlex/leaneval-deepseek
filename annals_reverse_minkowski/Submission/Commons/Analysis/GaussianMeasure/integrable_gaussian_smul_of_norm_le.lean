import Mathlib
import Submission.Commons.Analysis.Asymptotics.integrable_pow_mul_exp_neg_sq

namespace Commons.Analysis.GaussianMeasure

theorem integrable_gaussian_smul_of_norm_le {N n : ℕ}
    {Φ : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin n)} (hΦc : Continuous Φ)
    {A : ℝ} (hA : 0 ≤ A) {D : ℕ} (hΦ : ∀ y, ‖Φ y‖ ≤ A * (1 + ‖y‖) ^ D)
    (a : ℝ) (ha : 0 < a) (c : EuclideanSpace ℝ (Fin N)) :
    MeasureTheory.Integrable
      (fun y : EuclideanSpace ℝ (Fin N) => Real.exp (-a * ‖y - c‖ ^ 2) • Φ y)
      MeasureTheory.volume := by
  have hbase : MeasureTheory.Integrable
      (fun y : EuclideanSpace ℝ (Fin N) =>
        (1 + ‖y‖) ^ D * Real.exp (-(a / 2) * ‖y‖ ^ 2)) MeasureTheory.volume :=
    Commons.Analysis.Asymptotics.integrable_pow_mul_exp_neg_sq (a / 2) (by linarith) D
  have hg : MeasureTheory.Integrable
      (fun y : EuclideanSpace ℝ (Fin N) =>
        (A * Real.exp (a * ‖c‖ ^ 2)) *
          ((1 + ‖y‖) ^ D * Real.exp (-(a / 2) * ‖y‖ ^ 2))) MeasureTheory.volume :=
    hbase.const_mul _
  have hmeas : MeasureTheory.AEStronglyMeasurable
      (fun y : EuclideanSpace ℝ (Fin N) => Real.exp (-a * ‖y - c‖ ^ 2) • Φ y)
      MeasureTheory.volume := by
    apply Continuous.aestronglyMeasurable
    fun_prop
  refine MeasureTheory.Integrable.mono' hg hmeas ?_
  filter_upwards with y
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have hquad : (1 / 2 : ℝ) * ‖y‖ ^ 2 ≤ ‖y - c‖ ^ 2 + ‖c‖ ^ 2 := by
    have h1 : ‖y‖ ≤ ‖y - c‖ + ‖c‖ := by
      calc ‖y‖ = ‖(y - c) + c‖ := by rw [sub_add_cancel]
        _ ≤ ‖y - c‖ + ‖c‖ := norm_add_le _ _
    have h2 : ‖y‖ ^ 2 ≤ (‖y - c‖ + ‖c‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h1 2
    have h3 : (‖y - c‖ + ‖c‖) ^ 2 ≤ 2 * (‖y - c‖ ^ 2 + ‖c‖ ^ 2) := add_sq_le
    linarith
  have hexp : Real.exp (-a * ‖y - c‖ ^ 2)
      ≤ Real.exp (a * ‖c‖ ^ 2) * Real.exp (-(a / 2) * ‖y‖ ^ 2) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have := mul_le_mul_of_nonneg_left hquad ha.le
    nlinarith [this]
  have hΦb := hΦ y
  have hA2 : (0 : ℝ) ≤ A * (1 + ‖y‖) ^ D :=
    mul_nonneg hA (pow_nonneg (by positivity) _)
  calc Real.exp (-a * ‖y - c‖ ^ 2) * ‖Φ y‖
      ≤ Real.exp (-a * ‖y - c‖ ^ 2) * (A * (1 + ‖y‖) ^ D) :=
        mul_le_mul_of_nonneg_left hΦb (Real.exp_pos _).le
    _ ≤ (Real.exp (a * ‖c‖ ^ 2) * Real.exp (-(a / 2) * ‖y‖ ^ 2)) * (A * (1 + ‖y‖) ^ D) :=
        mul_le_mul_of_nonneg_right hexp hA2
    _ = (A * Real.exp (a * ‖c‖ ^ 2)) *
          ((1 + ‖y‖) ^ D * Real.exp (-(a / 2) * ‖y‖ ^ 2)) := by ring

end Commons.Analysis.GaussianMeasure
