import Mathlib
import Submission.Commons.Measure.Integral.ball_integral_rpow_decay_comparable
import Submission.Commons.Measure.EuclideanSpace.volume_ball_succ_integral

namespace Commons.Analysis.Integral

open MeasureTheory

/-- The integrand `u ↦ (1 - u ^ 2) ^ (m / 2)` is continuous. -/
private lemma continuous_one_sub_sq_rpow (m : ℕ) :
    Continuous fun u : ℝ => (1 - u ^ 2) ^ ((m : ℝ) / 2) :=
  (continuous_const.sub (continuous_id.pow 2)).rpow_const
    (fun _ => Or.inr (by positivity))

private lemma intervalIntegrable_one_sub_sq_rpow (m : ℕ) (a b : ℝ) :
    IntervalIntegrable (fun u : ℝ => (1 - u ^ 2) ^ ((m : ℝ) / 2)) volume a b :=
  (continuous_one_sub_sq_rpow m).intervalIntegrable a b

/-- Evenness of the integrand gives `∫_{-1}^1 = 2 ∫_0^1`. -/
private lemma integral_one_sub_sq_rpow_even (m : ℕ) :
    (∫ u in (-1 : ℝ)..1, (1 - u ^ 2) ^ ((m : ℝ) / 2))
      = 2 * ∫ u in (0 : ℝ)..1, (1 - u ^ 2) ^ ((m : ℝ) / 2) := by
  have h1 := intervalIntegrable_one_sub_sq_rpow m (-1) 0
  have h2 := intervalIntegrable_one_sub_sq_rpow m 0 1
  rw [← intervalIntegral.integral_add_adjacent_intervals h1 h2]
  have hneg : (∫ u in (-1 : ℝ)..0, (1 - u ^ 2) ^ ((m : ℝ) / 2))
      = ∫ u in (0 : ℝ)..1, (1 - u ^ 2) ^ ((m : ℝ) / 2) := by
    have key := intervalIntegral.integral_comp_neg (a := (-1 : ℝ)) (b := 0)
      (fun u : ℝ => (1 - u ^ 2) ^ ((m : ℝ) / 2))
    simp only [neg_zero, neg_neg] at key
    rw [← key]
    apply intervalIntegral.integral_congr
    intro u _
    simp only
    rw [neg_sq]
  rw [hneg]; ring

/-- Scaling the interval integral. -/
private lemma integral_sq_sub_sq_rpow_eq (m : ℕ) {T : ℝ} (hT : 0 < T) :
    (∫ x in (0 : ℝ)..T, (T ^ 2 - x ^ 2) ^ ((m : ℝ) / 2))
      = T ^ (m + 1) * ∫ u in (0 : ℝ)..1, (1 - u ^ 2) ^ ((m : ℝ) / 2) := by
  have hscale : (∫ x in (0 : ℝ)..T, (T ^ 2 - x ^ 2) ^ ((m : ℝ) / 2))
      = T * ∫ u in (0 : ℝ)..1, (T ^ 2 - (T * u) ^ 2) ^ ((m : ℝ) / 2) := by
    have key := intervalIntegral.integral_comp_mul_add (a := (0 : ℝ)) (b := (1 : ℝ))
      (c := T) (d := (0 : ℝ)) (f := fun x : ℝ => (T ^ 2 - x ^ 2) ^ ((m : ℝ) / 2)) hT.ne'
    simp only [mul_zero, add_zero, mul_one, smul_eq_mul] at key
    rw [key, ← mul_assoc, mul_inv_cancel₀ hT.ne', one_mul]
  have hcongr : (∫ u in (0 : ℝ)..1, (T ^ 2 - (T * u) ^ 2) ^ ((m : ℝ) / 2))
      = ∫ u in (0 : ℝ)..1, T ^ m * (1 - u ^ 2) ^ ((m : ℝ) / 2) := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hu
    have hu0 : 0 ≤ u := hu.1
    have hu1 : u ≤ 1 := hu.2
    have h1mu : 0 ≤ 1 - u ^ 2 := by nlinarith [hu0, hu1]
    have hT2 : (0 : ℝ) ≤ T ^ 2 := sq_nonneg T
    show (T ^ 2 - (T * u) ^ 2) ^ ((m : ℝ) / 2) = T ^ m * (1 - u ^ 2) ^ ((m : ℝ) / 2)
    have hbase : T ^ 2 - (T * u) ^ 2 = T ^ 2 * (1 - u ^ 2) := by ring
    rw [hbase, Real.mul_rpow hT2 h1mu]
    rw [show (T ^ 2 : ℝ) ^ ((m : ℝ) / 2) = T ^ m by
      rw [show (T ^ 2 : ℝ) = T ^ (2 : ℝ) from (Real.rpow_natCast T 2).symm,
        ← Real.rpow_mul hT.le (2 : ℝ) ((m : ℝ) / 2)]
      rw [show (2 : ℝ) * ((m : ℝ) / 2) = (m : ℝ) by ring, Real.rpow_natCast]]
  rw [hscale, hcongr, intervalIntegral.integral_const_mul, pow_succ']; ring

theorem integral_sq_sub_sq_rpow (m : ℕ) {T : ℝ} (hT : 0 ≤ T) :
    (∫ x in (0:ℝ)..T, (T ^ 2 - x ^ 2) ^ ((m : ℝ) / 2))
      = T ^ (m + 1) * (MeasureTheory.volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (m + 1))) 1)).toReal
          / (2 * (MeasureTheory.volume (Metric.ball (0 : EuclideanSpace ℝ (Fin m)) 1)).toReal) := by
  rcases eq_or_lt_of_le hT with h0 | hpos
  · rw [← h0]; simp [zero_pow (Nat.succ_ne_zero m)]
  · have hVpos : (0 : ℝ) <
        (MeasureTheory.volume (Metric.ball (0 : EuclideanSpace ℝ (Fin m)) 1)).toReal :=
      Commons.Measure.Integral.volume_unitBall_euclidean_pos m
    have key : (∫ u in (0 : ℝ)..1, (1 - u ^ 2) ^ ((m : ℝ) / 2))
        = (MeasureTheory.volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (m + 1))) 1)).toReal
          / (2 * (MeasureTheory.volume (Metric.ball (0 : EuclideanSpace ℝ (Fin m)) 1)).toReal) := by
      have h1 : (MeasureTheory.volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (m + 1))) 1)).toReal
          = (∫ u in (-1 : ℝ)..1, (1 - u ^ 2) ^ ((m : ℝ) / 2))
            * (MeasureTheory.volume (Metric.ball (0 : EuclideanSpace ℝ (Fin m)) 1)).toReal :=
        Commons.Measure.EuclideanSpace.volume_ball_succ_integral m
      have h2 : (∫ u in (-1 : ℝ)..1, (1 - u ^ 2) ^ ((m : ℝ) / 2))
          = 2 * (∫ u in (0 : ℝ)..1, (1 - u ^ 2) ^ ((m : ℝ) / 2)) :=
        integral_one_sub_sq_rpow_even m
      rw [h1, h2]
      rw [show (2 * (∫ u in (0 : ℝ)..1, (1 - u ^ 2) ^ ((m : ℝ) / 2)) *
            (MeasureTheory.volume (Metric.ball (0 : EuclideanSpace ℝ (Fin m)) 1)).toReal)
          = (2 * (MeasureTheory.volume (Metric.ball (0 : EuclideanSpace ℝ (Fin m)) 1)).toReal)
            * (∫ u in (0 : ℝ)..1, (1 - u ^ 2) ^ ((m : ℝ) / 2)) by ring]
      rw [mul_div_cancel_left₀ _ (mul_ne_zero two_ne_zero hVpos.ne')]
    rw [mul_div_assoc, integral_sq_sub_sq_rpow_eq m hpos, key]

end Commons.Analysis.Integral
