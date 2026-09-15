import Mathlib
import Submission.Commons.Analysis.Integral.integrable_of_log_le_lorentz

open MeasureTheory

namespace Commons.Analysis.Integral

/-- Elementary bound: `(|t|+3)^{1/2} ≤ 4^{1/2} (1+t²)^{1/4}`. -/
lemma rpow_half_abs_add_three_le (t : ℝ) :
    (|t| + 3) ^ ((1:ℝ)/2) ≤ (4:ℝ) ^ ((1:ℝ)/2) * (1 + t^2) ^ ((1:ℝ)/4) := by
  have h4 : |t| + 3 ≤ 4 * (1 + t^2) ^ ((1:ℝ)/2) := by
    rw [show (4:ℝ) * (1 + t^2) ^ ((1:ℝ)/2) = 4 * Real.sqrt (1 + t^2) from by
      rw [← Real.sqrt_eq_rpow]]
    have hsq : (|t| + 3)^2 ≤ (4 * Real.sqrt (1 + t^2))^2 := by
      have h4sq : (4 * Real.sqrt (1 + t^2))^2 = 16 * (1 + t^2) := by
        rw [mul_pow, Real.sq_sqrt (by positivity : (0:ℝ) ≤ 1 + t^2)]
        norm_num
      rw [h4sq]
      nlinarith [sq_abs t, sq_nonneg (|t| - 1/5), abs_nonneg t]
    have hle := sq_le_sq.mp hsq
    rwa [abs_of_nonneg (by positivity : (0:ℝ) ≤ |t| + 3),
         abs_of_nonneg (by positivity : (0:ℝ) ≤ 4 * Real.sqrt (1 + t^2))] at hle
  calc (|t| + 3) ^ ((1:ℝ)/2) ≤ (4 * (1 + t^2) ^ ((1:ℝ)/2)) ^ ((1:ℝ)/2) :=
        Real.rpow_le_rpow (by positivity) h4 (by norm_num)
    _ = (4:ℝ)^((1:ℝ)/2) * (1 + t^2)^((1:ℝ)/4) := by
        rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 4) (Real.rpow_nonneg (by positivity) _)]
        congr 1
        rw [← Real.rpow_mul (by positivity : (0:ℝ) ≤ 1 + t^2)]
        norm_num

/-- Elementary logarithmic bound: `log(|t|+2) + 1 ≤ (log 3 + 5) (1+t²)^{1/8}`. -/
lemma log_abs_add_two_add_one_le (t : ℝ) :
    Real.log (|t| + 2) + 1 ≤ (Real.log 3 + 5) * (1 + t^2) ^ ((1:ℝ)/8) := by
  set u : ℝ := 1 + t^2 with hu_def
  have hu_ge1 : 1 ≤ u := by rw [hu_def]; nlinarith [sq_nonneg t]
  have hu_pos : 0 < u := lt_of_lt_of_le one_pos hu_ge1
  have hu_nonneg : 0 ≤ u := le_of_lt hu_pos
  have hm_pos : 0 < |t| + 2 := by positivity
  have hsq : (|t| + 2)^2 ≤ 9 * u := by
    rw [hu_def]
    nlinarith [sq_abs t, sq_nonneg (|t| - 1/5), abs_nonneg t]
  have hsqrt9 : Real.sqrt (9:ℝ) = 3 := by
    rw [show (9:ℝ) = 3^2 by norm_num, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 3)]
  have hle : |t| + 2 ≤ 3 * u ^ ((1:ℝ)/2) := by
    have h1 : |t| + 2 ≤ Real.sqrt (9 * u) := by
      rw [← Real.sqrt_sq (by positivity : (0:ℝ) ≤ |t| + 2)]
      exact Real.sqrt_le_sqrt hsq
    rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 9)] at h1
    rw [hsqrt9] at h1
    rwa [Real.sqrt_eq_rpow] at h1
  have hlog_le : Real.log (|t| + 2) ≤ Real.log 3 + (1/2) * Real.log u := by
    have h := Real.log_le_log hm_pos hle
    rw [Real.log_mul (by norm_num : (3:ℝ) ≠ 0) (ne_of_gt (Real.rpow_pos_of_pos hu_pos _)),
        Real.log_rpow hu_pos] at h
    linarith [h]
  have hlogu : Real.log u ≤ 8 * u ^ ((1:ℝ)/8) := by
    have h := Real.log_le_rpow_div hu_nonneg (show (0:ℝ) < 1/8 by norm_num)
    have h2 : u ^ ((1:ℝ)/8) / (1/8) = 8 * u ^ ((1:ℝ)/8) := by rw [div_eq_mul_inv]; ring
    rwa [h2] at h
  have he_ge1 : 1 ≤ u ^ ((1:ℝ)/8) := Real.one_le_rpow hu_ge1 (by norm_num)
  have hlog3nn : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have hfinal : Real.log 3 + (1/2) * Real.log u + 1 ≤ (Real.log 3 + 5) * u ^ ((1:ℝ)/8) := by
    have hhalf : (1/2) * Real.log u ≤ 4 * u ^ ((1:ℝ)/8) := by linarith [hlogu]
    have hlog3le : Real.log 3 ≤ Real.log 3 * u ^ ((1:ℝ)/8) := by
      have := mul_le_mul_of_nonneg_left he_ge1 hlog3nn
      rwa [mul_one] at this
    nlinarith [hhalf, hlog3le, he_ge1]
  linarith [hlog_le, hfinal]

/-- The Green–Tao weight is nonnegative. -/
lemma uScaleHalf_nonneg (t : ℝ) :
    0 ≤ (|t| + 3) ^ ((1:ℝ)/2) * (Real.log (|t| + 2) + 1) / (1 + t^2) := by
  apply div_nonneg
  · apply mul_nonneg (Real.rpow_nonneg (by linarith [abs_nonneg t]) _)
    have : 0 ≤ Real.log (|t| + 2) := Real.log_nonneg (by linarith [abs_nonneg t])
    linarith
  · positivity

/-- Pointwise domination of the Green–Tao weight by a multiple of `(1+t²)^{-5/8}`. -/
lemma uScaleHalf_pointwise (t : ℝ) :
    (|t| + 3) ^ ((1:ℝ)/2) * (Real.log (|t| + 2) + 1) / (1 + t^2)
      ≤ ((4:ℝ) ^ ((1:ℝ)/2) * (Real.log 3 + 5)) * (1 + t^2) ^ (-((5:ℝ)/8)) := by
  have hu_pos : 0 < 1 + t^2 := by positivity
  have hsqrt := rpow_half_abs_add_three_le t
  have hlog := log_abs_add_two_add_one_le t
  have hnum_nonneg : 0 ≤ Real.log (|t| + 2) + 1 := by
    have : 0 ≤ Real.log (|t| + 2) := Real.log_nonneg (by linarith [abs_nonneg t])
    linarith
  have h4_nonneg : 0 ≤ (4:ℝ)^((1:ℝ)/2) := Real.rpow_nonneg (by norm_num) _
  calc
    (|t| + 3) ^ ((1:ℝ)/2) * (Real.log (|t| + 2) + 1) / (1 + t^2)
        = (|t| + 3) ^ ((1:ℝ)/2) * (Real.log (|t| + 2) + 1) * (1 + t^2)⁻¹ := by
          rw [div_eq_mul_inv]
    _ ≤ ((4:ℝ)^((1:ℝ)/2) * (1+t^2)^((1:ℝ)/4))
          * ((Real.log 3 + 5) * (1+t^2)^((1:ℝ)/8)) * (1+t^2)⁻¹ := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact mul_le_mul hsqrt hlog hnum_nonneg
            (mul_nonneg h4_nonneg (Real.rpow_nonneg (by positivity) _))
    _ = ((4:ℝ)^((1:ℝ)/2) * (Real.log 3 + 5))
          * ((1+t^2)^((1:ℝ)/4) * (1+t^2)^((1:ℝ)/8) * (1+t^2)⁻¹) := by ring
    _ = ((4:ℝ)^((1:ℝ)/2) * (Real.log 3 + 5)) * (1+t^2)^(-((5:ℝ)/8)) := by
          congr 1
          rw [← Real.rpow_neg_one (1+t^2), ← Real.rpow_add hu_pos, ← Real.rpow_add hu_pos]
          norm_num

/-- Continuity of the Green–Tao weight. -/
lemma uScaleHalf_continuous :
    Continuous (fun t : ℝ =>
      (|t| + 3) ^ ((1:ℝ)/2) * (Real.log (|t| + 2) + 1) / (1 + t^2)) := by
  have h1 : Continuous (fun t : ℝ => (|t| + 3) ^ ((1:ℝ)/2)) := by
    refine Continuous.rpow_const (continuous_abs.add continuous_const) ?_
    intro x; right; norm_num
  have h2 : Continuous (fun t : ℝ => Real.log (|t| + 2)) := by
    have hlin : Continuous (fun t : ℝ => |t| + 2) := continuous_abs.add continuous_const
    exact hlin.log (fun t => by positivity)
  have hden : Continuous (fun t : ℝ => (1 : ℝ) + t^2) := by fun_prop
  refine (h1.mul (h2.add continuous_const)).div hden ?_
  intro t
  have : 0 < (1:ℝ) + t^2 := by positivity
  exact ne_of_gt this

/-- The weight `t ↦ (|t|+3)^{1/2} (log(|t|+2)+1) / (1+t^2)` is integrable on `ℝ`, with an
explicit finite integral.  It dominates the `Γ₀ × Γ₀` Green–Tao double integral after using the
sharp bound `‖ζ(1+z+z')‖ ≤ C(|z.im|+|z'.im|+3)^{1/2}`.
Suggested route: `(|t|+3)^{1/2} ≤ c (1+t^2)^{1/4}` and `log(|t|+2)+1 ≤ c (1+t^2)^{1/8}`, so the
weight is `≤ c (1+t^2)^{-5/8}`, which is integrable since `5/4 > 1`
(`integrableOn_Ioi_rpow_iff`, `integral_Ioi_rpow_of_lt`, or `integrable_inv_one_add_sq`-style). -/
theorem uScaleHalf_integrable :
    ∃ K : ℝ, 0 < K ∧
      MeasureTheory.Integrable (fun t : ℝ => (|t| + 3) ^ ((1:ℝ)/2) * (Real.log (|t| + 2) + 1) / (1 + t ^ 2)) ∧
      (∫ t : ℝ, (|t| + 3) ^ ((1:ℝ)/2) * (Real.log (|t| + 2) + 1) / (1 + t ^ 2)) ≤ K := by
  have hbase : MeasureTheory.Integrable (fun t : ℝ => (1 + t^2) ^ (-((5:ℝ)/8))) :=
    integrable_one_add_sq_rpow_neg ((5:ℝ)/8) (by norm_num)
  have hdom : MeasureTheory.Integrable
      (fun t : ℝ => ((4:ℝ)^((1:ℝ)/2) * (Real.log 3 + 5)) * (1 + t^2) ^ (-((5:ℝ)/8))) :=
    hbase.const_mul _
  have hint : MeasureTheory.Integrable
      (fun t : ℝ => (|t| + 3) ^ ((1:ℝ)/2) * (Real.log (|t| + 2) + 1) / (1 + t ^ 2)) := by
    refine hdom.mono' uScaleHalf_continuous.aestronglyMeasurable ?_
    filter_upwards with t
    rw [Real.norm_of_nonneg (uScaleHalf_nonneg t)]
    exact uScaleHalf_pointwise t
  refine ⟨(∫ t : ℝ, (|t| + 3) ^ ((1:ℝ)/2) * (Real.log (|t| + 2) + 1) / (1 + t ^ 2)) + 1,
    ?_, hint, ?_⟩
  · have hnn : 0 ≤ ∫ t : ℝ, (|t| + 3) ^ ((1:ℝ)/2) * (Real.log (|t| + 2) + 1) / (1 + t ^ 2) :=
      integral_nonneg (fun t => uScaleHalf_nonneg t)
    linarith
  · linarith

end Commons.Analysis.Integral
