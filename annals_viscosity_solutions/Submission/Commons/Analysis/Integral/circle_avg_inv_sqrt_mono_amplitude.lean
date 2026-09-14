import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Commons.Analysis.Asymptotic.half_sum_rpow_neg_antitone

namespace Commons.Analysis.Integral

open MeasureTheory Set Real
open scoped Interval

private lemma continuous_add_cos_rpow {p A B : ℝ} (hB : 0 ≤ B) (hBA : B < A) :
    Continuous fun θ : ℝ => (A + B * Real.cos θ) ^ (-p) := by
  have hpos : ∀ θ : ℝ, 0 < A + B * Real.cos θ := fun θ => by
    have h := mul_le_mul_of_nonneg_left (Real.neg_one_le_cos θ) hB
    nlinarith
  exact (continuous_const.add (continuous_const.mul Real.continuous_cos)).rpow_const
    (fun θ => Or.inl (ne_of_gt (hpos θ)))

private lemma continuous_sub_cos_rpow {p A B : ℝ} (hB : 0 ≤ B) (hBA : B < A) :
    Continuous fun θ : ℝ => (A - B * Real.cos θ) ^ (-p) := by
  have hpos : ∀ θ : ℝ, 0 < A - B * Real.cos θ := fun θ => by
    have h := mul_le_mul_of_nonneg_left (Real.cos_le_one θ) hB
    nlinarith
  exact (continuous_const.sub (continuous_const.mul Real.continuous_cos)).rpow_const
    (fun θ => Or.inl (ne_of_gt (hpos θ)))

/-- Symmetrisation of the circle average of `θ ↦ (A + B cos θ) ^ (-p)`:
it equals twice the integral over `[0, π/2]` of the symmetrised integrand
`(A + B cos θ) ^ (-p) + (A - B cos θ) ^ (-p)`. -/
private lemma integral_cos_rpow_neg_symm {p A B : ℝ} (hB : 0 ≤ B)
    (hBA : B < A) :
    (∫ θ in (0)..(2 * Real.pi), (A + B * Real.cos θ) ^ (-p))
      = 2 * ∫ θ in (0)..(Real.pi / 2),
          ((A + B * Real.cos θ) ^ (-p) + (A - B * Real.cos θ) ^ (-p)) := by
  have hc1 := continuous_add_cos_rpow (p := p) hB hBA
  have hc2 := continuous_sub_cos_rpow (p := p) hB hBA
  have h1 : (∫ θ in (0)..(2 * Real.pi), (A + B * Real.cos θ) ^ (-p))
      = (∫ θ in (0)..Real.pi, (A + B * Real.cos θ) ^ (-p))
        + ∫ θ in Real.pi..(2 * Real.pi), (A + B * Real.cos θ) ^ (-p) :=
    (intervalIntegral.integral_add_adjacent_intervals (hc1.intervalIntegrable _ _)
      (hc1.intervalIntegrable _ _)).symm
  have h2 : (∫ θ in Real.pi..(2 * Real.pi), (A + B * Real.cos θ) ^ (-p))
      = ∫ θ in (0)..Real.pi, (A + B * Real.cos θ) ^ (-p) := by
    have hsub : (∫ θ in (0)..Real.pi, (A + B * Real.cos (θ + Real.pi)) ^ (-p))
        = ∫ θ in Real.pi..(2 * Real.pi), (A + B * Real.cos θ) ^ (-p) := by
      have h := intervalIntegral.integral_comp_add_right (a := (0 : ℝ)) (b := Real.pi)
        (fun θ : ℝ => (A + B * Real.cos θ) ^ (-p)) Real.pi
      simpa [show Real.pi + Real.pi = 2 * Real.pi by ring] using h
    rw [← hsub]
    calc (∫ θ in (0)..Real.pi, (A + B * Real.cos (θ + Real.pi)) ^ (-p))
        = ∫ θ in (0)..Real.pi, (A + B * Real.cos (Real.pi - θ)) ^ (-p) := by
          apply intervalIntegral.integral_congr
          intro θ _
          show (A + B * Real.cos (θ + Real.pi)) ^ (-p)
            = (A + B * Real.cos (Real.pi - θ)) ^ (-p)
          rw [Real.cos_add_pi, Real.cos_pi_sub]
      _ = ∫ θ in (0)..Real.pi, (A + B * Real.cos θ) ^ (-p) := by
          have h := intervalIntegral.integral_comp_sub_left (a := (0 : ℝ)) (b := Real.pi)
            (fun θ : ℝ => (A + B * Real.cos θ) ^ (-p)) Real.pi
          simpa using h
  have h3 : (∫ θ in (0)..Real.pi, (A + B * Real.cos θ) ^ (-p))
      = (∫ θ in (0)..(Real.pi / 2), (A + B * Real.cos θ) ^ (-p))
        + ∫ θ in (Real.pi / 2)..Real.pi, (A + B * Real.cos θ) ^ (-p) :=
    (intervalIntegral.integral_add_adjacent_intervals (hc1.intervalIntegrable _ _)
      (hc1.intervalIntegrable _ _)).symm
  have h4 : (∫ θ in (Real.pi / 2)..Real.pi, (A + B * Real.cos θ) ^ (-p))
      = ∫ θ in (0)..(Real.pi / 2), (A - B * Real.cos θ) ^ (-p) := by
    have hsub : (∫ θ in (0)..(Real.pi / 2), (A + B * Real.cos (Real.pi - θ)) ^ (-p))
        = ∫ θ in (Real.pi / 2)..Real.pi, (A + B * Real.cos θ) ^ (-p) := by
      have h := intervalIntegral.integral_comp_sub_left (a := (0 : ℝ)) (b := Real.pi / 2)
        (fun θ : ℝ => (A + B * Real.cos θ) ^ (-p)) Real.pi
      simpa [show Real.pi - Real.pi / 2 = Real.pi / 2 by ring] using h
    rw [← hsub]
    apply intervalIntegral.integral_congr
    intro θ _
    show (A + B * Real.cos (Real.pi - θ)) ^ (-p) = (A - B * Real.cos θ) ^ (-p)
    rw [Real.cos_pi_sub]
    ring_nf
  calc (∫ θ in (0)..(2 * Real.pi), (A + B * Real.cos θ) ^ (-p))
      = (∫ θ in (0)..Real.pi, (A + B * Real.cos θ) ^ (-p))
        + ∫ θ in Real.pi..(2 * Real.pi), (A + B * Real.cos θ) ^ (-p) := h1
    _ = (∫ θ in (0)..Real.pi, (A + B * Real.cos θ) ^ (-p))
        + ∫ θ in (0)..Real.pi, (A + B * Real.cos θ) ^ (-p) := by rw [h2]
    _ = 2 * ∫ θ in (0)..Real.pi, (A + B * Real.cos θ) ^ (-p) := by ring
    _ = 2 * ((∫ θ in (0)..(Real.pi / 2), (A + B * Real.cos θ) ^ (-p))
        + ∫ θ in (Real.pi / 2)..Real.pi, (A + B * Real.cos θ) ^ (-p)) := by rw [h3]
    _ = 2 * ((∫ θ in (0)..(Real.pi / 2), (A + B * Real.cos θ) ^ (-p))
        + ∫ θ in (0)..(Real.pi / 2), (A - B * Real.cos θ) ^ (-p)) := by rw [h4]
    _ = 2 * ∫ θ in (0)..(Real.pi / 2),
        ((A + B * Real.cos θ) ^ (-p) + (A - B * Real.cos θ) ^ (-p)) := by
        rw [intervalIntegral.integral_add (hc1.intervalIntegrable _ _) (hc2.intervalIntegrable _ _)]

/-- The circle average of `θ ↦ (A + B cos θ) ^ (-p)` is monotone in the amplitude `B`,
for `0 ≤ B ≤ C < A` and `p > 0`. -/
private lemma circle_rpow_neg_mono_amplitude {p A B C : ℝ} (hp : 0 < p) (hA : 0 < A)
    (hB : 0 ≤ B) (hBC : B ≤ C) (hC : C < A) :
    (∫ θ in (0)..(2 * Real.pi), (A + B * Real.cos θ) ^ (-p))
      ≤ ∫ θ in (0)..(2 * Real.pi), (A + C * Real.cos θ) ^ (-p) := by
  have hCnn : 0 ≤ C := le_trans hB hBC
  have hBA : B < A := lt_of_le_of_lt hBC hC
  rw [integral_cos_rpow_neg_symm (p := p) hB hBA,
      integral_cos_rpow_neg_symm (p := p) hCnn hC]
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
  apply intervalIntegral.integral_mono_on (by positivity : (0 : ℝ) ≤ Real.pi / 2)
  · exact ((continuous_add_cos_rpow (p := p) hB hBA).add
      (continuous_sub_cos_rpow (p := p) hB hBA)).intervalIntegrable _ _
  · exact ((continuous_add_cos_rpow (p := p) hCnn hC).add
      (continuous_sub_cos_rpow (p := p) hCnn hC)).intervalIntegrable _ _
  · intro θ hθ
    have hcos_nn : 0 ≤ Real.cos θ :=
      Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
    have hcos_le : Real.cos θ ≤ 1 := Real.cos_le_one θ
    have hple : B * Real.cos θ ≤ C * Real.cos θ := mul_le_mul_of_nonneg_right hBC hcos_nn
    have hx1 : B * Real.cos θ ∈ Icc (0 : ℝ) C := by
      refine ⟨mul_nonneg hB hcos_nn, ?_⟩
      calc B * Real.cos θ ≤ C * Real.cos θ := hple
        _ ≤ C * 1 := mul_le_mul_of_nonneg_left hcos_le hCnn
        _ = C := mul_one C
    have hx2 : C * Real.cos θ ∈ Icc (0 : ℝ) C := by
      refine ⟨mul_nonneg hCnn hcos_nn, ?_⟩
      calc C * Real.cos θ ≤ C * 1 := mul_le_mul_of_nonneg_left hcos_le hCnn
        _ = C := mul_one C
    have hmono := Commons.Analysis.Asymptotic.monotoneOn_half_sum_rpow_neg
      (p := p) (A := A) (B := C) hp hA hC
    have hkey := hmono hx1 hx2 hple
    linarith

theorem circle_avg_inv_sqrt_mono_amplitude {a d b : ℝ} (ha : 0 < a) (hd : 0 ≤ d) (hne : d ≠ a)
    (hb0 : 0 ≤ b) (hba : b ≤ a) :
    (1 / (2 * Real.pi)) * ∫ θ in (0)..(2 * Real.pi), (a ^ 2 + d ^ 2 + 2 * d * b * Real.cos θ) ^ (-(1:ℝ)/2)
      ≤ (1 / (2 * Real.pi)) * ∫ θ in (0)..(2 * Real.pi), (a ^ 2 + d ^ 2 + 2 * d * a * Real.cos θ) ^ (-(1:ℝ)/2) := by
  have hA : 0 < a ^ 2 + d ^ 2 := by positivity
  have hB : 0 ≤ 2 * d * b := by positivity
  have hCnn : 0 ≤ 2 * d * a := by positivity
  have hBC : 2 * d * b ≤ 2 * d * a := by nlinarith [hd, hba]
  have hClt : 2 * d * a < a ^ 2 + d ^ 2 := by
    have h : 0 < (a - d) ^ 2 := by
      apply sq_pos_of_ne_zero
      exact sub_ne_zero.mpr (Ne.symm hne)
    nlinarith [h]
  have key := circle_rpow_neg_mono_amplitude (p := (1:ℝ)/2) (A := a ^ 2 + d ^ 2)
    (B := 2 * d * b) (C := 2 * d * a) (by norm_num) hA hB hBC hClt
  rw [show -((1:ℝ)/2) = -(1:ℝ)/2 from by norm_num] at key
  exact mul_le_mul_of_nonneg_left key (by positivity)

end Commons.Analysis.Integral