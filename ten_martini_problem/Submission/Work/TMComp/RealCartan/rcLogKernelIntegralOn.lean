import Mathlib

namespace Work.TMComp.RealCartan

open MeasureTheory Set

/-- `Real.log` (hence its absolute value) is interval integrable on every interval. -/
theorem rcAbsLog_intervalIntegrable (a b : ℝ) :
    IntervalIntegrable (fun u : ℝ => |Real.log u|) volume a b :=
  (intervalIntegral.intervalIntegrable_log' (a := a) (b := b)).abs

/-- `∫_0^1 |log u| du = 1`. -/
theorem rcAbsLog_integral_zero_one : ∫ u in (0:ℝ)..1, |Real.log u| = 1 := by
  have h : Set.EqOn (fun u : ℝ => |Real.log u|) (fun u : ℝ => -Real.log u) (Set.uIcc 0 1) := by
    intro u hu
    rw [Set.uIcc_of_le zero_le_one] at hu
    simp only [Set.mem_Icc] at hu
    show |Real.log u| = -Real.log u
    rw [abs_of_nonpos (Real.log_nonpos hu.1 hu.2)]
  rw [intervalIntegral.integral_congr h, intervalIntegral.integral_neg, integral_log]
  norm_num

/-- `∫_{-1}^1 |log u| du = 2`. -/
theorem rcAbsLog_integral_neg_one_one : ∫ u in (-1:ℝ)..1, |Real.log u| = 2 := by
  have hneg : IntervalIntegrable (fun u : ℝ => |Real.log u|) volume (-1:ℝ) 0 :=
    rcAbsLog_intervalIntegrable (-1) 0
  have hpos : IntervalIntegrable (fun u : ℝ => |Real.log u|) volume (0:ℝ) 1 :=
    rcAbsLog_intervalIntegrable 0 1
  have hadj := intervalIntegral.integral_add_adjacent_intervals hneg hpos
  have heven : ∫ u in (-1:ℝ)..0, |Real.log u| = ∫ u in (-1:ℝ)..0, |Real.log (-u)| := by
    apply intervalIntegral.integral_congr
    intro u _
    show |Real.log u| = |Real.log (-u)|
    rw [Real.log_neg_eq_log]
  have hcomp : ∫ u in (-1:ℝ)..0, |Real.log (-u)| = ∫ u in (0:ℝ)..1, |Real.log u| := by
    have := intervalIntegral.integral_comp_neg
      (f := fun x : ℝ => |Real.log x|) (a := (-1:ℝ)) (b := 0)
    simpa using this
  have hnegval : ∫ u in (-1:ℝ)..0, |Real.log u| = 1 := by
    rw [heven, hcomp]
    exact rcAbsLog_integral_zero_one
  rw [← hadj, hnegval, rcAbsLog_integral_zero_one]
  norm_num

/-- The logarithmic kernel `t ↦ |log (|t - c| / ε)|` is integrable on `Ioc (c - ε) (c + ε)`
and its integral there equals `2 * ε`. -/
theorem rcLogKernelIntegralOn (c ε : ℝ) (hε : 0 < ε) :
    MeasureTheory.IntegrableOn (fun t : ℝ => |Real.log (|t - c| / ε)|)
        (Set.Ioc (c - ε) (c + ε)) MeasureTheory.volume ∧
      ∫ t in Set.Ioc (c - ε) (c + ε), |Real.log (|t - c| / ε)| = 2 * ε := by
  have hle : c - ε ≤ c + ε := by linarith
  have hpt : ∀ t : ℝ, |Real.log (|t - c| / ε)| = |Real.log ((t - c) / ε)| := by
    intro t
    have h1 : |t - c| / ε = |(t - c) / ε| := by rw [abs_div, abs_of_pos hε]
    rw [h1, Real.log_abs]
  have hFint : IntervalIntegrable (fun t : ℝ => |Real.log ((t - c) / ε)|) volume (c - ε) (c + ε) := by
    have h1 : IntervalIntegrable (fun u : ℝ => |Real.log (u / ε)|) volume (-ε) ε := by
      have h := (rcAbsLog_intervalIntegrable (-1) 1).comp_mul_left (c := ε⁻¹)
      simpa [div_eq_mul_inv, inv_inv, mul_comm] using h
    have h2 := h1.comp_sub_right c
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h2
  have hval : ∫ t in (c - ε)..(c + ε), |Real.log ((t - c) / ε)| = 2 * ε := by
    rw [intervalIntegral.integral_congr
      (f := fun t : ℝ => |Real.log ((t - c) / ε)|)
      (g := fun t : ℝ => |Real.log (t / ε - c / ε)|) (fun t _ => by simp only [sub_div])]
    rw [intervalIntegral.integral_comp_div_sub (fun u : ℝ => |Real.log u|) hε.ne' (c / ε)]
    rw [show (c - ε) / ε - c / ε = -1 by rw [sub_div, div_self hε.ne']; ring,
        show (c + ε) / ε - c / ε = 1 by rw [add_div, div_self hε.ne']; ring]
    rw [rcAbsLog_integral_neg_one_one]
    rw [smul_eq_mul, mul_comm]
  exact ⟨hFint.1.congr_fun (fun t _ => (hpt t).symm) measurableSet_Ioc, by
    rw [← intervalIntegral.integral_of_le hle]
    rw [intervalIntegral.integral_congr
      (f := fun t : ℝ => |Real.log (|t - c| / ε)|)
      (g := fun t : ℝ => |Real.log ((t - c) / ε)|) (fun t _ => hpt t)]
    exact hval⟩

end Work.TMComp.RealCartan
