import Mathlib
import Submission.Work.HP.ceil_logb_bounds

namespace Work.HP.Q44Main

theorem q44_log_sq_bound (Kmink Δ : ℝ) (hKmink : 1 ≤ Kmink) (hΔ : 1 ≤ Δ) :
    ((⌈Real.logb 2 (8 * Kmink * (Δ + 1))⌉₊ : ℝ) + 1) ^ 2
      ≤ ((Real.logb 2 (8 * Kmink) + 3) ^ 2 / (Real.log 2) ^ 2) * (Real.log (2 * Δ)) ^ 2 := by
  have hKpos : 0 < Kmink := lt_of_lt_of_le one_pos hKmink
  have hΔpos : 0 < Δ := lt_of_lt_of_le one_pos hΔ
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2ne : Real.log 2 ≠ 0 := ne_of_gt hlog2pos
  have harg1 : (1 : ℝ) ≤ 8 * Kmink * (Δ + 1) := by nlinarith [hKmink, hΔ]
  have hx_nonneg : 0 ≤ Real.logb 2 (8 * Kmink * (Δ + 1)) :=
    Real.logb_nonneg (by norm_num) harg1
  have hceil_lt : (⌈Real.logb 2 (8 * Kmink * (Δ + 1))⌉₊ : ℝ) <
      Real.logb 2 (8 * Kmink * (Δ + 1)) + 1 := Nat.ceil_lt_add_one hx_nonneg
  have hmul : Real.logb 2 (8 * Kmink * (Δ + 1)) =
      Real.logb 2 (8 * Kmink) + Real.logb 2 (Δ + 1) :=
    Real.logb_mul (by positivity) (by positivity)
  have hmono : Real.logb 2 (Δ + 1) ≤ Real.logb 2 (2 * Δ) := by
    rw [Real.logb_le_logb (b := 2) (x := Δ + 1) (y := 2 * Δ)
      (by norm_num) (by positivity) (by positivity)]
    linarith
  have hceil_lt' : (⌈Real.logb 2 (8 * Kmink * (Δ + 1))⌉₊ : ℝ) <
      Real.logb 2 (8 * Kmink) + Real.logb 2 (Δ + 1) + 1 := by
    calc (⌈Real.logb 2 (8 * Kmink * (Δ + 1))⌉₊ : ℝ)
        < Real.logb 2 (8 * Kmink * (Δ + 1)) + 1 := hceil_lt
      _ = Real.logb 2 (8 * Kmink) + Real.logb 2 (Δ + 1) + 1 := by rw [hmul]
  have hstep1 : (⌈Real.logb 2 (8 * Kmink * (Δ + 1))⌉₊ : ℝ) + 1 ≤
      Real.logb 2 (8 * Kmink) + Real.logb 2 (2 * Δ) + 2 := by
    linarith
  have hv : 1 ≤ Real.logb 2 (2 * Δ) := by
    have h := (Real.logb_le_logb (b := 2) (x := 2) (y := 2 * Δ)
      (by norm_num) (by norm_num) (by positivity)).mpr (by linarith)
    rw [Real.logb_self_eq_one (b := 2) (by norm_num)] at h
    exact h
  have hu : 0 ≤ Real.logb 2 (8 * Kmink) := Real.logb_nonneg (by norm_num) (by linarith)
  have hmain : Real.logb 2 (8 * Kmink) + Real.logb 2 (2 * Δ) + 2 ≤
      Real.logb 2 (2 * Δ) * (Real.logb 2 (8 * Kmink) + 3) := by
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ Real.logb 2 (8 * Kmink) + 2 by linarith)
      (show (0 : ℝ) ≤ Real.logb 2 (2 * Δ) - 1 by linarith)]
  have hstep : (⌈Real.logb 2 (8 * Kmink * (Δ + 1))⌉₊ : ℝ) + 1 ≤
      Real.logb 2 (2 * Δ) * (Real.logb 2 (8 * Kmink) + 3) := le_trans hstep1 hmain
  have hsq : ((⌈Real.logb 2 (8 * Kmink * (Δ + 1))⌉₊ : ℝ) + 1) ^ 2 ≤
      (Real.logb 2 (2 * Δ) * (Real.logb 2 (8 * Kmink) + 3)) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hstep 2
  have hv_eq : Real.logb 2 (2 * Δ) = Real.log (2 * Δ) / Real.log 2 := rfl
  calc ((⌈Real.logb 2 (8 * Kmink * (Δ + 1))⌉₊ : ℝ) + 1) ^ 2
      ≤ (Real.logb 2 (2 * Δ) * (Real.logb 2 (8 * Kmink) + 3)) ^ 2 := hsq
    _ = ((Real.logb 2 (8 * Kmink) + 3) ^ 2 / (Real.log 2) ^ 2) * (Real.log (2 * Δ)) ^ 2 := by
        rw [hv_eq]
        field_simp

end Work.HP.Q44Main
