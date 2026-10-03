import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Analysis.PertCrux.germ_cubic_bound

namespace Work.Analysis.PertCrux

open Complex Metric

/-- The algebraic identity behind `tau0_step_bound`: for `f z ≠ 0` and `z ≠ 0`,
`τ₀ (f z) - τ₀ z - 1 = (f z - z - z f z) / (z f z)`. -/
lemma tau0_sub_one_eq (f : ℂ → ℂ) {z : ℂ} (hz : z ≠ 0) (hf : f z ≠ 0) :
    MandelDim.tau0 (f z) - MandelDim.tau0 z - 1 = (f z - z - z * f z) / (z * f z) := by
  rw [MandelDim.tau0, MandelDim.tau0]
  field_simp
  ring

/-- For a parabolic germ `f₀ z = z + z² + O(z³)` there are `R₀ > 0` and `K ≥ 0` such that for
`0 < ‖z‖ ≤ R₀` the chart coordinate `τ₀ z = -1/z` satisfies `‖τ₀ (f₀ z) - τ₀ z - 1‖ ≤ K ‖z‖`, and
in particular `f₀ z ≠ 0`. -/
theorem tau0_step_bound {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (hd : MandelDim.IsParabolicGerm f₀ D₀) :
    ∃ R₀ : ℝ, 0 < R₀ ∧ ∃ K : ℝ, 0 ≤ K ∧ ∀ z : ℂ, 0 < ‖z‖ → ‖z‖ ≤ R₀ →
      f₀ z ≠ 0 ∧ ‖MandelDim.tau0 (f₀ z) - MandelDim.tau0 z - 1‖ ≤ K * ‖z‖ := by
  obtain ⟨C, hC, r, hr, hbound⟩ := germ_cubic_bound hd
  have h4pos : (0 : ℝ) < 4 * (1 + C) := by linarith
  refine ⟨min r (min 1 (1 / (4 * (1 + C)))), lt_min hr (lt_min one_pos (by positivity)),
    4 * C + 2, by linarith, ?_⟩
  intro z hz hzR
  have hz0 : z ≠ 0 := by rintro rfl; simp at hz
  set n : ℝ := ‖z‖ with hn
  have hnpos : 0 < n := hz
  have hnr : n ≤ r := le_trans hzR (min_le_left _ _)
  have hn1 : n ≤ 1 := le_trans hzR (le_trans (min_le_right _ _) (min_le_left _ _))
  have hnq : n ≤ 1 / (4 * (1 + C)) :=
    le_trans hzR (le_trans (min_le_right _ _) (min_le_right _ _))
  have hnq' : n * (1 + C) ≤ 1 / 4 := by
    have h := (le_div_iff₀ h4pos).mp hnq
    linarith
  set D : ℂ := f₀ z - z - z ^ 2 with hD
  have hG : ‖D‖ ≤ C * n ^ 3 := by
    have h := hbound z (by rw [← hn]; exact hnr)
    rw [← hn] at h
    rwa [← hD] at h
  -- ## `‖f₀ z - z‖ ≤ n/4`: `f₀ z = z + z² + O(z³)` with `‖z‖ ≤ R₀` small.
  have hstep : ‖f₀ z - z‖ ≤ n / 4 := by
    have hsplit : f₀ z - z = D + z ^ 2 := by rw [hD]; ring
    have h1 : ‖f₀ z - z‖ = ‖D + z ^ 2‖ := by rw [hsplit]
    rw [h1]
    have hkey : n ^ 2 * (1 + C) ≤ n / 4 := by
      have hmul := mul_le_mul_of_nonneg_left hnq' hnpos.le
      have he : n * (n * (1 + C)) = n ^ 2 * (1 + C) := by ring
      rw [he] at hmul
      linarith
    have hCn3 : C * n ^ 3 ≤ C * n ^ 2 := by
      have : n ^ 3 ≤ n ^ 2 := by nlinarith [hn1, hnpos]
      exact mul_le_mul_of_nonneg_left this hC
    calc ‖D + z ^ 2‖ ≤ ‖D‖ + ‖z ^ 2‖ := norm_add_le _ _
      _ = ‖D‖ + n ^ 2 := by rw [norm_pow, ← hn]
      _ ≤ C * n ^ 3 + n ^ 2 := by linarith
      _ ≤ n / 4 := by linarith
  have hfz_lower : 3 / 4 * n ≤ ‖f₀ z‖ := by
    have h := abs_norm_sub_norm_le (f₀ z) z
    have h2 := (abs_le.mp h).1
    linarith
  have hfz_ne : f₀ z ≠ 0 := by
    intro h0
    have : ‖f₀ z‖ = 0 := by rw [h0]; simp
    linarith
  refine ⟨hfz_ne, ?_⟩
  have hCnn : (0 : ℝ) ≤ C := hC
  have hn3nn : (0 : ℝ) ≤ n ^ 3 := pow_nonneg hnpos.le 3
  -- ## numerator bound: `f₀ z - z - z f₀ z = O(z³)`
  have hnum : f₀ z - z - z * f₀ z = D * (1 - z) - z ^ 3 := by
    rw [hD]; ring
  have hnum_norm : ‖f₀ z - z - z * f₀ z‖ ≤ (2 * C + 1) * n ^ 3 := by
    rw [hnum]
    have h1z : ‖(1 : ℂ) - z‖ ≤ 1 + n := by
      calc ‖(1 : ℂ) - z‖ ≤ ‖(1 : ℂ)‖ + ‖z‖ := norm_sub_le _ _
        _ = 1 + n := by simp [hn]
    have hDnn : (0 : ℝ) ≤ ‖D‖ := norm_nonneg _
    have hCn : (0 : ℝ) ≤ C * n ^ 3 := mul_nonneg hC hn3nn
    have hmult : C * n ^ 3 * (1 + n) ≤ C * n ^ 3 * 2 := by
      have h1n : (1 : ℝ) + n ≤ 2 := by linarith
      exact mul_le_mul_of_nonneg_left h1n hCn
    have hmain : ‖D‖ * ‖(1 : ℂ) - z‖ ≤ (C * n ^ 3) * (1 + n) :=
      mul_le_mul hG h1z (norm_nonneg _) hCn
    calc ‖D * (1 - z) - z ^ 3‖ ≤ ‖D * (1 - z)‖ + ‖z ^ 3‖ := norm_sub_le _ _
      _ = ‖D‖ * ‖(1 : ℂ) - z‖ + n ^ 3 := by rw [norm_mul, norm_pow, ← hn]
      _ ≤ (C * n ^ 3) * (1 + n) + n ^ 3 := by linarith
      _ ≤ (2 * C + 1) * n ^ 3 := by nlinarith [hmult, hn3nn]
  have hkey := tau0_sub_one_eq f₀ hz0 hfz_ne
  rw [hkey]
  -- ## denominator lower bound `‖z f₀ z‖ ≥ (3/4) n²`
  have hden_lower : 3 / 4 * n ^ 2 ≤ ‖z * f₀ z‖ := by
    rw [norm_mul]
    have h2 : n * (3 / 4 * n) ≤ n * ‖f₀ z‖ := mul_le_mul_of_nonneg_left hfz_lower hnpos.le
    calc 3 / 4 * n ^ 2 = n * (3 / 4 * n) := by ring
      _ ≤ n * ‖f₀ z‖ := h2
  have hden_pos : (0 : ℝ) < 3 / 4 * n ^ 2 := mul_pos (by norm_num) (pow_pos hnpos 2)
  calc ‖(f₀ z - z - z * f₀ z) / (z * f₀ z)‖
      = ‖f₀ z - z - z * f₀ z‖ / ‖z * f₀ z‖ := norm_div _ _
    _ ≤ ‖f₀ z - z - z * f₀ z‖ / (3 / 4 * n ^ 2) :=
        div_le_div_of_nonneg_left (norm_nonneg _) hden_pos hden_lower
    _ ≤ ((2 * C + 1) * n ^ 3) / (3 / 4 * n ^ 2) :=
        div_le_div_of_nonneg_right hnum_norm hden_pos.le
    _ = (4 / 3 * (2 * C + 1)) * n := by
        rw [div_eq_iff (ne_of_gt hden_pos)]
        ring
    _ ≤ (4 * C + 2) * n := by
        have hle : (4 : ℝ) / 3 * (2 * C + 1) ≤ 4 * C + 2 := by linarith
        exact mul_le_mul_of_nonneg_right hle hnpos.le

end Work.Analysis.PertCrux
