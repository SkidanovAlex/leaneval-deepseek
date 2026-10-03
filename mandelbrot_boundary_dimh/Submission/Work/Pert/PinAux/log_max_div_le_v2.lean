import Mathlib

namespace Work.Pert.PinAux

/-- `log (max x 1) = max (log x) 0` for `x ≥ 0` (the `max` here is what the
"pinched" ratio `max M (Ξ/2) / (Ξ/2)` collapses to). -/
private lemma log_max_one {x : ℝ} (hx : 0 ≤ x) :
    Real.log (max x 1) = max (Real.log x) 0 := by
  by_cases h : x ≤ 1
  · rw [max_eq_right h, Real.log_one]
    have hlogx : Real.log x ≤ 0 := by
      rcases eq_or_lt_of_le hx with h0 | hpos
      · rw [← h0, Real.log_zero]
      · rw [← Real.log_one]; exact Real.log_le_log hpos h
    rw [max_eq_right hlogx]
  · rw [max_eq_left (le_of_lt (not_le.mp h)), max_eq_left (Real.log_pos (not_le.mp h)).le]

/-- Key real inequality: for `u, C ≥ 0` and `s > 0`,
`log ((2u + C)·s) ≤ (C + 2)·s + 1 + log (2 + u)`.

Writing `W = (2u+C)/(2+u) ≤ C + 2`, the left side is
`log (2+u) + log (W·s) ≤ log (2+u) + W·s - 1` by `log y ≤ y - 1`. -/
private lemma key_ineq (u C s : ℝ) (hu : 0 ≤ u) (hC : 0 ≤ C) (hs : 0 < s) :
    Real.log ((2 * u + C) * s) ≤ (C + 2) * s + 1 + Real.log (2 + u) := by
  have h2u : (0 : ℝ) < 2 + u := by linarith
  have hP0 : (0 : ℝ) ≤ 2 * u + C := by linarith
  rcases eq_or_lt_of_le hP0 with hPz | hPpos
  · rw [← hPz, zero_mul, Real.log_zero]
    have hh : 0 ≤ (C + 2) * s := mul_nonneg (by linarith) (le_of_lt hs)
    have hl : 0 ≤ Real.log (2 + u) := Real.log_nonneg (by linarith)
    linarith
  · set W : ℝ := (2 * u + C) / (2 + u) with hW
    have hWpos : 0 < W := div_pos hPpos h2u
    have hWs : 0 < W * s := mul_pos hWpos hs
    have hWle : W ≤ C + 2 := by
      rw [hW, div_le_iff₀ h2u]
      nlinarith [hu, hC]
    have h1 : Real.log (W * s) ≤ W * s - 1 := Real.log_le_sub_one_of_pos hWs
    have h2 : W * s ≤ (C + 2) * s := mul_le_mul_of_nonneg_right hWle (le_of_lt hs)
    have hmul' : (2 + u) * W = 2 * u + C := by
      rw [hW]; exact mul_div_cancel₀ _ (ne_of_gt h2u)
    have hmul : (2 * u + C) * s = (2 + u) * (W * s) := by
      rw [← hmul', mul_assoc]
    rw [hmul, Real.log_mul (ne_of_gt h2u) (ne_of_gt hWs)]
    linarith

theorem log_max_div_le_v2 (z : ℂ) (lo hi Ξ C : ℝ) (hΞ : 0 < Ξ) (hC : 0 ≤ C)
    (hmax : max |lo| |hi| ≤ 2 * ‖z‖ + C) :
    Real.log (max (max |lo| |hi|) (Ξ / 2) / (Ξ / 2))
      ≤ (2 * (2 / Ξ) + (2 / Ξ) * C + 1) + Real.log (2 + ‖z‖) := by
  set u : ℝ := ‖z‖ with hu
  have hu0 : 0 ≤ u := by rw [hu]; exact norm_nonneg z
  set s : ℝ := 2 / Ξ with hsdef
  have hs : 0 < s := by rw [hsdef]; exact div_pos two_pos hΞ
  set a : ℝ := max |lo| |hi| with ha
  have ha0 : 0 ≤ a := by rw [ha]; exact le_trans (abs_nonneg lo) (le_max_left _ _)
  have haP : a ≤ 2 * u + C := by rw [ha, hu]; exact hmax
  have hBpos : 0 < Ξ / 2 := by linarith
  have hsB : s * (Ξ / 2) = 1 := by rw [hsdef]; field_simp
  have hdiv : a / (Ξ / 2) = a * s := by
    rw [div_eq_iff (ne_of_gt hBpos), mul_assoc, hsB, mul_one]
  have harg : max a (Ξ / 2) / (Ξ / 2) = max (a * s) 1 := by
    rw [(max_div_div_right (le_of_lt hBpos) a (Ξ / 2)).symm, hdiv, div_self (ne_of_gt hBpos)]
  have h2 : 0 ≤ (C + 2) * s + 1 + Real.log (2 + u) := by
    have hh : 0 ≤ (C + 2) * s := mul_nonneg (by linarith) (le_of_lt hs)
    have hl : 0 ≤ Real.log (2 + u) := Real.log_nonneg (by linarith)
    linarith
  have h1 : Real.log (a * s) ≤ (C + 2) * s + 1 + Real.log (2 + u) := by
    rcases eq_or_lt_of_le ha0 with ha0' | hapos
    · rw [← ha0', zero_mul, Real.log_zero]; exact h2
    · have has : 0 < a * s := mul_pos hapos hs
      have hle : a * s ≤ (2 * u + C) * s := mul_le_mul_of_nonneg_right haP (le_of_lt hs)
      exact le_trans (Real.log_le_log has hle) (key_ineq u C s hu0 hC hs)
  calc Real.log (max (max |lo| |hi|) (Ξ / 2) / (Ξ / 2))
      = Real.log (max (a * s) 1) := by rw [← ha, harg]
    _ = max (Real.log (a * s)) 0 := log_max_one (mul_nonneg ha0 (le_of_lt hs))
    _ ≤ (C + 2) * s + 1 + Real.log (2 + u) := max_le h1 h2
    _ = (2 * (2 / Ξ) + (2 / Ξ) * C + 1) + Real.log (2 + ‖z‖) := by
        rw [hsdef, hu]; ring

end Work.Pert.PinAux
