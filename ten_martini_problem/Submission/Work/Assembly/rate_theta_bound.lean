import Mathlib

namespace Work.Assembly

/-- Auxiliary: from `R^(8/9) < (s+1)*Q` and `3 ≤ s`, `Q > 0`, one gets
`3 * R^(8/9) ≤ 4 * (s*Q)`, hence `2/(s*Q) ≤ (8/3)/R^(8/9)`. -/
theorem rate_theta_aux {R Q s : ℝ} (hR : 0 < R) (hQ : 0 < Q) (hs : 3 ≤ s)
    (h : R ^ (8 / 9 : ℝ) < (s + 1) * Q) :
    2 / (s * Q) ≤ (8 / 3) / R ^ (8 / 9 : ℝ) := by
  have hsQ : 0 < s * Q := mul_pos (by linarith) hQ
  have hRpos : 0 < R ^ (8 / 9 : ℝ) := Real.rpow_pos_of_pos hR _
  have hkey : 3 * R ^ (8 / 9 : ℝ) ≤ 4 * (s * Q) := by
    nlinarith [h, hs, hQ, hRpos]
  have hkey2 : 2 * R ^ (8 / 9 : ℝ) ≤ (8 / 3) * (s * Q) := by linarith [hkey]
  rw [le_div_iff₀ hRpos, div_mul_eq_mul_div, div_le_iff₀ hsQ]
  linarith [hkey2]

theorem rate_theta_bound {R Q s c Cθ : ℝ} (hR : 0 < R) (hQ : 0 < Q) (hs : 3 ≤ s)
    (h : R ^ (8 / 9 : ℝ) < (s + 1) * Q) (hc : 0 < c)
    (hle : Real.log (1 / c) ≤ Cθ + 20 * Real.log (R + 2)) :
    2 * Real.log (1 / c) / (s * Q) ≤ (8 / 3) * (|Cθ| + 20 * Real.log (R + 2)) / R ^ (8 / 9 : ℝ) := by
  have hsQ : 0 < s * Q := mul_pos (by linarith) hQ
  have hRpos : 0 < R ^ (8 / 9 : ℝ) := Real.rpow_pos_of_pos hR _
  have hlogR2 : 0 ≤ Real.log (R + 2) := Real.log_nonneg (by linarith)
  have hL : 0 ≤ |Cθ| + 20 * Real.log (R + 2) := by
    have := abs_nonneg Cθ; linarith
  have hkeydiv : 2 / (s * Q) ≤ (8 / 3) / R ^ (8 / 9 : ℝ) :=
    rate_theta_aux hR hQ hs h
  by_cases hpos : 0 ≤ Real.log (1 / c)
  · have hle2 : Real.log (1 / c) ≤ |Cθ| + 20 * Real.log (R + 2) := by
      linarith [hle, le_abs_self Cθ]
    calc 2 * Real.log (1 / c) / (s * Q)
        ≤ 2 * (|Cθ| + 20 * Real.log (R + 2)) / (s * Q) := by
          apply div_le_div_of_nonneg_right _ (le_of_lt hsQ); linarith
      _ = (|Cθ| + 20 * Real.log (R + 2)) * (2 / (s * Q)) := by ring
      _ ≤ (|Cθ| + 20 * Real.log (R + 2)) * ((8 / 3) / R ^ (8 / 9 : ℝ)) :=
          mul_le_mul_of_nonneg_left hkeydiv hL
      _ = (8 / 3) * (|Cθ| + 20 * Real.log (R + 2)) / R ^ (8 / 9 : ℝ) := by ring
  · have h1 : 2 * Real.log (1 / c) / (s * Q) ≤ 0 := by
      apply div_nonpos_of_nonpos_of_nonneg _ (le_of_lt hsQ); linarith
    have h2 : 0 ≤ (8 / 3) * (|Cθ| + 20 * Real.log (R + 2)) / R ^ (8 / 9 : ℝ) := by
      apply div_nonneg _ (le_of_lt hRpos); nlinarith [hL]
    linarith

end Work.Assembly
