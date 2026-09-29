import Mathlib

namespace Work.TMC16Core.Assembly

/-- For any positive `L`, `εf` and nonnegative `C`, eventually the (sublinear) quantity
`log (2 C (1 + 2 qn))` is dominated by the linear expression
`(19/80) L qn + (14/5) εf qn + L + εf`.

The proof bounds `log y ≤ 2 √y` (via `Real.log_le_rpow_div` with exponent `1/2`) and reduces
the claim to `4 · 2 C (1 + 2 qn) ≤ (a qn + (L+εf))²`, where `a = (19/80) L + (14/5) εf > 0`.
The right-hand side is quadratic with positive leading coefficient and the left-hand side is
linear, so the inequality holds once `a² qn ≥ 24 C` (and `qn ≥ 1`). -/
theorem res_thresh_bad {L εf C : ℝ} (hL : 0 < L) (hεf : 0 < εf) (hC : 0 ≤ C) :
    ∃ Q : ℕ, ∀ qn : ℕ, Q ≤ qn →
      Real.log (2 * C * (1 + 2 * (qn : ℝ))) ≤
        (19 / 80) * L * (qn : ℝ) + (14 / 5) * εf * (qn : ℝ) + L + εf := by
  set a : ℝ := (19 / 80) * L + (14 / 5) * εf with ha_def
  have ha_pos : 0 < a := by rw [ha_def]; positivity
  obtain ⟨Q0, hQ0⟩ := exists_nat_ge ((24 * C) / a ^ 2)
  refine ⟨max 1 Q0, ?_⟩
  intro qn hqn
  have hq1 : 1 ≤ qn := le_trans (le_max_left (1 : ℕ) Q0) hqn
  have hqQ0 : Q0 ≤ qn := le_trans (le_max_right (1 : ℕ) Q0) hqn
  have hqn0 : (0 : ℝ) ≤ (qn : ℝ) := Nat.cast_nonneg qn
  have hqn1r : (1 : ℝ) ≤ (qn : ℝ) := by exact_mod_cast hq1
  have hthr : 24 * C / a ^ 2 ≤ (qn : ℝ) := le_trans hQ0 (by exact_mod_cast hqQ0)
  have ha2pos : 0 < a ^ 2 := by positivity
  have h_mul : 24 * C ≤ a ^ 2 * (qn : ℝ) := by
    have h := (div_le_iff₀ ha2pos).mp hthr
    linarith
  have h3 : 24 * C * (qn : ℝ) ≤ a ^ 2 * (qn : ℝ) ^ 2 := by
    have h := mul_le_mul_of_nonneg_right h_mul hqn0
    nlinarith [h]
  have hC8 : 8 * C ≤ 8 * C * (qn : ℝ) := by nlinarith [hC, hqn1r]
  have h12 : 4 * (2 * C * (1 + 2 * (qn : ℝ))) ≤ 24 * C * (qn : ℝ) := by
    nlinarith [hC8]
  have h4 : a ^ 2 * (qn : ℝ) ^ 2 ≤ (a * (qn : ℝ) + (L + εf)) ^ 2 := by
    have h1 : 0 ≤ a * (qn : ℝ) := by positivity
    have h2 : 0 ≤ L + εf := by linarith
    nlinarith [mul_nonneg h1 h2, sq_nonneg (L + εf)]
  have hfin : 4 * (2 * C * (1 + 2 * (qn : ℝ))) ≤ (a * (qn : ℝ) + (L + εf)) ^ 2 :=
    le_trans h12 (le_trans h3 h4)
  have hX_nonneg : 0 ≤ a * (qn : ℝ) + (L + εf) := by positivity
  have hsq4 : Real.sqrt (4 : ℝ) = 2 := by
    rw [Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)]; norm_num
  have hsqrt : 2 * Real.sqrt (2 * C * (1 + 2 * (qn : ℝ))) ≤ a * (qn : ℝ) + (L + εf) := by
    have h := (Real.sqrt_le_left hX_nonneg).mpr hfin
    have h4eq : Real.sqrt (4 * (2 * C * (1 + 2 * (qn : ℝ))))
        = 2 * Real.sqrt (2 * C * (1 + 2 * (qn : ℝ))) := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4), hsq4]
    rwa [h4eq] at h
  have hlog : Real.log (2 * C * (1 + 2 * (qn : ℝ)))
      ≤ 2 * Real.sqrt (2 * C * (1 + 2 * (qn : ℝ))) := by
    have hy : 0 ≤ 2 * C * (1 + 2 * (qn : ℝ)) := by positivity
    have h := Real.log_le_rpow_div hy (show (0 : ℝ) < 1 / 2 by norm_num)
    rw [Real.sqrt_eq_rpow]
    have : (2 * C * (1 + 2 * (qn : ℝ))) ^ (1 / 2 : ℝ) / (1 / 2)
        = 2 * (2 * C * (1 + 2 * (qn : ℝ))) ^ (1 / 2 : ℝ) := by ring
    linarith [h]
  have hRHS : a * (qn : ℝ) + (L + εf)
      = (19 / 80) * L * (qn : ℝ) + (14 / 5) * εf * (qn : ℝ) + L + εf := by
    rw [ha_def]; ring
  linarith [hlog, hsqrt]

end Work.TMC16Core.Assembly
