import Mathlib

set_option linter.unusedVariables false

namespace Work.Pert.PinAux

/-- Core real inequality behind `log_max_div_le`.

If `M ≤ A + B` with `A, B ≥ 0`, then the `log` of the "pinched" ratio
`max M (Ξ/2) / (Ξ/2)` (which is `max (M·k) 1` with `k = 2/Ξ`) is bounded by
`(1 + B)·k + log (2 + A)`.  The proof is a single exponential estimate:
`max (M·k) 1 ≤ (2 + A)·exp ((1 + B)·k)`, which follows from the polynomial
bound `(A + B)·k ≤ (2 + A)·(1 + (1 + B)·k)` together with `1 + x ≤ exp x`. -/
theorem log_max_div_le_core (M A B Ξ : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hΞ : 0 < Ξ)
    (hM : M ≤ A + B) :
    Real.log (max M (Ξ / 2) / (Ξ / 2)) ≤ (1 + B) * (2 / Ξ) + Real.log (2 + A) := by
  have hΞ2 : 0 < Ξ / 2 := by linarith
  set k : ℝ := 2 / Ξ with hk_def
  have hk : 0 < k := by rw [hk_def]; exact div_pos two_pos hΞ
  have hkΞ : k * (Ξ / 2) = 1 := by rw [hk_def]; field_simp
  have hkeq : M / (Ξ / 2) = M * k := by
    rw [div_eq_iff (ne_of_gt hΞ2), mul_assoc, hkΞ, mul_one]
  have hmaxeq : max M (Ξ / 2) / (Ξ / 2) = max (M * k) 1 := by
    rw [← max_div_div_right (le_of_lt hΞ2) M (Ξ / 2), hkeq, div_self (ne_of_gt hΞ2)]
  rw [hmaxeq]
  have h2A : (2 : ℝ) + A ≠ 0 := by positivity
  have hMk : M * k ≤ (2 + A) * Real.exp ((1 + B) * k) := by
    have h1 : M * k ≤ (A + B) * k := mul_le_mul_of_nonneg_right hM (le_of_lt hk)
    have h2 : (A + B) * k ≤ (2 + A) * (1 + (1 + B) * k) := by
      have hp1 : 0 ≤ A * k := by positivity
      have hp2 : 0 ≤ B * k := by positivity
      have hp3 : 0 ≤ A * B * k := by positivity
      nlinarith [hp1, hp2, hp3]
    have h3 : (2 + A) * (1 + (1 + B) * k) ≤ (2 + A) * Real.exp ((1 + B) * k) :=
      mul_le_mul_of_nonneg_left (by linarith [Real.add_one_le_exp ((1 + B) * k)]) (by linarith)
    linarith [h1, h2, h3]
  have h1X : (1 : ℝ) ≤ (2 + A) * Real.exp ((1 + B) * k) := by
    have hexp : (1 : ℝ) ≤ Real.exp ((1 + B) * k) := Real.one_le_exp (by nlinarith [hB, hk])
    nlinarith [hexp, hA]
  have hpos : 0 < max (M * k) 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hle : max (M * k) 1 ≤ (2 + A) * Real.exp ((1 + B) * k) := max_le hMk h1X
  have hlog := Real.log_le_log hpos hle
  rw [Real.log_mul h2A (Real.exp_ne_zero _), Real.log_exp] at hlog
  linarith

theorem log_max_div_le (z : ℂ) (lo hi B Ξ : ℝ) (hB : 0 ≤ B) (hΞB : Ξ ≤ B) (hΞ : 0 < Ξ)
    (hmax : max |lo| |hi| ≤ |z.im| + B) :
    Real.log (max (max |lo| |hi|) (Ξ / 2) / (Ξ / 2)) ≤ (1 + B) * (2 / Ξ) + Real.log (2 + ‖z‖) := by
  refine log_max_div_le_core (max |lo| |hi|) ‖z‖ B Ξ (norm_nonneg z) hB hΞ ?_
  have h : |z.im| + B ≤ ‖z‖ + B := by linarith [Complex.abs_im_le_norm z]
  exact le_trans hmax h

end Work.Pert.PinAux
