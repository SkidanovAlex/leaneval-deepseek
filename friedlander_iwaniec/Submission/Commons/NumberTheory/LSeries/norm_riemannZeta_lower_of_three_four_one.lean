import Mathlib
import Submission.Commons.NumberTheory.LSeries.one_le_norm_riemannZeta_three_four_one
import Submission.Commons.NumberTheory.LSeries.riemannZeta_norm_le_inv_sub_one
import Submission.Commons.NumberTheory.LSeries.norm_riemannZeta_le_five_mul_log

open Complex

namespace Commons.NumberTheory.LSeries

/-- **Lower bound for the Riemann zeta function just right of the pole.**
For `1 < σ ≤ 2` and `|t| ≥ 1`,
`((σ-1)^3 / (100 log(|t|+2)))^(1/4) ≤ ‖ζ(σ + it)‖`.

This is the standard consequence of the `(3,4,1)` inequality
`1 ≤ |ζ(σ)|^3 |ζ(σ+it)|^4 |ζ(σ+2it)|`: combining it with `|ζ(σ)| ≤ σ/(σ-1)` and the
Euler–Maclaurin bound `|ζ(σ+2it)| ≤ 5 log(2|t|+2)` gives
`|ζ(σ+it)|^4 ≥ (σ-1)^3 / (100 log(|t|+2))`. -/
theorem norm_riemannZeta_lower_of_three_four_one {σ t : ℝ} (h1 : 1 < σ) (h2 : σ ≤ 2) (ht : 1 ≤ |t|) :
    ((σ - 1) ^ 3 / (100 * Real.log (|t| + 2))) ^ (1 / 4 : ℝ)
      ≤ ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ := by
  set L := Real.log (|t| + 2) with hLdef
  have hLpos : 0 < L := by
    rw [hLdef]; exact Real.log_pos (by linarith [abs_nonneg t])
  have hσ1 : 0 < σ - 1 := by linarith
  -- Upper bound for `|ζ(σ)|^3` after multiplying by `(σ-1)^3`.
  have hA : (σ - 1) ^ 3 * ‖riemannZeta (σ : ℂ)‖ ^ 3 ≤ 8 := by
    have hle : ‖riemannZeta (σ : ℂ)‖ ≤ 2 / (σ - 1) :=
      riemannZeta_norm_le_inv_sub_one h1 h2
    have hmul : (σ - 1) * ‖riemannZeta (σ : ℂ)‖ ≤ 2 := by
      calc (σ - 1) * ‖riemannZeta (σ : ℂ)‖ ≤ (σ - 1) * (2 / (σ - 1)) :=
            mul_le_mul_of_nonneg_left hle hσ1.le
        _ = 2 := by field_simp
    have hp : ((σ - 1) * ‖riemannZeta (σ : ℂ)‖) ^ 3 ≤ (2 : ℝ) ^ 3 :=
      pow_le_pow_left₀ (by positivity) hmul 3
    have he : ((σ - 1) * ‖riemannZeta (σ : ℂ)‖) ^ 3
        = (σ - 1) ^ 3 * ‖riemannZeta (σ : ℂ)‖ ^ 3 := by ring
    rw [he] at hp
    norm_num at hp
    linarith [hp]
  -- Logarithmic upper bound for the shifted value `ζ(σ + 2it)`.
  have hC : ‖riemannZeta ((σ : ℂ) + 2 * (t : ℂ) * Complex.I)‖ ≤ 12.5 * L := by
    have h2t : (1 : ℝ) ≤ |2 * t| := by
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      linarith
    have h := norm_riemannZeta_le_five_mul_log (σ := σ) (t := 2 * t) h1.le h2t
    have harg : ((σ : ℂ) + (((2 * t : ℝ)) : ℂ) * Complex.I)
        = (σ : ℂ) + 2 * (t : ℂ) * Complex.I := by push_cast; ring
    rw [harg] at h
    have hlog : Real.log (|2 * t| + 2) ≤ Real.log 2 + L := by
      have h2t' : |2 * t| = 2 * |t| := by rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      rw [h2t', hLdef]
      calc Real.log (2 * |t| + 2) ≤ Real.log (2 * (|t| + 2)) := by
            apply Real.log_le_log (by positivity)
            linarith
        _ = Real.log 2 + Real.log (|t| + 2) := Real.log_mul (by norm_num) (by positivity)
    have hlog2 : Real.log 2 ≤ L := by
      rw [hLdef]; exact Real.log_le_log (by norm_num) (by linarith [abs_nonneg t])
    calc ‖riemannZeta ((σ : ℂ) + 2 * (t : ℂ) * Complex.I)‖ ≤ 5 * Real.log (|2 * t| + 2) := h
      _ ≤ 5 * (Real.log 2 + L) := by linarith
      _ ≤ 12.5 * L := by linarith
  -- The `(3,4,1)` inequality.
  have h341 := one_le_norm_riemannZeta_three_four_one (σ := σ) (t := t) h1
  have hk : 0 < (σ - 1) ^ 3 := by positivity
  have hBnn : 0 ≤ ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 4 := by positivity
  have hAC : (σ - 1) ^ 3 * (‖riemannZeta (σ : ℂ)‖ ^ 3
      * ‖riemannZeta ((σ : ℂ) + 2 * (t : ℂ) * Complex.I)‖) ≤ 100 * L := by
    have h := mul_le_mul hA hC (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 8)
    nlinarith [h]
  have hkey : ‖riemannZeta (σ : ℂ)‖ ^ 3
      * ‖riemannZeta ((σ : ℂ) + 2 * (t : ℂ) * Complex.I)‖ ≤ (100 * L) / (σ - 1) ^ 3 := by
    rw [le_div_iff₀ hk]
    nlinarith [hAC]
  have hstep : (‖riemannZeta (σ : ℂ)‖ ^ 3
        * ‖riemannZeta ((σ : ℂ) + 2 * (t : ℂ) * Complex.I)‖)
        * ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 4
      ≤ ((100 * L) / (σ - 1) ^ 3)
        * ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 4 :=
    mul_le_mul_of_nonneg_right hkey hBnn
  have hone : 1 ≤ ((100 * L) / (σ - 1) ^ 3)
      * ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 4 := by
    refine le_trans ?_ hstep
    nlinarith [h341]
  have hM : 0 < (100 * L) / (σ - 1) ^ 3 := by positivity
  have hfin : (σ - 1) ^ 3 / (100 * L)
      ≤ ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 4 := by
    have hone' : 1 ≤ ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 4
        * ((100 * L) / (σ - 1) ^ 3) := by
      simpa only [mul_comm] using hone
    have h' := (inv_le_iff_one_le_mul₀ hM).mpr hone'
    have heq : ((100 * L) / (σ - 1) ^ 3)⁻¹ = (σ - 1) ^ 3 / (100 * L) := by field_simp
    rwa [heq] at h'
  have hXnn : 0 ≤ (σ - 1) ^ 3 / (100 * L) := by positivity
  have hr := Real.rpow_le_rpow hXnn hfin (by norm_num : (0 : ℝ) ≤ 1 / 4)
  have h4 : (‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 4) ^ (1 / 4 : ℝ)
      = ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _),
      show ((4 : ℕ) : ℝ) * (1 / 4) = 1 by norm_num, Real.rpow_one]
  rwa [h4] at hr

end Commons.NumberTheory.LSeries
