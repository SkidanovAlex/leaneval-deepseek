import Mathlib
import Submission.Work.Interfaces.Parabolic

namespace Work.Pert

/-!
# PERT · `Work.Pert.gate_L1_arith`

Elementary arithmetic gate used by the `L¹` form of Shishikura's (A.1.7)(ii) near-translation
statement (`Work.Pert.gate_scale_L1`): for `α ∈ 𝓕₁` (`|Im α| < Re α`) and `‖σ‖ ≤ 8π‖α‖`,

`(32/ρmin + 16) · ‖σ‖² / (Re α · ‖α‖ · (10¹²/min ρmin 1)) ≤ 1/64`.

The estimate is very slack.  `𝓕₁` gives `Re α ≥ ‖α‖/2` (via `‖α‖ ≤ |Re α| + |Im α| < 2 Re α`),
so the quotient is at most `2 (32/ρmin + 16) ‖σ‖² m / (‖α‖² 10¹²)` with `m = min ρmin 1`
(`‖α‖ > 0`), and `‖σ‖² ≤ 64π²‖α‖²` kills `‖α‖²`:
`(32/ρmin + 16) m ≤ 32 + 16 = 48` (using `m ≤ ρmin` and `m ≤ 1`), leaving
`128π² · 48 / 10¹² ≤ 1/64` since `π² ≤ 16`.  (Note the hypothesis `‖α‖ ≤ m/10¹²` is not needed.)
-/

/-- The arithmetic gate `(32/ρmin + 16)‖σ‖²/(Re α ‖α‖ (10¹²/min ρmin 1)) ≤ 1/64`. -/
theorem gate_L1_arith {ρmin : ℝ} {α σ : ℂ} (hρmin : 0 < ρmin) (hinf : MandelDim.InF1 α)
    (hσ : ‖σ‖ ≤ 8 * Real.pi * ‖α‖) (hα : ‖α‖ ≤ min ρmin 1 / 10 ^ 12) :
    (32 / ρmin + 16) * ‖σ‖ ^ 2 * (1 / (α.re * ‖α‖ * (10 ^ 12 / min ρmin 1))) ≤ 1 / 64 := by
  -- ## basic positivity
  have ha : 0 < α.re := by
    have h := hinf; simp only [MandelDim.InF1] at h; linarith [abs_nonneg α.im]
  have ha_ne : α ≠ 0 := by intro h; rw [h] at ha; simp at ha
  have hm : 0 < min ρmin 1 := lt_min hρmin one_pos
  have hnpos : 0 < ‖α‖ := norm_pos_iff.mpr ha_ne
  have h10 : (0 : ℝ) < 10 ^ 12 := by norm_num
  have hden : 0 < α.re * ‖α‖ * (10 ^ 12 / min ρmin 1) :=
    mul_pos (mul_pos ha hnpos) (div_pos h10 hm)
  -- ## `𝓕₁` gives `Re α ≥ ‖α‖/2`
  have hn_le : ‖α‖ ≤ 2 * α.re := by
    have h3 : ‖α‖ ≤ |α.re| + |α.im| := Complex.norm_le_abs_re_add_abs_im α
    rw [abs_of_pos ha] at h3
    have h4 := hinf
    simp only [MandelDim.InF1] at h4
    linarith
  -- ## `‖σ‖² ≤ 64π²‖α‖²`
  have hS : ‖σ‖ ^ 2 ≤ 64 * Real.pi ^ 2 * ‖α‖ ^ 2 := by
    have h := pow_le_pow_left₀ (norm_nonneg σ) hσ 2
    have hexp : (8 * Real.pi * ‖α‖) ^ 2 = 64 * Real.pi ^ 2 * ‖α‖ ^ 2 := by ring
    rw [hexp] at h; exact h
  -- ## clear the denominators
  rw [mul_one_div, div_le_iff₀ hden]
  field_simp
  -- goal: `(32 + 16ρmin)‖σ‖²·64·(min ρmin 1) ≤ ρmin·Re α·‖α‖·10¹²`
  have hm_leρ : min ρmin 1 ≤ ρmin := min_le_left _ _
  have hm_le1 : min ρmin 1 ≤ 1 := min_le_right _ _
  have hA : (32 + 16 * ρmin) * (min ρmin 1) ≤ 48 * ρmin := by
    nlinarith [mul_le_mul_of_nonneg_right hm_leρ (by norm_num : (0 : ℝ) ≤ 32),
      mul_le_mul_of_nonneg_right hm_le1 (by positivity : (0 : ℝ) ≤ 16 * ρmin)]
  have hn2 : ‖α‖ ^ 2 ≤ 2 * α.re * ‖α‖ := by
    nlinarith [mul_le_mul_of_nonneg_right hn_le (norm_nonneg α)]
  have hnum : 48 * 64 * 64 * Real.pi ^ 2 ≤ (5 : ℝ) * 10 ^ 11 := by
    have hp2 : Real.pi ^ 2 ≤ 16 := by nlinarith [Real.pi_lt_four, Real.pi_pos]
    nlinarith
  have hL1 : (32 + 16 * ρmin) * ‖σ‖ ^ 2 * 64 * (min ρmin 1) ≤
      (48 * ρmin) * (64 * Real.pi ^ 2 * ‖α‖ ^ 2) * 64 := by
    have h1 := mul_le_mul_of_nonneg_right hA (by positivity : (0 : ℝ) ≤ ‖σ‖ ^ 2 * 64)
    have h2 := mul_le_mul_of_nonneg_left hS (by positivity : (0 : ℝ) ≤ 48 * ρmin * 64)
    nlinarith [h1, h2]
  have hL2 : (48 * ρmin) * (64 * Real.pi ^ 2 * ‖α‖ ^ 2) * 64 ≤ ρmin * α.re * ‖α‖ * 10 ^ 12 := by
    have h1 : (ρmin * ‖α‖ ^ 2) * (48 * 64 * 64 * Real.pi ^ 2) ≤
        (ρmin * ‖α‖ ^ 2) * ((5 : ℝ) * 10 ^ 11) :=
      mul_le_mul_of_nonneg_left hnum (by positivity)
    have h3 : ‖α‖ ^ 2 * ((5 : ℝ) * 10 ^ 11) ≤ (2 * α.re * ‖α‖) * ((5 : ℝ) * 10 ^ 11) :=
      mul_le_mul_of_nonneg_right hn2 (by norm_num)
    have h2 : (ρmin * ‖α‖ ^ 2) * ((5 : ℝ) * 10 ^ 11) ≤ ρmin * α.re * ‖α‖ * 10 ^ 12 := by
      nlinarith [h3, hρmin]
    nlinarith [h1, h2]
  linarith [hL1, hL2]

end Work.Pert
