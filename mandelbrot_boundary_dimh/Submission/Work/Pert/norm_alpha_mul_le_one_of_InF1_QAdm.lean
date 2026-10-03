import Mathlib
import Submission.Work.Pert.Setup

/-!
# PERT: `‖α‖ · Ξ ≤ 1` from `InF1 α` and the admissibility of the gate `Q(Ξ - 1/α, -Ξ)`

For `α` in Shishikura's class `𝓕₁` (`|Im α| < Re α`) the reciprocal obeys

`(1/α).re = α.re / ‖α‖² ≤ ‖α‖ / ‖α‖² = 1/‖α‖`,

an **upper** bound on `Re (1/α)` (the matching lower bound `1/(2‖α‖) < Re (1/α)` is
`Work.Pert.inv_re_lower`).  Admissibility of the lower gate
`Q(Ξ - 1/α, -Ξ)` says `Re (-Ξ) > Re (Ξ - 1/α) + 4`, i.e. `2Ξ + 4 < Re (1/α)`; chaining with
the upper bound gives `2Ξ < 1/‖α‖`, hence `‖α‖ · Ξ < 1/2 ≤ 1`.
-/

namespace Work.Pert

open MandelDim Complex

noncomputable section

/-- `InF1 α` bounds `Re (1/α)` **above** by `1/‖α‖`. -/
theorem inv_re_upper {α : ℂ} (hF1 : MandelDim.InF1 α) : (1 / α).re ≤ 1 / ‖α‖ := by
  have hre : 0 < α.re := lt_of_le_of_lt (abs_nonneg α.im) hF1
  have hne : α ≠ 0 := by intro hh; rw [hh] at hre; simp at hre
  have hnorm : 0 < ‖α‖ := norm_pos_iff.mpr hne
  have hinv : (1 / α).re = α.re / ‖α‖ ^ 2 := by
    simp only [one_div, Complex.inv_re, Complex.normSq_eq_norm_sq]
  rw [hinv, div_le_div_iff₀ (pow_pos hnorm 2) hnorm]
  nlinarith [Complex.re_le_norm α, norm_nonneg α]

/-- Admissibility of `Q(Ξ - 1/α, -Ξ)` reads `2Ξ + 4 < Re (1/α)`. -/
theorem two_mul_add_four_lt_inv_re {α : ℂ} {Ξ : ℝ}
    (hadm : MandelDim.QAdm (some ((Ξ : ℂ) - 1 / α)) (some (-(Ξ : ℂ)))) :
    2 * Ξ + 4 < (1 / α).re := by
  have h1 : ((Ξ : ℂ) - 1 / α) ∈ (some ((Ξ : ℂ) - 1 / α) : Option ℂ) := by simp
  have h2 : (-(Ξ : ℂ)) ∈ (some (-(Ξ : ℂ)) : Option ℂ) := by simp
  have h := hadm _ h1 _ h2
  simp only [Complex.sub_re, Complex.ofReal_re, Complex.neg_re] at h
  linarith

theorem norm_alpha_mul_le_one_of_InF1_QAdm {α : ℂ} {Ξ : ℝ} (hΞ : 0 < Ξ)
    (hinf : MandelDim.InF1 α)
    (hadm : MandelDim.QAdm (some ((Ξ : ℂ) - 1 / α)) (some (-(Ξ : ℂ)))) :
    ‖α‖ * Ξ ≤ 1 := by
  have hre : 0 < α.re := lt_of_le_of_lt (abs_nonneg α.im) hinf
  have hne : α ≠ 0 := by intro hh; rw [hh] at hre; simp at hre
  have hnorm : 0 < ‖α‖ := norm_pos_iff.mpr hne
  have hle : (1 / α).re ≤ 1 / ‖α‖ := inv_re_upper hinf
  have h2 : 2 * Ξ + 4 < (1 / α).re := two_mul_add_four_lt_inv_re hadm
  have h3 : 2 * Ξ < 1 / ‖α‖ := by linarith
  have hmul := mul_lt_mul_of_pos_right h3 hnorm
  rw [div_mul_cancel₀ 1 (ne_of_gt hnorm)] at hmul
  nlinarith [hmul, hΞ]

end

end Work.Pert
