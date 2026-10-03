import Mathlib
import Submission.Work.Pert.V5.W2.Setup

/-!
# `Work.Pert.V5.W2.xiB_gt_edge`

**The left edge of the window strip lies strictly below the `mgB`-crossing `ξ_B`.**

Write `A := Re (1/α)`, `B := Im (1/α)`, `ξ_B := |z₀.im| - Ξ - √2 Rde` (the abscissa at which
`mgB (· + i z₀.im)` crosses `√2 Rde`) and `c := ((Ξ : ℂ) - 1/α).re + 1 = Ξ - A + 1` (the left edge
of the window strip `{z | c < z.re < -Ξ - 3}`).  The lemma says `c < ξ_B`, i.e.

  `A + |z₀.im| > 2Ξ + 1 + √2 Rde`.

The two inputs are

* `α ∈ 𝓕₁` with `‖α‖ ≤ 1/(32 (M+2+Ξ))` forces `A = Re (1/α) ≥ 1/(√2 ‖α‖) ≥ 16√2 (M+2+Ξ)`, so in
  particular `A ≥ 5Ξ + 5`; and `|B| ≤ A` (`InF1` says `|Im α| ≤ Re α`);
* the clearing hypothesis `closedBall z₀ (2 Rde + 2) ⊆ Qm Ξ α` gives both gate margins at the pin,
  `mgA z₀ > 2 Rde + 2` and `mgB z₀ > 2 Rde + 2` (`zo_margins`), i.e.
  `z₀.re - Ξ + A + |z₀.im + B| > 2 Rde + 2` and `|z₀.im| - Ξ - z₀.re > 2 Rde + 2`.
  Adding them and using `|z₀.im + B| ≤ |z₀.im| + |B| ≤ |z₀.im| + A` yields
  `4 Rde + 4 < 2 (A + |z₀.im|) - 2Ξ`, whence `√2 Rde < (3/2) Rde < (3/4)(A + |z₀.im| - Ξ - 2)`, and
  the last quantity is `≤ A + |z₀.im| - 2Ξ - 1` because `A ≥ 5Ξ + 5`.
-/

namespace Work.Pert.V5.W2

noncomputable section

set_option maxHeartbeats 1000000

/-! ## Elementary bounds on `Re (1/α)` and `Im (1/α)` for `α ∈ 𝓕₁` -/

/-- For `α ∈ 𝓕₁` with `‖α‖ ≤ 1/(32 (M+2+Ξ))`: `Re (1/α) ≥ 5Ξ + 5`.

Indeed `Re (1/α) ≥ 1/(√2 ‖α‖) ≥ 16√2 (M+2+Ξ) ≥ 5Ξ + 5`. -/
lemma xiB_inv_re_lower {Ξ M : ℝ} {α : ℂ}
    (hΞ : 0 < Ξ) (hM : 2 ^ 10 ≤ M) (hInF1 : MandelDim.InF1 α)
    (hα : ‖α‖ ≤ 1 / (32 * (M + 2 + Ξ))) :
    5 * Ξ + 5 ≤ (1 / α).re := by
  have hX : 0 < M + 2 + Ξ := by linarith
  have hX32 : (0 : ℝ) < 32 * (M + 2 + Ξ) := by linarith
  have hnormpos : 0 < ‖α‖ := by
    have hre : 0 < α.re := lt_of_le_of_lt (abs_nonneg α.im) hInF1
    exact norm_pos_iff.mpr (by intro h; rw [h] at hre; simp at hre)
  have h1 : 1 / (Real.sqrt 2 * ‖α‖) ≤ (1 / α).re := Work.Pert.band_Qm_inv_re_lower hInF1
  have hmul : ‖α‖ * (32 * (M + 2 + Ξ)) ≤ 1 := by
    have h := mul_le_mul_of_nonneg_right hα hX32.le
    rwa [one_div, inv_mul_cancel₀ hX32.ne'] at h
  have h2 : 32 * (M + 2 + Ξ) ≤ 1 / ‖α‖ := by
    rw [le_div_iff₀ hnormpos]
    linarith
  have h3 : 16 * Real.sqrt 2 * (M + 2 + Ξ) ≤ 1 / (Real.sqrt 2 * ‖α‖) := by
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < Real.sqrt 2 * ‖α‖)]
    have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
    have heq : 16 * Real.sqrt 2 * (M + 2 + Ξ) * (Real.sqrt 2 * ‖α‖)
        = ‖α‖ * (32 * (M + 2 + Ξ)) := by
      calc 16 * Real.sqrt 2 * (M + 2 + Ξ) * (Real.sqrt 2 * ‖α‖)
          = 16 * (Real.sqrt 2 * Real.sqrt 2) * ((M + 2 + Ξ) * ‖α‖) := by ring
        _ = 16 * 2 * ((M + 2 + Ξ) * ‖α‖) := by rw [hs2]
        _ = ‖α‖ * (32 * (M + 2 + Ξ)) := by ring
    rw [heq]
    linarith
  have h4 : 5 * Ξ + 5 ≤ 16 * Real.sqrt 2 * (M + 2 + Ξ) := by
    have hs : (7 : ℝ) / 5 ≤ Real.sqrt 2 := by
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
    have h22 : 5 * Ξ + 5 ≤ 22 * (M + 2 + Ξ) := by linarith
    have hcoef : (22 : ℝ) ≤ 16 * Real.sqrt 2 := by linarith
    calc 5 * Ξ + 5 ≤ 22 * (M + 2 + Ξ) := h22
      _ ≤ 16 * Real.sqrt 2 * (M + 2 + Ξ) := by
          have := mul_le_mul_of_nonneg_right hcoef hX.le
          linarith
  linarith

/-- For `α ∈ 𝓕₁`: `|Im (1/α)| ≤ Re (1/α)`. -/
lemma xiB_inv_im_le {α : ℂ} (hInF1 : MandelDim.InF1 α) : |(1 / α).im| ≤ (1 / α).re := by
  have hre : 0 < α.re := lt_of_le_of_lt (abs_nonneg α.im) hInF1
  have hne : α ≠ 0 := by intro h; rw [h] at hre; simp at hre
  have hnormpos : 0 < ‖α‖ := norm_pos_iff.mpr hne
  have hIm : |α.im| ≤ α.re := le_of_lt hInF1
  have h1 : (1 / α).im = -α.im / ‖α‖ ^ 2 := by
    rw [one_div, Complex.inv_im, Complex.normSq_eq_norm_sq]
  have h2 : (1 / α).re = α.re / ‖α‖ ^ 2 := by
    rw [one_div, Complex.inv_re, Complex.normSq_eq_norm_sq]
  rw [h1, h2, abs_div, abs_neg, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖α‖ ^ 2)]
  exact div_le_div_of_nonneg_right hIm (by positivity)

/-! ## The lemma -/

theorem xiB_gt_edge {Ξ M Rde : ℝ} {α : ℂ} {z₀ : ℂ}
    (hΞ : 0 < Ξ) (hM : 2 ^ 10 ≤ M) (hInF1 : MandelDim.InF1 α)
    (hα : ‖α‖ ≤ 1 / (32 * (M + 2 + Ξ))) (hRde : 0 < Rde)
    (hcl : Metric.closedBall z₀ (2 * Rde + 2) ⊆ Work.Pert.Qm Ξ α) :
    ((Ξ : ℂ) - 1 / α).re + 1 < |z₀.im| - Ξ - Real.sqrt 2 * Rde := by
  have hA : 5 * Ξ + 5 ≤ (1 / α).re := xiB_inv_re_lower hΞ hM hInF1 hα
  have hB : |(1 / α).im| ≤ (1 / α).re := xiB_inv_im_le hInF1
  obtain ⟨hmA, hmB⟩ := Work.Pert.V5.zo_margins hRde hcl
  simp only [mgA, mgB] at hmA hmB
  -- add the two margin inequalities and bound `|z₀.im + (1/α).im|`
  have htri : |z₀.im + (1 / α).im| ≤ |z₀.im| + |(1 / α).im| := abs_add_le _ _
  have hy : (0 : ℝ) ≤ |z₀.im| := abs_nonneg _
  have hsum : 4 * Rde + 4 < 2 * ((1 / α).re + |z₀.im|) - 2 * Ξ := by linarith
  have hR : Rde < ((1 / α).re + |z₀.im| - Ξ - 2) / 2 := by linarith
  have hs32 : Real.sqrt 2 < 3 / 2 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
  have hsR : Real.sqrt 2 * Rde < (3 / 2) * Rde := mul_lt_mul_of_pos_right hs32 hRde
  have h3 : (3 / 2) * Rde < (3 / 4) * ((1 / α).re + |z₀.im| - Ξ - 2) := by linarith
  have h4 : (3 / 4) * ((1 / α).re + |z₀.im| - Ξ - 2)
      ≤ (1 / α).re + |z₀.im| - 2 * Ξ - 1 := by linarith
  have hmain : 2 * Ξ + 1 + Real.sqrt 2 * Rde < (1 / α).re + |z₀.im| := by linarith
  have hre : ((Ξ : ℂ) - 1 / α).re = Ξ - (1 / α).re := by
    simp [Complex.sub_re]
  rw [hre]
  linarith

end

end Work.Pert.V5.W2
