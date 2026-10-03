import Mathlib
import Submission.Work.Interfaces.Parabolic

/-!
# Elementary bounds for the rotation number `alphaOf a₁ a₂ β`

This file collects the crude estimates on
`alphaOf a₁ a₂ β = 1 / (a₁ - 1/(a₂ + β))` (Shishikura, Theorem 2, at the cusp `p/q = 0/1`)
that the §6 assembly (`Work.Repel.repel`) needs: for `a₁ ≥ 4`, `a₂ ≥ 4` and `0 ≤ Re β < 1`,

* `α = alphaOf a₁ a₂ β` lies in Shishikura's class `𝓕₁` (`|Im α| < Re α`, in particular `α ≠ 0`);
* `‖α‖ ≤ 4/a₁` and `1/α` stays small in modulus, `‖1/α‖`-type information in the form
  `Re(w) ≤ 1/4` with `w = 1/(a₂ + β)`, so that `‖a₁ - w‖ ≥ a₁/2`;
* `w = 1/(a₂ + β)` has `‖w‖ ≤ 1/a₂ ≤ 1/4`, `|Re w| ≤ 1/2`;
* `‖exp (2πi w) - 1‖ ≤ 32/a₂`.

Everything is proved from `‖a₂ + β‖ ≥ Re (a₂ + β) = a₂ + Re β ≥ a₂ ≥ 4`, so the constants are
crude but uniform in `β`.
-/

namespace Work.Repel

set_option linter.unusedVariables false

open MandelDim Complex Set Metric Filter Topology

/-- If `0 < c ≤ ‖z‖` then `‖1/z‖ ≤ 1/c`. -/
lemma norm_one_div_le_of_le_norm (z : ℂ) {c : ℝ} (hc : 0 < c) (h : c ≤ ‖z‖) :
    ‖(1 : ℂ) / z‖ ≤ 1 / c := by
  rw [one_div, norm_inv, one_div]
  exact (inv_le_inv₀ (lt_of_lt_of_le hc h) hc).mpr h

/-- For `‖w‖ ≤ c ≤ 1/4`, `‖exp (2πi w) - 1‖ ≤ 8π c`.

Proof: `x = 2πi w` has `‖x/2‖ = π‖w‖ ≤ π/4 < 1`, so that
`exp x - 1 = (exp (x/2) - 1)(exp (x/2) + 1)` is bounded by `‖x‖ · 4`: the first factor by
`Complex.norm_exp_sub_one_le`, the second by `‖exp (x/2)‖ + 1 ≤ e + 1 < 4`. -/
lemma exp_two_pi_I_mul_sub_one_le (w : ℂ) {c : ℝ} (hc4 : c ≤ 1 / 4)
    (hw : ‖w‖ ≤ c) : ‖Complex.exp (2 * Real.pi * Complex.I * w) - 1‖ ≤ 8 * Real.pi * c := by
  set x : ℂ := 2 * Real.pi * Complex.I * w with hx
  have h2 : ‖(2 : ℂ)‖ = 2 := by norm_num
  have hxnorm : ‖x‖ = 2 * Real.pi * ‖w‖ := by
    rw [hx]; simp [Complex.norm_I, Real.norm_eq_abs]
  have hhalf : ‖x / 2‖ ≤ 1 := by
    rw [norm_div, h2, hxnorm]
    have hlt : Real.pi * (1 / 4) < 1 := by linarith [Real.pi_lt_four]
    have hc1 : Real.pi * ‖w‖ ≤ Real.pi * (1 / 4) :=
      mul_le_mul_of_nonneg_left (le_trans hw hc4) (le_of_lt Real.pi_pos)
    have heq : 2 * Real.pi * ‖w‖ / 2 = Real.pi * ‖w‖ := by ring
    rw [heq]; linarith
  have h1 : ‖Complex.exp (x / 2) - 1‖ ≤ ‖x‖ := by
    have h := Complex.norm_exp_sub_one_le hhalf
    have heq : 2 * ‖x / 2‖ = ‖x‖ := by rw [norm_div, h2]; ring
    linarith
  have hplus : ‖Complex.exp (x / 2) + 1‖ ≤ 4 := by
    have h := norm_add_le (Complex.exp (x / 2)) (1 : ℂ)
    simp only [Complex.norm_exp, norm_one] at h
    have hre : (x / 2).re ≤ ‖x / 2‖ := Complex.re_le_norm _
    have hle : Real.exp (x / 2).re ≤ Real.exp 1 :=
      Real.exp_le_exp.mpr (le_trans hre hhalf)
    linarith [h, hle, Real.exp_one_lt_three]
  have hfac : Complex.exp x - 1 = (Complex.exp (x / 2) - 1) * (Complex.exp (x / 2) + 1) := by
    have hmul : (↑(2 : ℕ) : ℂ) * (x / 2) = x := by ring
    have hsq : Complex.exp x = Complex.exp (x / 2) ^ 2 := by
      conv_lhs => rw [← hmul]
      rw [Complex.exp_nat_mul]
    rw [hsq]; ring
  calc ‖Complex.exp x - 1‖
      = ‖(Complex.exp (x / 2) - 1) * (Complex.exp (x / 2) + 1)‖ := by rw [hfac]
    _ = ‖Complex.exp (x / 2) - 1‖ * ‖Complex.exp (x / 2) + 1‖ := norm_mul _ _
    _ ≤ ‖x‖ * 4 := mul_le_mul h1 hplus (norm_nonneg _) (norm_nonneg _)
    _ ≤ (2 * Real.pi * c) * 4 := by
        apply mul_le_mul_of_nonneg_right _ (by norm_num)
        rw [hxnorm]
        exact mul_le_mul_of_nonneg_left hw (by positivity)
    _ = 8 * Real.pi * c := by ring

theorem alphaOf_bounds (b : ℝ) (hb : 0 ≤ b) :
    ∃ N : ℕ, ∀ a₁ : ℕ, N ≤ a₁ → ∀ a₂ : ℕ, 4 ≤ a₂ → ∀ β : ℂ,
      0 ≤ β.re → β.re < 1 → |β.im| ≤ b →
      InF1 (alphaOf a₁ a₂ β) ∧
      ‖alphaOf a₁ a₂ β‖ ≤ 4 / (a₁ : ℝ) ∧
      ‖(1 : ℂ) / ((a₂ : ℂ) + β)‖ ≤ 2 / (a₂ : ℝ) ∧
      |((1 : ℂ) / ((a₂ : ℂ) + β)).re| ≤ 1 / 2 ∧
      ‖Complex.exp (2 * Real.pi * I * (1 / ((a₂ : ℂ) + β))) - 1‖ ≤ 32 / (a₂ : ℝ) ∧
      ‖(a₁ : ℂ) - 1 / ((a₂ : ℂ) + β)‖ ≥ (a₁ : ℝ) / 2 ∧
      alphaOf a₁ a₂ β ≠ 0 := by
  refine ⟨4, ?_⟩
  intro a₁ ha₁ a₂ ha₂ β hβre hβre' hβim
  have ha₁R : (4 : ℝ) ≤ (a₁ : ℝ) := by exact_mod_cast ha₁
  have ha₂R : (4 : ℝ) ≤ (a₂ : ℝ) := by exact_mod_cast ha₂
  have ha₁pos : (0 : ℝ) < (a₁ : ℝ) := by linarith
  have ha₂pos : (0 : ℝ) < (a₂ : ℝ) := by linarith
  set z : ℂ := (a₂ : ℂ) + β with hz
  set w : ℂ := 1 / z with hw
  have hzre : (a₂ : ℝ) ≤ z.re := by
    rw [hz, Complex.add_re]
    have : ((a₂ : ℂ)).re = (a₂ : ℝ) := by simp
    linarith
  have hznorm : (a₂ : ℝ) ≤ ‖z‖ := le_trans hzre (Complex.re_le_norm z)
  have hw_norm : ‖w‖ ≤ 1 / (a₂ : ℝ) := by
    rw [hw]
    exact norm_one_div_le_of_le_norm z ha₂pos hznorm
  have hle_quarter : 1 / (a₂ : ℝ) ≤ 1 / 4 :=
    one_div_le_one_div_of_le (show (0 : ℝ) < 4 by norm_num) ha₂R
  have hw_le_quarter : ‖w‖ ≤ 1 / 4 := le_trans hw_norm hle_quarter
  have hw_re_abs : |w.re| ≤ 1 / (a₂ : ℝ) := le_trans (Complex.abs_re_le_norm w) hw_norm
  have hw_im_abs : |w.im| ≤ 1 / (a₂ : ℝ) := le_trans (Complex.abs_im_le_norm w) hw_norm
  have hw_re_le_quarter : w.re ≤ 1 / 4 :=
    le_trans (le_trans (le_abs_self w.re) hw_re_abs) hle_quarter
  set u : ℂ := (a₁ : ℂ) - w with hu
  have hu_re : u.re = (a₁ : ℝ) - w.re := by rw [hu, Complex.sub_re]; simp
  have hu_im : u.im = -w.im := by rw [hu, Complex.sub_im]; simp
  have hu_re_ge : (a₁ : ℝ) / 2 ≤ u.re := by
    rw [hu_re]; linarith [ha₁R, hw_re_le_quarter]
  have hu_norm : (a₁ : ℝ) / 2 ≤ ‖u‖ := le_trans hu_re_ge (Complex.re_le_norm u)
  have hu_ne : u ≠ 0 := by
    intro h0
    rw [h0] at hu_norm
    simp at hu_norm
    linarith
  have hαu : alphaOf a₁ a₂ β = 1 / u := by rw [alphaOf, ← hz, ← hw, ← hu]
  have h_inF1 : InF1 (1 / u) := by
    have hpos : 0 < Complex.normSq u := Complex.normSq_pos.mpr hu_ne
    have him : |u.im| < u.re := by
      have h1 : |u.im| ≤ 1 / 4 := by
        rw [hu_im, abs_neg]
        exact le_trans hw_im_abs hle_quarter
      have h2 : (15 : ℝ) / 4 ≤ u.re := by
        rw [hu_re]; linarith [ha₁R, hw_re_le_quarter]
      linarith
    unfold InF1
    rw [one_div, Complex.inv_re, Complex.inv_im, abs_div, abs_neg, abs_of_pos hpos]
    exact (div_lt_div_iff_of_pos_right hpos).mpr him
  have h_αnorm : ‖1 / u‖ ≤ 4 / (a₁ : ℝ) := by
    have h := norm_one_div_le_of_le_norm u (c := (a₁ : ℝ) / 2) (by linarith) hu_norm
    rw [one_div_div] at h
    exact le_trans h (div_le_div_of_nonneg_right (by norm_num) (le_of_lt ha₁pos))
  have h_w2 : ‖(1 : ℂ) / ((a₂ : ℂ) + β)‖ ≤ 2 / (a₂ : ℝ) := by
    rw [← hz, ← hw]
    exact le_trans hw_norm (div_le_div_of_nonneg_right (by norm_num) (le_of_lt ha₂pos))
  have h_re : |((1 : ℂ) / ((a₂ : ℂ) + β)).re| ≤ 1 / 2 := by
    rw [← hz, ← hw]
    exact le_trans hw_re_abs
      (one_div_le_one_div_of_le (show (0 : ℝ) < 2 by norm_num) (by linarith))
  have h_exp : ‖Complex.exp (2 * Real.pi * I * (1 / ((a₂ : ℂ) + β))) - 1‖ ≤ 32 / (a₂ : ℝ) := by
    rw [← hz, ← hw]
    have h := exp_two_pi_I_mul_sub_one_le w (c := 1 / (a₂ : ℝ)) hle_quarter hw_norm
    have h32 : 8 * Real.pi * (1 / (a₂ : ℝ)) ≤ 32 / (a₂ : ℝ) := by
      have hpi : 8 * Real.pi ≤ 32 := by linarith [Real.pi_lt_four]
      rw [show 8 * Real.pi * (1 / (a₂ : ℝ)) = 8 * Real.pi / (a₂ : ℝ) by ring]
      exact div_le_div_of_nonneg_right hpi (le_of_lt ha₂pos)
    linarith
  have h_u : ‖(a₁ : ℂ) - 1 / ((a₂ : ℂ) + β)‖ ≥ (a₁ : ℝ) / 2 := by
    rw [← hz, ← hw, ← hu]; exact hu_norm
  have h_ne : alphaOf a₁ a₂ β ≠ 0 := by
    rw [hαu]; exact div_ne_zero one_ne_zero hu_ne
  rw [hαu]
  exact ⟨h_inF1, h_αnorm, h_w2, h_re, h_exp, h_u, h_ne⟩

end Work.Repel
