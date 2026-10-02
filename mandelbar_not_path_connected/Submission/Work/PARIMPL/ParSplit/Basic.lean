/-
Copyright: subproject `Submission/Work/PARIMPL/ParSplit/` of `mandelbar_not_path_connected`.

# `Work.PARIMPL.ParSplit.Basic` — elementary steps towards `ParNormal`

This module collects the *elementary* (algebraic, or one-variable norm-estimate) steps needed
for `Work.PARIMPL.exists_parNormal`.  Nothing here depends on the (hard) parabolic splitting
theory; it is the layer on which both the splitting and the assembly build.

Mathematical content.

* `norm_sub_one_sq`, `seven_eighths_le_re`, `norm_sub_one_le_of_re` — the condition
  `‖τ‖ = 1 ∧ ‖τ - 1‖ ≤ 1/2` of `ParBounds` is equivalent to `7/8 ≤ Re τ`;
* `exists_unit_close_of_im`, `exists_unit_close_of_re` — the **phase tests**.  In the parameter
  normal form the scale `a` is forced by `‖h c 0‖ = 1` to satisfy `‖a c‖ = ‖2D‖/‖E‖` with
  `D = m c - Ft c (m c)` and `E` the difference of the two split fixed points; then
  `h c 0 = 2D/(E·a c)`, a unit complex number.  These lemmas say exactly that `‖h c 0 - 1‖ ≤ 1/2`
  holds *provided* `2D/E` is almost purely imaginary (implantation side, `a` forced to be
  positive imaginary) resp. almost real (the other side, `a` real), up to the free labelling of
  the two fixed points;
* `ne_zero_of_norm_sum_lt` — the elementary separation criterion: a polynomial whose constant
  term dominates the remaining terms on `‖z‖ ≤ r` has no zero there.  This is the substitute for
  Rouché's theorem in the count of the fixed points near `z₁`.
-/
import Mathlib
import Submission.Work.PARIMPL.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option linter.unusedVariables false

open Classical Filter Set Metric
open scoped Topology

noncomputable section

namespace Work.PARIMPL

/-! ## The `τ`-condition of `ParBounds` -/

/-- For a unit complex number, `‖τ - 1‖² = 2 - 2 Re τ`. -/
theorem norm_sub_one_sq (τ : ℂ) (hτ : ‖τ‖ = 1) : ‖τ - 1‖ ^ 2 = 2 - 2 * τ.re := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im]
  have hsq : (τ.re : ℝ) ^ 2 + τ.im ^ 2 = 1 := by
    have : Complex.normSq τ = 1 := by rw [← Complex.sq_norm, hτ]; norm_num
    simpa [Complex.normSq_apply, sq] using this
  nlinarith [hsq]

/-- A unit complex number with `‖τ - 1‖ ≤ 1/2` has real part at least `7/8`. -/
theorem seven_eighths_le_re {τ : ℂ} (hτ : ‖τ‖ = 1) (h : ‖τ - 1‖ ≤ 1 / 2) :
    7 / 8 ≤ τ.re := by
  have h2 := norm_sub_one_sq τ hτ
  have h3 : ‖τ - 1‖ ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by nlinarith [norm_nonneg (τ - 1)]
  nlinarith [h2 ▸ h3]

/-- Conversely, a unit complex number with real part at least `7/8` is within `1/2` of `1`. -/
theorem norm_sub_one_le_of_re {τ : ℂ} (hτ : ‖τ‖ = 1) (h : 7 / 8 ≤ τ.re) :
    ‖τ - 1‖ ≤ 1 / 2 := by
  have h2 := norm_sub_one_sq τ hτ
  have h3 : ‖τ - 1‖ ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by nlinarith
  nlinarith [norm_nonneg (τ - 1)]

/-! ## The phase tests -/

/-- The real part of `W/(I‖W‖)`. -/
theorem re_div_I_norm (W : ℂ) (hW : W ≠ 0) :
    (W / (Complex.I * (‖W‖ : ℂ))).re = W.im / ‖W‖ := by
  simp only [Complex.div_re, Complex.normSq_apply, Complex.mul_re, Complex.mul_im, Complex.I_re,
    Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, one_mul, mul_zero, sub_zero,
    add_zero, Complex.add_re, Complex.add_im, add_zero]
  field_simp
  ring

/-- The norm of `W/(I‖W‖)`. -/
theorem norm_div_I_norm (W : ℂ) (hW : W ≠ 0) : ‖W / (Complex.I * (‖W‖ : ℂ))‖ = 1 := by
  rw [norm_div, norm_mul, Complex.norm_I, one_mul, Complex.norm_real]
  simp only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg W)]
  exact div_self (ne_of_gt (norm_pos_iff.mpr hW))

/-- The real part of `W/‖W‖`. -/
theorem re_div_norm (W : ℂ) (hW : W ≠ 0) : (W / (‖W‖ : ℂ)).re = W.re / ‖W‖ := by
  simp only [Complex.div_re, Complex.normSq_apply, Complex.ofReal_re, Complex.ofReal_im, mul_zero]
  field_simp
  ring

/-- The norm of `W/‖W‖`. -/
theorem norm_div_norm (W : ℂ) (hW : W ≠ 0) : ‖W / (‖W‖ : ℂ)‖ = 1 := by
  rw [norm_div, Complex.norm_real]
  simp only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg W)]
  exact div_self (ne_of_gt (norm_pos_iff.mpr hW))

/-- **Implosion side.**  If `W ≠ 0` is almost purely imaginary, `7‖W‖ ≤ 8|Im W|`, then one of
the two values `±(W/(I‖W‖))` — the two possible values of `h c 0 = 2D/(E·a)` for the two
labellings of the split fixed points when `a` is positive imaginary — is within `1/2` of `1`. -/
theorem exists_unit_close_of_im (W : ℂ) (hW : W ≠ 0) (h : 7 * ‖W‖ ≤ 8 * |W.im|) :
    ‖W / (Complex.I * (‖W‖ : ℂ)) - 1‖ ≤ 1 / 2 ∨
      ‖-(W / (Complex.I * (‖W‖ : ℂ))) - 1‖ ≤ 1 / 2 := by
  have hn : 0 < ‖W‖ := norm_pos_iff.mpr hW
  have hφ : ‖W / (Complex.I * (‖W‖ : ℂ))‖ = 1 := norm_div_I_norm W hW
  have hr : (W / (Complex.I * (‖W‖ : ℂ))).re = W.im / ‖W‖ := re_div_I_norm W hW
  have key : 7 / 8 ≤ |W.im| / ‖W‖ := by
    rw [le_div_iff₀ hn]; nlinarith
  rcases lt_or_ge 0 W.im with hpos | hneg
  · left
    refine norm_sub_one_le_of_re hφ ?_
    rw [hr]; rw [abs_of_nonneg (le_of_lt hpos)] at key; exact key
  · right
    refine norm_sub_one_le_of_re ?_ ?_
    · rw [norm_neg]; exact hφ
    · rw [Complex.neg_re, hr]
      rw [abs_of_nonpos hneg] at key
      have : -(W.im / ‖W‖) = -W.im / ‖W‖ := by ring
      rw [this]; exact key

/-- **The other side.**  If `W ≠ 0` is almost real, `7‖W‖ ≤ 8|Re W|`, then one of the two
values `±(W/‖W‖)` — the two possible values of `h c 0 = 2D/(E·a)` for the two labellings, when
`a` is chosen real — is within `1/2` of `1`. -/
theorem exists_unit_close_of_re (W : ℂ) (hW : W ≠ 0) (h : 7 * ‖W‖ ≤ 8 * |W.re|) :
    ‖W / (‖W‖ : ℂ) - 1‖ ≤ 1 / 2 ∨ ‖-(W / (‖W‖ : ℂ)) - 1‖ ≤ 1 / 2 := by
  have hn : 0 < ‖W‖ := norm_pos_iff.mpr hW
  have hφ : ‖W / (‖W‖ : ℂ)‖ = 1 := norm_div_norm W hW
  have hr : (W / (‖W‖ : ℂ)).re = W.re / ‖W‖ := re_div_norm W hW
  have key : 7 / 8 ≤ |W.re| / ‖W‖ := by
    rw [le_div_iff₀ hn]; nlinarith
  rcases lt_or_ge 0 W.re with hpos | hneg
  · left
    refine norm_sub_one_le_of_re hφ ?_
    rw [hr]; rw [abs_of_nonneg (le_of_lt hpos)] at key; exact key
  · right
    refine norm_sub_one_le_of_re ?_ ?_
    · rw [norm_neg]; exact hφ
    · rw [Complex.neg_re, hr]
      rw [abs_of_nonpos hneg] at key
      have h' : -(W.re / ‖W‖) = -W.re / ‖W‖ := by ring
      rw [h']; exact key

/-! ## The separation criterion -/

/-- **Separation.**  If the constant term of a polynomial dominates the remaining terms on the
disc of radius `r`, then the polynomial has no zero there.  This is the elementary substitute
for Rouché's theorem in the count of the fixed points near `z₁`. -/
theorem ne_zero_of_norm_sum_lt {n : ℕ} {a : ℕ → ℂ} {z : ℂ} {r : ℝ}
    (hz : ‖z‖ ≤ r) (h0 : a 0 ≠ 0)
    (h : (∑ k ∈ Finset.range n, ‖a (k + 1)‖ * r ^ k) * r < ‖a 0‖) :
    (∑ k ∈ Finset.range (n + 1), a k * z ^ k) ≠ 0 := by
  intro hzero
  have hsplit : ∑ k ∈ Finset.range (n + 1), a k * z ^ k
      = a 0 + ∑ k ∈ Finset.range n, a (k + 1) * z ^ (k + 1) := by
    rw [Finset.sum_range_succ']
    simp only [pow_zero, mul_one]
    rw [add_comm]
  have hneg : (∑ k ∈ Finset.range n, a (k + 1) * z ^ (k + 1)) = -(a 0) := by
    rw [hsplit] at hzero
    exact Eq.symm (neg_eq_of_add_eq_zero_right hzero)
  have hnorm : ‖a 0‖ = ‖∑ k ∈ Finset.range n, a (k + 1) * z ^ (k + 1)‖ := by
    rw [hneg, norm_neg]
  have hle : ‖∑ k ∈ Finset.range n, a (k + 1) * z ^ (k + 1)‖
      ≤ (∑ k ∈ Finset.range n, ‖a (k + 1)‖ * r ^ k) * r := by
    calc ‖∑ k ∈ Finset.range n, a (k + 1) * z ^ (k + 1)‖
        ≤ ∑ k ∈ Finset.range n, ‖a (k + 1) * z ^ (k + 1)‖ := norm_sum_le _ _
      _ = ∑ k ∈ Finset.range n, ‖a (k + 1)‖ * ‖z‖ ^ (k + 1) := by
            apply Finset.sum_congr rfl
            intro k _
            rw [norm_mul, norm_pow]
      _ ≤ ∑ k ∈ Finset.range n, ‖a (k + 1)‖ * r ^ (k + 1) := by
            apply Finset.sum_le_sum
            intro k _
            exact mul_le_mul_of_nonneg_left
              (pow_le_pow_left₀ (norm_nonneg _) hz _) (norm_nonneg _)
      _ = (∑ k ∈ Finset.range n, ‖a (k + 1)‖ * r ^ k) * r := by
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro k _
            rw [pow_succ]; ring
  have hlt : ‖a 0‖ < ‖a 0‖ := by
    rw [hnorm]
    exact lt_of_le_of_lt hle (hnorm ▸ h)
  exact lt_irrefl _ hlt

end Work.PARIMPL
