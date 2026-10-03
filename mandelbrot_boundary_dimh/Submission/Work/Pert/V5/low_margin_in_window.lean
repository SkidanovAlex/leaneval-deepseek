import Mathlib
import Submission.Work.Pert.V5.Basics
import Submission.Work.Pert.V5.Facts
import Submission.Work.Pert.V5.clear_lattice_gate

/-!
# `Work.Pert.V5.low_margin_in_window`

**The statement.**  Let `Qm Ξ α = Qreg (Ξ - 1/α) (-Ξ)` be the gate, with the two marginals
`mgA Ξ α z = Re z - Ξ + Re (1/α) + |Im z + Im (1/α)|` and `mgB Ξ z = |Im z| - Ξ - Re z`.  If
`z₀` is *cleared* (the closed ball of radius `2 Rde + 2` around it lies in the gate) and `ξ` is an
abscissa to the **right** of `z₀` at which the `mgB`-margin of the horizontal line through `z₀` has
dropped below `√2 Rde`, then `ξ` has already crossed the *window strip*, i.e.
`ξ > (Ξ - 1/α).re + 1 = Ξ - Re (1/α) + 1`.

In the corridor analysis of `Work.Pert.Phi_dev_gate_lin_v5` this is the case-analysis lemma: the
low-`mgB` end of the corridor at the pin's height is always inside the window strip, so the cheap
pointwise bound `‖Φ' - 1‖ ≤ 1/150 + 1/31` applies there (see `window_horiz_dev_le` in
`Work.Pert.V5.Facts`).

**Why it is true (the whole content).**  Write `A = Re (1/α)`, `B = Im (1/α)`, `x₀ = z₀.re`,
`y₀ = z₀.im`.  `MandelDim.InF1 α` (`|Im α| < Re α`) plus `‖α‖ ≤ 1/(32 (M+2+Ξ))` give the two
*unconditional* bounds

* `A ≥ 16 (M + 2 + Ξ)`  — inversion preserves the 45° sector, so `A ≥ 1/(√2 ‖α‖) ≥ 16√2 (M+2+Ξ)`;
* `|B| ≤ A`  — likewise, `1/α` stays in the sector;

and `zo_margins` turns the clearing hypothesis into `mgA z₀ > 2Rde + 2`, `mgB z₀ > 2Rde + 2`, i.e.

* `|y₀| - Ξ - x₀ > 2Rde + 2`,
* `x₀ - Ξ + A + |y₀ + B| > 2Rde + 2`.

Now suppose, for contradiction, `ξ ≤ Ξ - A + 1`.  Then `mgB (ξ + i y₀) = |y₀| - Ξ - ξ < √2 Rde`
taken together with `ξ ≤ Ξ - A + 1` gives the upper bound `|y₀| < 2Ξ - A + 1 + √2 Rde`; feeding
this into the two margin inequalities yields the *pair*

* `(2 - √2) Rde + 1 - Ξ - |B| < x₀`  (from `mgA z₀ > 2Rde+2`, using `|y₀ + B| ≤ |y₀| + |B|`),
* `x₀ < Ξ - A - 1 + (√2 - 2) Rde`  (from `mgB z₀ > 2Rde+2` and the upper bound on `|y₀|`),

whence `(4 - 2√2) Rde < 3Ξ - A - 2 + |B| ≤ 3Ξ - 2`.  On the other hand `ξ ≤ Ξ - A + 1` and
`mgB (ξ + i y₀) < √2 Rde` give `A - 2Ξ - 1 < √2 Rde`, so with `A ≥ 16(M+2+Ξ)`,

`16M + 14Ξ + 31 < √2 Rde < 2 Rde`, hence `8M + 7Ξ + 31/2 < Rde`; while
`(1/2) Rde < (4 - 2√2) Rde < 3Ξ - 2` gives `Rde < 6Ξ - 4 < 6Ξ`.  Adding,
`8M + Ξ + 31/2 < 0`, impossible since `M ≥ 2^10 > 0` and `Ξ > 0`.
-/

open Set Metric Filter
open scoped Topology

namespace Work.Pert.V5

noncomputable section

/-- `MandelDim.InF1 α` (`|Im α| < Re α`) says that `α` lies in the open 45° sector around the
positive real axis; inversion preserves that sector, so `|Im (1/α)| ≤ Re (1/α)`. -/
lemma lm_abs_im_inv_le_re_inv {α : ℂ} (hF1 : MandelDim.InF1 α) :
    |(1 / α).im| ≤ (1 / α).re := by
  have hre : 0 < α.re := lt_of_le_of_lt (abs_nonneg α.im) hF1
  have hne : α ≠ 0 := by intro h; rw [h] at hre; simp at hre
  have hns : 0 < Complex.normSq α := by
    rw [Complex.normSq_eq_norm_sq]; exact pow_pos (norm_pos_iff.mpr hne) 2
  rw [one_div, Complex.inv_im, Complex.inv_re, abs_div, abs_neg, abs_of_pos hns]
  exact div_le_div_of_nonneg_right hF1.le hns.le

/-- `MandelDim.InF1 α` and `‖α‖ ≤ 1/(32 (M+2+Ξ))` force the *unconditional* bound
`16 (M + 2 + Ξ) ≤ Re (1/α)`:  `Re (1/α) ≥ 1/(√2 ‖α‖) ≥ 16√2 (M+2+Ξ) ≥ 16 (M+2+Ξ)`. -/
lemma lm_sixteen_le_inv_re {Ξ M : ℝ} {α : ℂ} (hM : 2 ^ 10 ≤ M) (hΞ : 0 < Ξ)
    (hF1 : MandelDim.InF1 α) (hα : ‖α‖ ≤ 1 / (32 * (M + 2 + Ξ))) :
    16 * (M + 2 + Ξ) ≤ (1 / α).re := by
  have hM1024 : (1024 : ℝ) ≤ M := by have h := hM; norm_num at h; exact h
  have hX : 0 < M + 2 + Ξ := by linarith
  have hX32 : 0 < 32 * (M + 2 + Ξ) := by linarith
  have hnorm : 0 < ‖α‖ := by
    have hre : 0 < α.re := lt_of_le_of_lt (abs_nonneg α.im) hF1
    exact norm_pos_iff.mpr (by intro h; rw [h] at hre; simp at hre)
  have h1 : 1 / (Real.sqrt 2 * ‖α‖) ≤ (1 / α).re := Work.Pert.band_Qm_inv_re_lower hF1
  have hmul : ‖α‖ * (32 * (M + 2 + Ξ)) ≤ 1 := by
    have h := mul_le_mul_of_nonneg_right hα hX32.le
    rwa [one_div, inv_mul_cancel₀ hX32.ne'] at h
  have h2 : 16 * Real.sqrt 2 * (M + 2 + Ξ) ≤ 1 / (Real.sqrt 2 * ‖α‖) := by
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
  have h3 : 16 * (M + 2 + Ξ) ≤ 16 * Real.sqrt 2 * (M + 2 + Ξ) := by
    have hs : (1 : ℝ) ≤ Real.sqrt 2 := Real.one_le_sqrt.mpr (by norm_num)
    have := mul_nonneg (sub_nonneg.mpr hs) hX.le
    linarith
  linarith

/-- **The low-`mgB` end of the corridor at the pin's height lies in the window strip.**

If the closed ball of radius `2 Rde + 2` around `z₀` lies in the gate `Qm Ξ α` and at the abscissa
`ξ ≥ z₀.re`, at the height of `z₀`, the marginal `mgB` has fallen below `√2 Rde`, then `ξ` is past
the window threshold:  `(Ξ - 1/α).re + 1 < ξ`. -/
theorem low_margin_in_window {Ξ M Rde : ℝ} {α : ℂ} {z₀ : ℂ} {ξ : ℝ}
    (hΞ : 0 < Ξ) (hM : 2 ^ 10 ≤ M) (hInF1 : MandelDim.InF1 α)
    (hα : ‖α‖ ≤ 1 / (32 * (M + 2 + Ξ))) (hRde : 0 < Rde)
    (hcl : Metric.closedBall z₀ (2 * Rde + 2) ⊆ Work.Pert.Qm Ξ α)
    (hξlo : z₀.re ≤ ξ)
    (hξB : Work.Pert.V5.mgB Ξ ((ξ : ℂ) + (z₀.im : ℂ) * Complex.I) < Real.sqrt 2 * Rde) :
    ((Ξ : ℂ) - 1 / α).re + 1 < ξ := by
  have hgoal : ((Ξ : ℂ) - 1 / α).re = Ξ - (1 / α).re := by simp [Complex.sub_re]
  -- the clearing hypothesis, in real coordinates
  obtain ⟨hmA0, hmB0⟩ := zo_margins hRde hcl
  rw [mgA] at hmA0
  rw [mgB] at hmB0
  rw [mgB_re_im] at hξB
  rw [hgoal]
  by_contra hcon
  rw [not_lt] at hcon
  -- `ξ ≤ Ξ - A + 1` bounds the height of the pin from above
  have hy0_ub : |z₀.im| < 2 * Ξ - (1 / α).re + 1 + Real.sqrt 2 * Rde := by
    linarith [hξB, hcon]
  -- the two consequences of the margin inequalities
  have hxu : z₀.re < Ξ - (1 / α).re - 1 + (Real.sqrt 2 - 2) * Rde := by
    linarith [hmB0, hy0_ub]
  have hxl : (2 - Real.sqrt 2) * Rde + 1 - Ξ - |(1 / α).im| < z₀.re := by
    have habs : |z₀.im + (1 / α).im| ≤ |z₀.im| + |(1 / α).im| := abs_add_le _ _
    linarith [hmA0, habs, hy0_ub]
  have hiii : 2 * (2 - Real.sqrt 2) * Rde < 3 * Ξ - (1 / α).re - 2 + |(1 / α).im| := by
    linarith [hxl, hxu]
  have hBle : |(1 / α).im| ≤ (1 / α).re := lm_abs_im_inv_le_re_inv hInF1
  have hiii' : (4 - 2 * Real.sqrt 2) * Rde < 3 * Ξ - 2 := by linarith [hiii, hBle]
  -- `ξ ≤ Ξ - A + 1` also bounds `Rde` from below
  have hiv : (1 / α).re - 2 * Ξ - 1 < Real.sqrt 2 * Rde := by
    have h1 : |z₀.im| + (1 / α).re - 2 * Ξ - 1 ≤ |z₀.im| - Ξ - ξ := by linarith [hcon]
    linarith [h1, hξB, abs_nonneg z₀.im]
  have hA16 : 16 * (M + 2 + Ξ) ≤ (1 / α).re := lm_sixteen_le_inv_re hM hΞ hInF1 hα
  have hiv2 : 16 * M + 14 * Ξ + 31 < Real.sqrt 2 * Rde := by linarith [hiv, hA16]
  -- the two bounds on `Rde` are incompatible
  have hslt : Real.sqrt 2 < 2 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
  have h2 : Real.sqrt 2 * Rde < 2 * Rde := by
    nlinarith [mul_lt_mul_of_pos_right hslt hRde]
  have hA' : 8 * M + 7 * Ξ + 31 / 2 < Rde := by linarith [hiv2, h2]
  have hc4 : (1 / 2 : ℝ) < 4 - 2 * Real.sqrt 2 := by
    have hs2 : Real.sqrt 2 ≤ 3 / 2 := by
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
    linarith
  have h3 : (1 / 2 : ℝ) * Rde < (4 - 2 * Real.sqrt 2) * Rde :=
    mul_lt_mul_of_pos_right hc4 hRde
  have hB' : Rde < 6 * Ξ - 4 := by linarith [hiii', h3]
  have hM1024 : (1024 : ℝ) ≤ M := by have h := hM; norm_num at h; exact h
  linarith [hA', hB', hM1024, hΞ]

end

end Work.Pert.V5
