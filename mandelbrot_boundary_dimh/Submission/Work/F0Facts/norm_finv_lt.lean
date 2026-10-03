import Mathlib
import Submission.Work.F0Facts.FinvRegion
import Submission.Work.F0Facts.Basic

namespace Work.F0Facts

open Complex

/-- If `u.re ≥ 1` and `u ≠ 1` then `‖u + 1‖ > 2`.

(Indeed `‖u + 1‖ ≥ u.re + 1 ≥ 2`, and equality would force `u.re = 1` and `u.im = 0`,
i.e. `u = 1`.) -/
lemma two_lt_norm_add_one {u : ℂ} (hre : 1 ≤ u.re) (hne : u ≠ 1) : 2 < ‖u + 1‖ := by
  have hsq : ‖u + 1‖ ^ 2 = (u.re + 1) ^ 2 + u.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im,
      Complex.one_re, Complex.one_im]
    ring
  have hgt4 : 4 < ‖u + 1‖ ^ 2 := by
    rw [hsq]
    rcases eq_or_lt_of_le hre with h1 | h1
    · have him : u.im ≠ 0 := fun h => hne (Complex.ext h1.symm h)
      have hpos : 0 < u.im ^ 2 := sq_pos_of_ne_zero him
      nlinarith [h1, hpos]
    · nlinarith [sq_nonneg u.im, sq_nonneg (u.re - 1)]
  nlinarith [norm_nonneg (u + 1), sq_nonneg (‖u + 1‖ - 2)]

/-- On the repelling region, the inverse branch `finv w = (-1 + √(1+4w))/2` strictly
contracts: `‖finv w‖ < ‖w‖` for every `w ∈ repelling`, `w ≠ 0`.

Writing `σ = √(1 + 4w)`, so that `finv w = (σ - 1)/2` and `w = (σ² - 1)/4 =
(σ - 1)(σ + 1)/4`, the inequality reduces (after cancelling `‖σ - 1‖ > 0`, i.e. `w ≠ 0`)
to `‖σ + 1‖ > 2`, which holds because `σ.re ≥ 1` on `repelling` and `σ ≠ 1`. -/
theorem norm_finv_lt {w : ℂ} (hw : w ∈ repelling) (hw0 : w ≠ 0) : ‖finv w‖ < ‖w‖ := by
  set σ : ℂ := sqroot w with hσ
  have hσsq : σ ^ 2 = 1 + 4 * w := by
    rw [hσ, sqroot]; exact sqrt_sq (1 + 4 * w)
  have hsqrt : Complex.sqrt (1 + 4 * w) = σ := by rw [hσ, sqroot]
  have hσne1 : σ ≠ 1 := by
    intro h
    have h1 : (1 : ℂ) = 1 + 4 * w := by rw [← hσsq, h]; ring
    have h3 : (4 : ℂ) * w = 0 := by linear_combination -h1
    have h4 : w = 0 := (mul_eq_zero.mp h3).resolve_left (by norm_num)
    exact hw0 h4
  have ha : 1 ≤ σ.re := by
    rw [hσ]; exact one_le_re_sqroot_of_mem hw
  have hfinv : finv w = (σ - 1) / 2 := by
    rw [finv, hsqrt]; ring
  have hw_eq : w = (σ ^ 2 - 1) / 4 := by rw [hσsq]; ring
  rw [hfinv, hw_eq]
  have h1 : ‖(σ - 1) / 2‖ = ‖σ - 1‖ / 2 := by rw [norm_div]; norm_num
  have h2 : ‖(σ ^ 2 - 1) / 4‖ = ‖σ - 1‖ * ‖σ + 1‖ / 4 := by
    have hfac : σ ^ 2 - 1 = (σ - 1) * (σ + 1) := by ring
    rw [hfac, norm_div, norm_mul]; norm_num
  rw [h1, h2]
  have hc : 0 < ‖σ - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hσne1)
  have hkey : 2 < ‖σ + 1‖ := two_lt_norm_add_one ha hσne1
  nlinarith [hc, hkey]

end Work.F0Facts
