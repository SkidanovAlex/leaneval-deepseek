import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.PARIMPL.ParSplit

/-- **Phase lower bound for the normalized square.**

If `W ≠ 0` is almost real, `7‖W‖ ≤ 8|Re W|`, then the real part of `(W/‖W‖)²` is at least
`17/32`; if `W` is almost purely imaginary, `7‖W‖ ≤ 8|Im W|`, then the real part of the
*negative* of `(W/‖W‖)²` is at least `17/32`.

Equivalently: writing `z = W/‖W‖` (a unit complex number with `z.re = W.re/‖W‖`,
`z.im = W.im/‖W‖` and `z.re² + z.im² = 1`), the hypothesis `7‖W‖ ≤ 8|Re W|` gives
`|z.re| ≥ 7/8` hence `z.re² ≥ 49/64`, and `(z²).re = z.re² - z.im² = 2 z.re² - 1 ≥ 17/32`.
The imaginary case is symmetric, using `z.im` and `(-(z²)).re = z.im² - z.re² = 2 z.im² - 1`. -/
theorem phase_re_lower (W : ℂ) (hW : W ≠ 0) :
    (7 * ‖W‖ ≤ 8 * |W.re| → (17 : ℝ) / 32 ≤ ((W / ((‖W‖ : ℝ) : ℂ)) ^ 2).re) ∧
    (7 * ‖W‖ ≤ 8 * |W.im| → (17 : ℝ) / 32 ≤ (-((W / ((‖W‖ : ℝ) : ℂ)) ^ 2)).re) := by
  set r : ℝ := ‖W‖ with hr
  have hrpos : 0 < r := by rw [hr]; exact norm_pos_iff.mpr hW
  have hrne : r ≠ 0 := ne_of_gt hrpos
  set z : ℂ := W / (r : ℂ) with hz
  have hznorm : ‖z‖ = 1 := by
    rw [hz, norm_div]
    have hc : ‖(r : ℂ)‖ = r := by simp [abs_of_pos hrpos]
    rw [hc]
    exact div_self hrne
  have hznormsq : z.re ^ 2 + z.im ^ 2 = 1 := by
    have h : Complex.normSq z = 1 := by rw [Complex.normSq_eq_norm_sq, hznorm]; norm_num
    rw [Complex.normSq_apply] at h
    simpa [pow_two] using h
  have hzre : z.re = W.re / r := by
    rw [hz]
    simp only [Complex.div_re, Complex.normSq_apply, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, add_zero]
    field_simp
    ring
  have hzim : z.im = W.im / r := by
    rw [hz]
    simp only [Complex.div_im, Complex.normSq_apply, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero]
    field_simp
    ring
  have hzre2 : (z^2).re = z.re ^ 2 - z.im ^ 2 := by rw [pow_two, Complex.mul_re]; ring
  have hneg : (-(z^2)).re = z.im ^ 2 - z.re ^ 2 := by rw [Complex.neg_re, hzre2]; ring
  constructor
  · intro h
    have h7 : 7/8 ≤ |z.re| := by
      rw [hzre, abs_div, abs_of_pos hrpos, le_div_iff₀ hrpos]
      nlinarith [h]
    have hsq : (49:ℝ)/64 ≤ z.re ^ 2 := by
      have h' : (7/8:ℝ)^2 ≤ z.re^2 := by
        rw [← sq_abs z.re]
        exact pow_le_pow_left₀ (by norm_num) h7 2
      norm_num at h'
      linarith [h']
    calc (17:ℝ)/32 = 2 * ((49:ℝ)/64) - 1 := by norm_num
      _ ≤ 2 * z.re^2 - 1 := by linarith
      _ = z.re^2 - z.im^2 := by linarith [hznormsq]
      _ = (z^2).re := by rw [hzre2]
  · intro h
    have h7 : 7/8 ≤ |z.im| := by
      rw [hzim, abs_div, abs_of_pos hrpos, le_div_iff₀ hrpos]
      nlinarith [h]
    have hsq : (49:ℝ)/64 ≤ z.im ^ 2 := by
      have h' : (7/8:ℝ)^2 ≤ z.im^2 := by
        rw [← sq_abs z.im]
        exact pow_le_pow_left₀ (by norm_num) h7 2
      norm_num at h'
      linarith [h']
    calc (17:ℝ)/32 = 2 * ((49:ℝ)/64) - 1 := by norm_num
      _ ≤ 2 * z.im^2 - 1 := by linarith
      _ = z.im^2 - z.re^2 := by linarith [hznormsq]
      _ = (-(z^2)).re := by rw [hneg]

end Work.PARIMPL.ParSplit
