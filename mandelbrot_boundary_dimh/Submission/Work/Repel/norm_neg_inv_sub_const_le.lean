import Mathlib

namespace Work.Repel

/-- Real part of `-1/w - s·i/η`: it equals `-(w.re / normSq w)`, independent of `s`.
(Proved by expanding the real parts of complex division/multiplication.) -/
private lemma re_helper (η s : ℝ) (w : ℂ) :
    (-1 / w - (s:ℂ) * Complex.I / η).re = -(w.re / Complex.normSq w) := by
  simp only [Complex.sub_re, Complex.neg_re, Complex.neg_im, Complex.div_re, Complex.one_re,
    Complex.one_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- Imaginary part of `-1/w - s·i/η`: it equals `w.im / normSq w - s/η`. -/
private lemma im_helper (η s : ℝ) (hη : η ≠ 0) (w : ℂ) :
    (-1 / w - (s:ℂ) * Complex.I / η).im = w.im / Complex.normSq w - s / η := by
  simp only [Complex.sub_im, Complex.neg_im, Complex.neg_re, Complex.div_im, Complex.one_im,
    Complex.one_re, Complex.mul_im, Complex.I_im, Complex.mul_re, Complex.I_re,
    Complex.ofReal_re, Complex.ofReal_im, Complex.normSq_ofReal]
  field_simp
  ring

/-- For `w` in the box `|Re w| ≤ η/8`, `|Im w - η| ≤ 1/8` with `η ≥ 100`, the quantity
`-1/w` is within `(1412/10000)/η` of `1.05 i/η`.

The whole content is the two-variable real inequality
`(x/s)² + (y/s - 1.05/η)² ≤ (1412/(10000 η))²` (with `s = x² + y²`), which after clearing
denominators is equivalent to `η² - 2.1 η y + c (x² + y²) ≤ 0` with `c = 422876/390625`; the
rectangle corners are where that quadratic function is extremal. -/
theorem norm_neg_inv_sub_const_le {η : ℝ} (hη : 100 ≤ η) {w : ℂ}
    (hre : |w.re| ≤ η / 8) (him : |w.im - η| ≤ 1 / 8) :
    ‖-1 / w - 1.05 * Complex.I / η‖ ≤ (1412 / 10000) / η := by
  have hηpos : 0 < η := by linarith
  have hηne : η ≠ 0 := ne_of_gt hηpos
  rcases abs_le.mp him with ⟨him1, him2⟩
  have hy_pos : 0 < w.im := by linarith
  have hw : w ≠ 0 := by
    intro h; rw [h] at hy_pos; simp at hy_pos
  have hs_pos : 0 < Complex.normSq w := Complex.normSq_pos.mpr hw
  rcases abs_le.mp hre with ⟨hre1, hre2⟩
  have hx2 : w.re^2 ≤ (η/8)^2 := by nlinarith [hre1, hre2]
  have hy2 : (w.im - η)^2 ≤ (1/8)^2 := by nlinarith [him1, him2]
  -- the extremal two-variable inequality on the box
  have hkey : η^2 - 2.1*η*w.im + (422876/390625)*(w.re^2 + w.im^2) ≤ 0 := by
    nlinarith [hx2, hy2, sq_nonneg (w.im - η), hη]
  have hzre : (-1 / w - 1.05 * Complex.I / η).re = -(w.re / Complex.normSq w) :=
    re_helper η (1.05) w
  have hzim : (-1 / w - 1.05 * Complex.I / η).im = w.im / Complex.normSq w - 1.05 / η :=
    im_helper η (1.05) hηne w
  have hsq : ‖-1 / w - 1.05 * Complex.I / η‖^2 ≤ ((1412 / 10000) / η)^2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hzre, hzim]
    simp only [Complex.normSq_apply]
    have hc : (1.05:ℝ)^2 - (1412/10000:ℝ)^2 = 422876/390625 := by norm_num
    field_simp
    nlinarith [hkey, hc]
  have htg : 0 ≤ (1412 / 10000) / η := by positivity
  have h := sq_le_sq.mp hsq
  rwa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg htg] at h

end Work.Repel
