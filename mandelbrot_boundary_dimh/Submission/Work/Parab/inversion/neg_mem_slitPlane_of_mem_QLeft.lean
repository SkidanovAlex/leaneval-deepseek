import Mathlib
import Submission.Work.Parab.Setup

namespace Work.Parab.inversion

open Complex

/-- **Distance of a sector point to the non-negative real axis.**
If `w` lies in Shishikura's sector `QLeft ξ` (`ξ > 0`) and `‖w‖ > ξ`, then every point
`t ≥ 0` of the ray `[0,∞) ⊂ ℂ` is at distance `> ‖w‖/8` from `w`.

Indeed, writing `w = a + ib` and using `QLeft ξ = {w | 2 Re(w+ξ) < ‖w+ξ‖}` (see
`Work.Parab.QLeft_iff`):

* if `a ≥ 0` the sector condition forces `3 (a+ξ)^2 < b^2`, whence `63 b^2 > a^2` and so
  `‖w‖^2 = a^2+b^2 < 64 b^2`, i.e. `|b| > ‖w‖/8`; since `‖w - t‖ ≥ |Im(w-t)| = |b|` we are done;
* if `a ≤ 0` then `‖w - t‖^2 = (a-t)^2 + b^2 ≥ a^2 + b^2 = ‖w‖^2 > (‖w‖/8)^2`.

(Note the second case needs only `‖w‖ > 0`, which follows from `ξ < ‖w‖`.) -/
lemma norm_div_eight_lt_norm_sub_ofReal {ξ : ℝ} (hξ : 0 < ξ) {w : ℂ}
    (hw : w ∈ MandelDim.QLeft ξ) (hwn : ξ < ‖w‖) :
    ∀ t : ℝ, 0 ≤ t → ‖w‖ / 8 < ‖w - (t : ℂ)‖ := by
  intro t ht
  have hQ : 2 * (w + ξ).re < ‖w + ξ‖ := (Work.Parab.QLeft_iff ξ w).mp hw
  have hQ' : 2 * (w.re + ξ) < ‖w + ξ‖ := by simpa using hQ
  have hsqw : ‖w‖ ^ 2 = w.re ^ 2 + w.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have hnormsq : ‖w - (t : ℂ)‖ ^ 2 = (w.re - t) ^ 2 + w.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      Complex.ofReal_re, Complex.ofReal_im]; ring
  have hwpos : 0 < ‖w‖ := by linarith
  by_cases ha : 0 ≤ w.re
  · -- `Re w ≥ 0`: the imaginary part is large.
    have hpos : 0 < 2 * (w.re + ξ) := by linarith
    have hsq : ‖w + ξ‖ ^ 2 = (w.re + ξ) ^ 2 + w.im ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im,
        Complex.ofReal_re, Complex.ofReal_im]; ring
    have h2 : (2 * (w.re + ξ)) ^ 2 < (‖w + ξ‖) ^ 2 := by
      exact sq_lt_sq.mpr (by
        rw [abs_of_pos hpos, abs_of_nonneg (norm_nonneg _)]; exact hQ')
    have h3 : 3 * (w.re + ξ) ^ 2 < w.im ^ 2 := by nlinarith [hsq, h2]
    have hb2 : 3 * w.re ^ 2 < w.im ^ 2 := by nlinarith [h3, ha, hξ]
    have hbig : ‖w‖ ^ 2 < 64 * w.im ^ 2 := by nlinarith [hb2, hsqw]
    have him : ‖w‖ / 8 < |w.im| := by
      have h8 : ‖w‖ < 8 * |w.im| := by
        have h1 : ‖w‖ ^ 2 < (8 * |w.im|) ^ 2 := by
          rw [mul_pow, sq_abs]; linarith [hbig]
        have h2' := sq_lt_sq.mp h1
        rwa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (by positivity)] at h2'
      linarith
    have himle : |w.im| ≤ ‖w - (t : ℂ)‖ := by
      have h1 : |w.im| ^ 2 ≤ ‖w - (t : ℂ)‖ ^ 2 := by
        rw [sq_abs, hnormsq]; nlinarith [sq_nonneg (w.re - t)]
      have h2' := sq_le_sq.mp h1
      simpa using h2'
    linarith
  · -- `Re w ≤ 0`: the point `w` itself is already far from the ray.
    have ha' : w.re ≤ 0 := le_of_not_ge ha
    have h1 : ‖w‖ ^ 2 ≤ ‖w - (t : ℂ)‖ ^ 2 := by
      rw [hnormsq, hsqw]; nlinarith [ht, ha', sq_nonneg t]
    have h2' := sq_le_sq.mp h1
    rw [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (norm_nonneg _)] at h2'
    linarith

/-- **The sector `QLeft ξ` avoids the interval `[0,∞)` by a definite margin.**
If `w ∈ QLeft ξ` with `ξ > 0`, `ξ < ‖w‖`, and `x` is within `‖w‖/8` of `w`, then `x` is not a
non-negative real number, i.e. `-x` lies in the slit plane `ℂ ∖ ℝ≤0`.

(Equivalently: `x` is at distance `> ‖w‖/8` from the ray `[0,∞)`.  This is what makes the
branch of `log(-·)` well defined and single-valued on the disc of radius `‖w‖/8` about `w`.) -/
theorem neg_mem_slitPlane_of_mem_QLeft {ξ : ℝ} (hξ : 0 < ξ) {w x : ℂ}
    (hw : w ∈ MandelDim.QLeft ξ) (hwn : ξ < ‖w‖) (hx : ‖x - w‖ ≤ ‖w‖ / 8) :
    -x ∈ Complex.slitPlane := by
  by_contra hcon
  rw [Complex.mem_slitPlane_iff] at hcon
  push Not at hcon
  obtain ⟨hre, him⟩ := hcon
  simp only [Complex.neg_re, Complex.neg_im] at hre him
  have hxre : 0 ≤ x.re := by linarith
  have hxim : x.im = 0 := by linarith
  -- `x` is the non-negative real number `x.re`
  have hxeq : x = ((x.re : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [hxim]
  have hkey := norm_div_eight_lt_norm_sub_ofReal hξ hw hwn x.re hxre
  have hlt : ‖w‖ / 8 < ‖x - w‖ := by
    rw [hxeq, norm_sub_rev]
    exact hkey
  linarith

end Work.Parab.inversion
