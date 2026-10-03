import Mathlib
import Submission.Work.Pert.Setup
import Submission.Work.Pert.Basic
import Submission.Work.Pert.gate_geom_facts
import Submission.Work.Pert.walk_gate_mono
import Submission.Work.Pert.Qm_slice
import Submission.Work.Pert.GateDriftRate.waist_walk_re
import Submission.Work.Pert.GateDriftRate.waist_geo_re

namespace Work.Pert.GateDriftRate

open Complex

/-!
# `Work.Pert.GateDriftRate.waist_diam_le`

The *waist* of a legal gate walk: two points `w j`, `w j'` (`j, j' ≤ n`) of the walk which both
lie in the strip `|Im (α · w)| < 1` have their *phase* `Re (α · w)` in an interval of length
`≤ 200`, and their real parts within `200 / ‖α‖`.

The proof splits on the aspect ratio of `α = a + bi` (`a = Re α > |Im α| = |b|`, the hypothesis
`MandelDim.InF1`):

* **steep case** `|b| ≥ ‖α‖/16` (`waist_walk_re`, proved in this directory): each `1/32`-near
  translation moves `Im (α · (w (j+1) - w j))` by `b` with error at most `‖α‖/32`, so the
  imaginary parts of two waist points differ by at least `‖α‖/32` per step; staying in
  `|Im (α · w)| < 1` therefore bounds `|j - j'|` by `64/‖α‖` and the phase difference by `66`.

* **shallow case** `|b| ≤ ‖α‖/16` (`waist_geo_re`, proved in this directory): `α` is nearly real
  (`a ≥ 255‖α‖/256`), and the two defining inequalities of the gate `Qm Ξ α`, together with
  `|Im (α · w)| < 1` alone (no walk needed), squeeze `Re (α · w)` into an interval of length `< 3`.

Both cases give `|Re (α · w j) - Re (α · w j')| ≤ 66`, and the statement on the real parts follows
from the linear relation `a · Re (α w) + b · Im (α w) = ‖α‖² · Re w`.
-/

/-- The linear relation between a point `w` and its image `α * w`: multiplying the real part of
`α * w` by `α.re` and the imaginary part by `α.im` recovers `‖α‖² · Re w`. -/
private lemma re_mul_re_add_im_mul_im (α w : ℂ) :
    α.re * (α * w).re + α.im * (α * w).im = Complex.normSq α * w.re := by
  rw [Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
  ring

/-- Difference form of `re_mul_re_add_im_mul_im`. -/
private lemma normSq_mul_re_sub (α z z' : ℂ) :
    Complex.normSq α * (z.re - z'.re)
      = α.re * ((α * z).re - (α * z').re) + α.im * ((α * z).im - (α * z').im) := by
  have h1 := re_mul_re_add_im_mul_im α z
  have h2 := re_mul_re_add_im_mul_im α z'
  linarith

/-- The imaginary parts of the two `α`-images differ by at most `2` when both lie in the
waist `|Im (α · w)| < 1`. -/
private lemma abs_im_sub_le_two {α z z' : ℂ}
    (h : |(α * z).im| < 1) (h' : |(α * z').im| < 1) :
    |(α * z).im - (α * z').im| ≤ 2 := by
  have habs := abs_add_le (α * z).im (-((α * z').im))
  rw [abs_neg] at habs
  have h2 : |(α * z).im - (α * z').im| ≤ |(α * z).im| + |(α * z').im| := by
    simpa [sub_eq_add_neg] using habs
  linarith

/-- **The waist diameter bound.**  Any two points of the walk `w` (indices `≤ n`) which lie in the
waist `|Im (α · w)| < 1` have phases `Re (α · w)` within `200`, and real parts within
`200 / ‖α‖`. -/
theorem waist_diam_le {Ξ : ℝ} {α : ℂ} {w : ℕ → ℂ} {n : ℕ}
    (hΞ : 0 < Ξ) (hInF1 : MandelDim.InF1 α)
    (hstep : ∀ j < n, ‖w (j + 1) - (w j + 1)‖ ≤ 1 / 32)
    (hgate : ∀ j ≤ n, w j ∈ Work.Pert.Qm Ξ α) :
    ∀ j j' : ℕ, j ≤ n → j' ≤ n → |(α * w j).im| < 1 → |(α * w j').im| < 1 →
      |(α * w j).re - (α * w j').re| ≤ 200 ∧
      |(w j).re - (w j').re| ≤ 200 / ‖α‖ := by
  -- Step 1: the phase difference is at most `66` in both aspect regimes.
  have key1 : ∀ (j j' : ℕ), j ≤ n → j' ≤ n → |(α * w j).im| < 1 → |(α * w j').im| < 1 →
      |(α * w j).re - (α * w j').re| ≤ 66 := by
    intro j j' hj hj' h1 h2
    by_cases hcase : ‖α‖ / 16 ≤ |α.im|
    · exact waist_walk_re hstep hcase j j' hj hj' h1 h2
    · push Not at hcase
      have ha := waist_geo_re (le_of_lt hΞ) hInF1 (hgate j hj) (le_of_lt hcase) h1
      have hb := waist_geo_re (le_of_lt hΞ) hInF1 (hgate j' hj') (le_of_lt hcase) h2
      have h := abs_add_le (α * w j).re (-((α * w j').re))
      rw [abs_neg] at h
      have h2' : |(α * w j).re - (α * w j').re| ≤ |(α * w j).re| + |(α * w j').re| := by
        simpa [sub_eq_add_neg] using h
      linarith
  intro j j' hj hj' h1 h2
  have hA := key1 j j' hj hj' h1 h2
  -- `α ≠ 0` and `‖α‖ > 0`, from `InF1 α`.
  have ha : 0 < α.re := lt_of_le_of_lt (abs_nonneg (α.im)) hInF1
  have hane : α ≠ 0 := by
    intro h; rw [h] at ha; simp at ha
  have hRpos : 0 < ‖α‖ := norm_pos_iff.mpr hane
  have hu : 0 < Complex.normSq α := Complex.normSq_pos.mpr hane
  -- Step 2: the real parts.  The linear relation gives
  -- `‖α‖² · (Re w j - Re w j') = α.re · (Δφ) + α.im · (Δψ)` with `|Δφ| ≤ 66`, `|Δψ| ≤ 2`.
  have hB := abs_im_sub_le_two h1 h2
  have hmain : Complex.normSq α * |(w j).re - (w j').re| ≤ 68 * ‖α‖ := by
    have habs : Complex.normSq α * |(w j).re - (w j').re|
        = |Complex.normSq α * ((w j).re - (w j').re)| := by
      rw [abs_mul, abs_of_pos hu]
    rw [habs, normSq_mul_re_sub]
    set X : ℝ := (α * w j).re - (α * w j').re with hX
    set Y : ℝ := (α * w j).im - (α * w j').im with hY
    have hXY : |α.re * X + α.im * Y| ≤ |α.re| * |X| + |α.im| * |Y| := by
      calc |α.re * X + α.im * Y| ≤ |α.re * X| + |α.im * Y| := abs_add_le _ _
        _ = |α.re| * |X| + |α.im| * |Y| := by rw [abs_mul, abs_mul]
    have hXb : |X| ≤ 66 := by rw [hX]; exact hA
    have hYb : |Y| ≤ 2 := by rw [hY]; exact hB
    have h1r : |α.re| ≤ ‖α‖ := Complex.abs_re_le_norm α
    have h1i : |α.im| ≤ ‖α‖ := Complex.abs_im_le_norm α
    nlinarith [hXY, hXb, hYb, h1r, h1i, abs_nonneg α.re, abs_nonneg α.im,
      abs_nonneg X, abs_nonneg Y, norm_nonneg α]
  have hfin : |(w j).re - (w j').re| ≤ 68 / ‖α‖ := by
    have h2 : |(w j).re - (w j').re| ≤ 68 * ‖α‖ / Complex.normSq α := by
      rw [le_div_iff₀ hu, mul_comm]; exact hmain
    rw [Complex.normSq_eq_norm_sq, show 68 * ‖α‖ / ‖α‖ ^ 2 = 68 / ‖α‖ by field_simp] at h2
    exact h2
  refine ⟨by linarith, ?_⟩
  have hle : (68 : ℝ) / ‖α‖ ≤ 200 / ‖α‖ :=
    div_le_div_of_nonneg_right (by norm_num) (le_of_lt hRpos)
  linarith

end Work.Pert.GateDriftRate
