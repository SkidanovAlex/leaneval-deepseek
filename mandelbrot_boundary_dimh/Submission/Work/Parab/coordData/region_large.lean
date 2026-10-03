import Mathlib
import Submission.Work.Parab.Setup

namespace Work.Parab.coordData

open Complex

/-- **A quantitative sector bound.**  If `2 Re z < ‖z‖` (i.e. `|arg z| > π/3`) and
additionally `Re z ≥ -‖z‖/2` (i.e. `arg z` is not past `±2π/3`), then `|Im z|` is
comparable to `‖z‖`: indeed `|Im z| > (17/20)‖z‖` (in fact `≥ (√3/2)‖z‖ > 0.85 ‖z‖`).

This is the numerical input of `region_large`: a point of the sector `QLeft ξ` (translated
by `ξ`) with `Re` not too negative has a large imaginary part. -/
lemma abs_im_lower {z : ℂ} (h : 2 * z.re < ‖z‖) (h2 : -‖z‖ / 2 ≤ z.re) :
    (17 / 20 : ℝ) * ‖z‖ < |z.im| := by
  have hz0 : z ≠ 0 := by
    intro hz; rw [hz] at h; simp at h
  have hs0 : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  have hre : z.re ^ 2 ≤ (‖z‖ / 2) ^ 2 := by nlinarith [h, h2]
  have hsq : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have him : ((17 / 20 : ℝ) * ‖z‖) ^ 2 < z.im ^ 2 := by nlinarith [hre, hsq, hs0]
  have := sq_lt_sq.mp him
  simpa [abs_of_nonneg (by positivity : (0:ℝ) ≤ 17 / 20 * ‖z‖)] using this

/-- **The two-region description of the ζ-plane left coordinate near a far sector.**  If `M₀, M₁, ξ₁ > 0`, then for all large enough `ξ₀ ≥ ξ₁`: every point `y` that lies within `‖u‖ / 4 + 4` of a point `u` of the sector `QLeft ξ₀` (i.e. `|arg (u + ξ₀)| > π/3`) lies in the union
`{Re < -M₀} ∪ {M₁ < |Im|, Re < 3 |Im|}`,
the region which the left (repelling) coordinate's domain `L` always contains.

Proof sketch (`Work.Parab.QLeft_iff` gives `2 α < s` for `α = (u + ξ₀).re`, `s = ‖u + ξ₀‖`; also
`‖u‖ ≤ s + ξ₀`, `u.re = α - ξ₀`, `|u.im| = |(u + ξ₀).im|`, `|(u + ξ₀).im| ^ 2 = s ^ 2 - α ^ 2`).
Take `ξ₀ = max ξ₁ (1000 * (M₀ + M₁ + 1) + 1)`; let `δ = ‖y - u‖ ≤ ‖u‖ / 4 + 4`, so
`y.re ≤ u.re + δ` and `|y.im| ≥ |u.im| - δ`.
* `α < -s / 2`:  `y.re ≤ -s/4 - 3ξ₀/4 + 4 < -M₀`.
* `α ≥ -s / 2` (so `|α| < s/2`, hence `|u.im| > (√3/2)s ≥ (17/20)s`, using `√3 > 17/10`):
  - `s ≤ ξ₀/2`: `y.re ≤ 3s/4 - 3ξ₀/4 + 4 ≤ -3ξ₀/8 + 4 < -M₀`;
  - `s > ξ₀/2`: `|y.im| ≥ (17/20)s - (s + ξ₀)/4 - 4 ≥ ξ₀/20 - 4 > M₁`, and
    `y.re ≤ 3s/4 - 3ξ₀/4 + 4 < 1.8s - 3ξ₀/4 - 12 ≤ 3|y.im|` since `s > ξ₀/2 ≥ 500`.
(Any constant in place of `1000` above `64` works; only `√3/2 ≥ 17/20` is used numerically.) -/
theorem region_large {M₀ M₁ ξ₁ : ℝ} (hM₀ : 0 < M₀) (hM₁ : 0 < M₁) (hξ₁ : 0 < ξ₁) :
    ∃ ξ₀ : ℝ, ξ₁ ≤ ξ₀ ∧ 0 < ξ₀ ∧
      ∀ (u y : ℂ), u ∈ MandelDim.QLeft ξ₀ → ‖y - u‖ ≤ ‖u‖ / 4 + 4 →
        y.re < -M₀ ∨ (M₁ < |y.im| ∧ y.re < 3 * |y.im|) := by
  set ξ₀ : ℝ := max ξ₁ (1000 * (M₀ + M₁ + 1) + 1) with hξ₀def
  have hbig : 1000 * (M₀ + M₁ + 1) + 1 ≤ ξ₀ := by rw [hξ₀def]; exact le_max_right _ _
  have hξ₁ξ : ξ₁ ≤ ξ₀ := by rw [hξ₀def]; exact le_max_left _ _
  have hξ₀pos : 0 < ξ₀ := lt_of_lt_of_le hξ₁ hξ₁ξ
  refine ⟨ξ₀, hξ₁ξ, hξ₀pos, ?_⟩
  intro u y hu hyu
  -- the elementary description of the sector
  have hQ : 2 * ((u + (ξ₀ : ℂ)).re) < ‖u + (ξ₀ : ℂ)‖ := (Work.Parab.QLeft_iff ξ₀ u).mp hu
  set α : ℝ := (u + (ξ₀ : ℂ)).re with hαdef
  set s : ℝ := ‖u + (ξ₀ : ℂ)‖ with hsdef
  have h2α : 2 * α < s := hQ
  have hs0 : 0 ≤ s := by rw [hsdef]; exact norm_nonneg _
  have hure : u.re = α - ξ₀ := by
    have h1 : (u + (ξ₀ : ℂ)).re = u.re + ξ₀ := by simp
    rw [← hαdef] at h1
    linarith
  have huim : |u.im| = |(u + (ξ₀ : ℂ)).im| := by simp
  have hunorm : ‖u‖ ≤ s + ξ₀ := by
    have h := norm_sub_le (u + (ξ₀ : ℂ)) (ξ₀ : ℂ)
    simp only [add_sub_cancel_right] at h
    rw [← hsdef, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hξ₀pos] at h
    exact h
  have hδc : ‖y - u‖ ≤ (s + ξ₀) / 4 + 4 := by linarith
  have hyre : y.re ≤ α - ξ₀ + ‖y - u‖ := by
    have h1 : (y - u).re = y.re - u.re := by simp
    have h2 := Complex.re_le_norm (y - u)
    rw [h1] at h2
    rw [hure] at h2
    linarith
  have hyim : |u.im| - ‖y - u‖ ≤ |y.im| := by
    have h1 : (y - u).im = y.im - u.im := by simp
    have h2 : |u.im - y.im| ≤ ‖y - u‖ := by
      have hh := Complex.abs_im_le_norm (y - u)
      rw [h1, abs_sub_comm] at hh
      exact hh
    have h3 : |u.im| ≤ |y.im| + |u.im - y.im| := by
      have he : y.im + (u.im - y.im) = u.im := by ring
      have h := abs_add_le y.im (u.im - y.im)
      rwa [he] at h
    linarith
  by_cases hcase : α < -s / 2
  · -- the sector point is well past the `2π/3` direction: `y` is far to the left
    left
    nlinarith [hyre, hδc, hcase, hbig, hM₀, hs0]
  · have hcase' : -s / 2 ≤ α := not_lt.mp hcase
    -- `|u.im|` is comparable to `s`
    have him : (17 / 20 : ℝ) * s < |u.im| := by
      have hA : 2 * (u + (ξ₀ : ℂ)).re < ‖u + (ξ₀ : ℂ)‖ := by rw [← hαdef, ← hsdef]; exact h2α
      have hB : -‖u + (ξ₀ : ℂ)‖ / 2 ≤ (u + (ξ₀ : ℂ)).re := by rw [← hαdef, ← hsdef]; linarith
      have h := abs_im_lower (z := u + (ξ₀ : ℂ)) hA hB
      rw [← hsdef, ← huim] at h
      exact h
    by_cases hsmall : s ≤ ξ₀ / 2
    · -- the sector point is near the vertex: `y` is again far to the left
      left
      nlinarith [hyre, hδc, h2α, hsmall, hbig, hM₀, hs0]
    · -- the two-sided wedge
      have hsmall' : ξ₀ / 2 < s := not_le.mp hsmall
      right
      refine ⟨?_, ?_⟩
      · nlinarith [hyim, him, hδc, hsmall', hbig, hM₁]
      · nlinarith [hyre, hδc, h2α, him, hyim, hsmall', hbig, hM₀, hM₁]

end Work.Parab.coordData
