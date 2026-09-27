import Mathlib
import Submission.Work.Drive.UmlaufSetup

set_option linter.unusedVariables false

namespace Work.Drive

/-- The imaginary part of the direction of a complex number `z`.  The formula is also correct at
`z = 0`, where `dirOf` takes the junk value `1`: both sides are `0` there. -/
lemma dirOf_im (z : ℂ) : (((dirOf z : Circle) : ℂ)).im = z.im / ‖z‖ := by
  by_cases hz : z = 0
  · rw [hz, dirOf_zero]; simp
  · rw [dirOf_coe hz, Complex.div_ofReal_im]

/-- `dirOf` sends a complex number in the closed upper half plane to a direction in the closed
upper half plane. -/
lemma dirOf_im_nonneg {z : ℂ} (h : 0 ≤ z.im) : 0 ≤ (((dirOf z : Circle) : ℂ)).im := by
  rw [dirOf_im]; exact div_nonneg h (norm_nonneg z)

/-- `dirOf` sends a real complex number to a direction on the real axis. -/
lemma dirOf_im_eq_zero {z : ℂ} (h : z.im = 0) : (((dirOf z : Circle) : ℂ)).im = 0 := by
  rw [dirOf_im, h, zero_div]

/-- If the tangent at `t` is horizontal, the direction of the tangent lies on the real axis. -/
lemma tangDir_im_eq_zero (c : ℝ → ℝ × ℝ) {t : ℝ} (hderiv : (deriv c t).2 = 0) :
    ((tangDir c t : Circle) : ℂ).im = 0 := by
  rw [tangDir]
  exact dirOf_im_eq_zero (by simp [hderiv])

/-- If `c t` is not below `c s`, the direction of the secant from `c s` to `c t` lies in the closed
upper half plane. -/
lemma secDir_im_nonneg (c : ℝ → ℝ × ℝ) {s t : ℝ} (h : (c s).2 ≤ (c t).2) :
    0 ≤ ((secDir c s t : Circle) : ℂ).im := by
  rw [secDir]
  apply dirOf_im_nonneg
  simp only [toC_im]
  have := h
  simp only [Prod.snd_sub]
  linarith

/-- The vertical side of Hopf's triangle stays in the closed upper half plane, when `c t₀` is the
lowest point of the curve and the tangent at `t₀` is horizontal.

Cases on `t ∈ Icc t₀ (t₀+2π)`.  If `t = t₀ + 2π` the corner branch of `sigmaPt` returns
`-(tangDir c t₀)`, whose imaginary part is `-(deriv c t₀).2 / ‖·‖ = 0` by `hderiv`.  If
`t₀ < t < t₀+2π` the value is `secDir c t₀ t`, the direction of `toC (c t - c t₀)` whose imaginary
part is `(c t).2 - (c t₀).2 ≥ 0` by `hmin`, and dividing by the nonnegative real `‖toC (c t - c t₀)‖`
preserves the sign (`dirOf_coe`, `Complex.div_im`).  If `t = t₀` the value is `tangDir c t₀`, with
imaginary part `0` as above. -/
theorem sigmaPt_im_nonneg (c : ℝ → ℝ × ℝ) (hc : Work.Drive.RegCurve c) {t₀ : ℝ}
    (hmin : ∀ t, (c t₀).2 ≤ (c t).2) (hderiv : (deriv c t₀).2 = 0) {t : ℝ}
    (ht : t ∈ Set.Icc t₀ (t₀ + 2 * Real.pi)) :
    0 ≤ ((Work.Drive.sigmaPt c t₀ (t₀, t) : Circle) : ℂ).im := by
  have htang : ((tangDir c t₀ : Circle) : ℂ).im = 0 := tangDir_im_eq_zero c hderiv
  have hsec : 0 ≤ ((secDir c t₀ t : Circle) : ℂ).im := secDir_im_nonneg c (hmin t)
  unfold Work.Drive.sigmaPt
  split_ifs
  · rw [show ((↑(-(tangDir c t₀)) : ℂ)).im = -((↑(tangDir c t₀) : ℂ)).im by simp]
    rw [htang]; norm_num
  · exact hsec
  · rw [htang]

end Work.Drive
