import Mathlib
import Submission.Work.Drive.N2Lead.arcZ_re_strictMono

/-!
# Rigid bounds for the model arc `arcZ η w` in the far band

The model arc of the saddle window is `arcZ η w = I * sqrt (η - I w)` (`saddleArcs.lean`).  This file
proves that in the far band `|w| ≥ 39/20`, for every scaling parameter `η` in the window
`0 < η ≤ 3/800`, both coordinates of `arcZ η w` are bounded below by `3/4` in absolute value:

* `Im (arcZ η w) ≥ 3/4`,
* `|Re (arcZ η w)| ≥ 3/4`.

This is the numerical input consumed by `MfrPinRowsX.lean`: the twist parameter `ε` may be taken
below `(arcZ ηs (39/20)).re ≥ 3/4` and the twist is *strictly settled* on `|u| ≥ 39/20`
(strict monotonicity of `Re ∘ arcZ`).

## The mathematics

Write `z = arcZ η w`, `a = Re z`, `b = Im z` and `s = sqrt (η ^ 2 + w ^ 2)`.  From
`z ^ 2 = -η + I w` we read off

* `a ^ 2 - b ^ 2 = -η`   (real part),
* `a ^ 2 + b ^ 2 = s`    (modulus, `normSq_arcZ`),

so `a ^ 2 = (s - η) / 2` and `b ^ 2 = (s + η) / 2`.  Since `s ≥ |w|` (because
`|w| ^ 2 = w ^ 2 ≤ η ^ 2 + w ^ 2`) and `|w| ≥ 39/20`, `η ≤ 3/800`, `η > 0`, we get

* `b ^ 2 ≥ |w| / 2 ≥ 39/40 ≥ 9/16`, and `b > 0`, hence `b ≥ 3/4`;
* `a ^ 2 ≥ (39/20 - 3/800) / 2 = 1557/1600 ≥ 9/16`, hence `|a| ≥ 3/4`.

Note that only the *lower* bound `s ≥ |w|` is needed: the bounds are very comfortable.
-/

namespace Work.Drive.N2Lead

/-- In the far band `|w| ≥ 39/20` the model arc `arcZ η w` has both coordinates at least `3/4` in
absolute value, for every window parameter `0 < η ≤ 3/800`. -/
theorem arcZ_rigid_bounds {ηs : ℝ} (hηs : 0 < ηs) (hηs' : ηs ≤ 3 / 800) {w : ℝ}
    (hw : 39 / 20 ≤ |w|) :
    (3 / 4 : ℝ) ≤ (Work.Drive.N2Lead.arcZ ηs w).im ∧
      (3 / 4 : ℝ) ≤ |(Work.Drive.N2Lead.arcZ ηs w).re| := by
  set z : ℂ := Work.Drive.N2Lead.arcZ ηs w with hz
  -- `z ^ 2 = -η + I w` and `normSq z = sqrt (η ^ 2 + w ^ 2)`, transferred to `z`.
  have hsq : z ^ 2 = -(ηs : ℂ) + (w : ℂ) * Complex.I := by
    rw [hz]; exact Work.Drive.N2Lead.arcZ_sq ηs w
  have hnorm : Complex.normSq z = Real.sqrt (ηs ^ 2 + w ^ 2) := by
    rw [hz]; exact Work.Drive.N2Lead.normSq_arcZ ηs w
  have him : 0 < z.im := by
    rw [hz]; exact Work.Drive.N2Lead.ReStrictMono.im_arcZ_pos hηs w
  -- The two algebraic identities `a ^ 2 - b ^ 2 = -η`, `a ^ 2 + b ^ 2 = s`.
  have hA : z.re ^ 2 - z.im ^ 2 = -ηs := by
    have h := congrArg Complex.re hsq
    rw [pow_two, Complex.mul_re] at h
    simpa [pow_two] using h
  have hB : z.re ^ 2 + z.im ^ 2 = Real.sqrt (ηs ^ 2 + w ^ 2) := by
    rw [Complex.normSq_apply] at hnorm
    rw [← pow_two, ← pow_two] at hnorm
    exact hnorm
  -- `|w| ≤ sqrt (η ^ 2 + w ^ 2)`.
  have hsqrt : |w| ≤ Real.sqrt (ηs ^ 2 + w ^ 2) := by
    rw [Real.le_sqrt (abs_nonneg w) (by positivity)]
    nlinarith [sq_abs w]
  have ha2 : z.re ^ 2 = (Real.sqrt (ηs ^ 2 + w ^ 2) - ηs) / 2 := by linarith
  have hb2 : z.im ^ 2 = (Real.sqrt (ηs ^ 2 + w ^ 2) + ηs) / 2 := by linarith
  have h39 : (39 : ℝ) / 20 ≤ Real.sqrt (ηs ^ 2 + w ^ 2) := le_trans hw hsqrt
  have ha2' : (9 : ℝ) / 16 ≤ z.re ^ 2 := by rw [ha2]; linarith
  have hb2' : (9 : ℝ) / 16 ≤ z.im ^ 2 := by rw [hb2]; linarith
  constructor
  · -- `3/4 ≤ b`, from `b > 0` and `b ^ 2 ≥ 9/16`.
    have h3 : 0 < z.im + 3 / 4 := by linarith
    have h2 : 0 ≤ (z.im + 3 / 4) * (z.im - 3 / 4) := by nlinarith
    have h4 : 0 ≤ z.im - 3 / 4 := nonneg_of_mul_nonneg_right h2 h3
    linarith
  · -- `3/4 ≤ |a|`, from `|a| ≥ 0` and `|a| ^ 2 = a ^ 2 ≥ 9/16`.
    have habs : (|z.re| : ℝ) ^ 2 = z.re ^ 2 := sq_abs z.re
    have h3 : 0 < |z.re| + 3 / 4 := by linarith [abs_nonneg z.re]
    have h2 : 0 ≤ (|z.re| + 3 / 4) * (|z.re| - 3 / 4) := by nlinarith
    have h4 : 0 ≤ |z.re| - 3 / 4 := nonneg_of_mul_nonneg_right h2 h3
    linarith

end Work.Drive.N2Lead
