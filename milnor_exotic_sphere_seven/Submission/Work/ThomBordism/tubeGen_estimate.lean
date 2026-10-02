import Mathlib
import Submission.Work.ThomBordism.TubeGenAux

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The threshold estimate for the interpolating collapse `θ_s`

`Work.ThomBordism.TubeGen.theta R s` is the coordinatewise interpolation

  `θ_s(y)_j = (1-s) · (R · y_j / √(1 + y_j²)) + s · y_j`

between the "squashing" `y_j ↦ R y_j/√(1+y_j²)` (at `s = 0`) and the identity (at `s = 1`).

This file proves the elementary estimate which says that the interpolation *stays outside the ball
of radius* `R - δ` *as long as one coordinate enters the box of radius* `thresh R δ`:

`∃ j, thresh R δ ≤ |y_j|  ⟹  ∃ j, R - δ ≤ |θ_s(y)_j|`

for `0 ≤ R`, `δ > 0` and `s ∈ [0,1]`.

The two ingredients are the two numerical facts built into the definition of the threshold
`thresh R δ = max 1 (max (4R²/δ) (max (4R/δ) √(2R/δ)))`:

* `thresh_ge_sub` — the threshold itself dominates `R - δ`;
* `squashed_sub_le` — above the threshold the squashing is `δ`-close to `R`
  (`R - R t/√(1+t²) ≤ δ`), which follows from `1 - t/√(1+t²) = 1/((√(1+t²)+t)·√(1+t²)) ≤ 1/t²`
  together with `t² ≥ 2R/δ`.
-/

namespace Work.ThomBordism

open TubeGen

/-- The threshold `thresh R δ` dominates `R - δ` (for `R ≥ 0`, `δ > 0`). -/
theorem thresh_ge_sub {R δ : ℝ} (hR : 0 ≤ R) (hδ : 0 < δ) : R - δ ≤ thresh R δ := by
  rcases le_or_gt R δ with h | h
  · have : R - δ ≤ 1 := by linarith
    exact le_trans this (one_le_thresh R δ)
  · have h4 : 4 * R ^ 2 / δ ≤ thresh R δ := four_R_sq_div_le_thresh R δ
    have hle : R - δ ≤ 4 * R ^ 2 / δ := by
      rw [le_div_iff₀ hδ]
      nlinarith
    linarith

/-- Above the threshold, the squashing is `δ`-close to `R`:
`R · (1 - t/√(1+t²)) ≤ δ` whenever `thresh R δ ≤ t` (for `R ≥ 0`, `δ > 0`). -/
theorem squashed_sub_le {R δ : ℝ} (hR : 0 ≤ R) (hδ : 0 < δ) {t : ℝ}
    (ht : thresh R δ ≤ t) : R * (1 - t / Real.sqrt (1 + t ^ 2)) ≤ δ := by
  have ht1 : 1 ≤ t := le_trans (one_le_thresh R δ) ht
  have ht0 : 0 ≤ t := le_trans zero_le_one ht1
  set s := Real.sqrt (1 + t ^ 2) with hs
  have hs1 : 1 ≤ s := by
    rw [hs]
    exact (Real.le_sqrt (by norm_num) (by positivity)).mpr (by nlinarith)
  have hs0 : 0 ≤ s := le_trans zero_le_one hs1
  have hst : t ≤ s := by
    rw [hs]
    exact (Real.le_sqrt ht0 (by positivity)).mpr (by nlinarith)
  have hspos : 0 < s := lt_of_lt_of_le zero_lt_one hs1
  -- `1 - t/√(1+t²) = 1/((√(1+t²)+t)·√(1+t²))`
  have hkey : 1 - t / s = 1 / ((s + t) * s) := by
    field_simp
    nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 1 + t ^ 2 by positivity), hs]
  have hsqr : t ^ 2 ≤ (s + t) * s := by nlinarith
  have hinv : 1 / ((s + t) * s) ≤ 1 / t ^ 2 :=
    one_div_le_one_div_of_le (by positivity) hsqr
  have hstep : R * (1 - t / s) ≤ R * (1 / t ^ 2) := by
    rw [hkey]
    exact mul_le_mul_of_nonneg_left hinv hR
  have hfinal : R * (1 / t ^ 2) ≤ δ := by
    rw [mul_one_div, div_le_iff₀ (by positivity : (0:ℝ) < t ^ 2)]
    have h2 : 2 * R / δ ≤ t ^ 2 := by
      have h := pow_le_pow_left₀ (Real.sqrt_nonneg (2 * R / δ))
        (le_trans (sqrt_two_R_div_le_thresh R δ) ht) 2
      rwa [Real.sq_sqrt (by positivity)] at h
    have h3 : δ * (2 * R / δ) = 2 * R := by field_simp
    nlinarith
  linarith

/-- **The threshold estimate.**  If one coordinate of `y` has absolute value at least
`thresh R δ`, then at every time `s ∈ [0,1]` some coordinate of the interpolated point `θ_s(y)` has
absolute value at least `R - δ`. -/
theorem tubeGen_estimate {n : ℕ} {R δ s : ℝ} (hR : 0 ≤ R) (hδ : 0 < δ)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) {y : Work.Tubular.Euc n}
    (hy : ∃ j : Fin n, Work.ThomBordism.TubeGen.thresh R δ ≤ |y j|) :
    ∃ j : Fin n, R - δ ≤ |Work.ThomBordism.TubeGen.theta R s y j| := by
  obtain ⟨j, hj⟩ := hy
  refine ⟨j, ?_⟩
  set t := |y j| with ht
  have ht0 : 0 ≤ t := abs_nonneg _
  have ht1 : 1 ≤ t := le_trans (one_le_thresh R δ) hj
  have hj' : thresh R δ ≤ t := by rw [ht]; exact hj
  have hsq : (y j) ^ 2 = t ^ 2 := by rw [ht, sq_abs]
  -- factor out the sign of `y j`
  have hfac : theta R s y j = y j * ((1 - s) * (R / Real.sqrt (1 + t ^ 2)) + s) := by
    rw [theta_apply, hsq]
    ring
  have hbr : 0 ≤ (1 - s) * (R / Real.sqrt (1 + t ^ 2)) + s := by
    have h1 : 0 ≤ R / Real.sqrt (1 + t ^ 2) := div_nonneg hR (Real.sqrt_nonneg _)
    nlinarith
  have habs : |theta R s y j| = t * ((1 - s) * (R / Real.sqrt (1 + t ^ 2)) + s) := by
    rw [hfac, abs_mul, abs_of_nonneg hbr, ← ht]
  rw [habs]
  -- the squashed coordinate is within `δ` of `R` …
  have hA : R - δ ≤ R * t / Real.sqrt (1 + t ^ 2) := by
    have h := squashed_sub_le hR hδ hj'
    have heq : R * (1 - t / Real.sqrt (1 + t ^ 2))
        = R - R * t / Real.sqrt (1 + t ^ 2) := by ring
    rw [heq] at h
    linarith
  -- … and the unsquashed coordinate already exceeds `R - δ`
  have htB : R - δ ≤ t := le_trans (thresh_ge_sub hR hδ) hj'
  -- so every convex combination does as well
  have hfin : R - δ ≤ (1 - s) * (R * t / Real.sqrt (1 + t ^ 2)) + s * t := by
    have h1 : (1 - s) * (R - δ) ≤ (1 - s) * (R * t / Real.sqrt (1 + t ^ 2)) :=
      mul_le_mul_of_nonneg_left hA (by linarith)
    have h2 : s * (R - δ) ≤ s * t := mul_le_mul_of_nonneg_left htB hs0
    nlinarith
  have heq2 : t * ((1 - s) * (R / Real.sqrt (1 + t ^ 2)) + s)
      = (1 - s) * (R * t / Real.sqrt (1 + t ^ 2)) + s * t := by ring
  rw [heq2]
  exact hfin

end Work.ThomBordism
