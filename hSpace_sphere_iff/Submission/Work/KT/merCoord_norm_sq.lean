import Mathlib
import Submission.Work.KT.CapCoord

namespace Work.KT

/-- **The meridian formula stays on the unit sphere.**  If `z = (a, s)` has `‖a‖ ^ 2 + s ^ 2 = 1`,
`s ≤ 1/2` and `0 ≤ η ≤ 1`, then the same holds for `merCoord m η z`.  (`merCoord m η z` is defined
in `Submission/Work/KT/CapCoord.lean` as `(√(η * (2 - η * (s + 1)) / (1 - s)) • a, -1 + η * (s + 1))`.)
The hypotheses `0 ≤ η` and `η ≤ 1` are needed for the square root and for `2 - η * (s + 1) ≥ 0`; the
hypothesis `s ≤ 1/2` gives `1 - s ≥ 1/2`, so the denominator is harmless. -/
lemma merCoord_norm_sq (m : ℕ) {z : Eu m × ℝ} {η : ℝ}
    (hz : ‖z.1‖ ^ 2 + z.2 ^ 2 = 1) (hs : z.2 ≤ 1 / 2) (hη0 : 0 ≤ η) (hη1 : η ≤ 1) :
    ‖(merCoord m η z).1‖ ^ 2 + (merCoord m η z).2 ^ 2 = 1 := by
  -- The height `s` lies in `[-1, 1/2]`, so `-1 ≤ s` and `0 < 1 - s`.
  have hs2 : ‖z.1‖ ^ 2 = 1 - z.2 ^ 2 := by linarith
  have hden : (0 : ℝ) < 1 - z.2 := by linarith
  have hsp1 : 0 ≤ z.2 + 1 := by nlinarith [sq_nonneg ‖z.1‖]
  -- The square-root argument is nonnegative.
  have hle : η * (z.2 + 1) ≤ 1 * (z.2 + 1) := mul_le_mul_of_nonneg_right hη1 hsp1
  have harg : 0 ≤ η * (2 - η * (z.2 + 1)) / (1 - z.2) :=
    div_nonneg (mul_nonneg hη0 (by linarith)) (le_of_lt hden)
  -- First coordinate: `‖c • a‖ ^ 2 = c ^ 2 * ‖a‖ ^ 2`.
  have hnorm : ‖(merCoord m η z).1‖ ^ 2
      = (Real.sqrt (η * (2 - η * (z.2 + 1)) / (1 - z.2))) ^ 2 * ‖z.1‖ ^ 2 := by
    simp only [merCoord]
    rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  have hh : (merCoord m η z).2 = -1 + η * (z.2 + 1) := rfl
  rw [hnorm, hh, Real.sq_sqrt harg, hs2]
  -- `‖a‖ ^ 2 = 1 - s ^ 2 = (1 - s)(1 + s)`, and everything cancels.
  have h1 : (1 : ℝ) - z.2 ≠ 0 := ne_of_gt hden
  field_simp
  ring

end Work.KT
