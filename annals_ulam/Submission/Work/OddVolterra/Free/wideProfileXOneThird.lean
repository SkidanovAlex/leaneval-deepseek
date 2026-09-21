import Mathlib
import Submission.Work.OddVolterra.Free.envelopeLeft_gap_dev_orders_two

/-!
# `|profileX'| ≥ 1/3` on `[2/3, 1]`

The semicircle chord function `profileX s = 1/√(1 + s²)` has

  `|profileX' s| = s / (1 + s²)^{3/2}`  for `s > 0`

(`Work.OddCurve.LowSlope.deriv_profileX_eq`), and `g s = s / (1 + s²)^{3/2}` is *decreasing*
on `[1/√2, ∞)`, so on `[2/3, 1]` it is bounded below by `g 1 = 1/(2√2) > 1/3`.  Rather than
formalise the monotonicity, we use the equivalent squared inequality

  `(1 + s²)³ ≤ 9 s²`   (`s ∈ [2/3, 1]`)

which is polynomial, together with `profileX s ^ 2 * (1 + s²) = 1`; for `s ∈ [2/3, 1]`,

  `9 s² - (1 + s²)³ = (1 - s²) (s⁴ + 4 s² - 1) + s² ≥ 0`,

as both factors are non-negative there (`s⁴ ≥ 16/81` and `4 s² ≥ 16/9` give
`s⁴ + 4 s² - 1 ≥ 79/81 > 0`, while `s ≤ 1` gives `1 - s² ≥ 0`).

This is the wider-range companion of `Work.OddCurve.LowSlope.one_third_le_abs_deriv_profileX`,
which covers `[3/4, 9/10]`: the perturbation window of the odd Ulam construction meets the
slope range `[2/3, 1]`, whose far end `s = 1` is *not* covered by the narrow statement.
-/

namespace Work.OddVolterra.Free

theorem wideProfileXOneThird :
    ∀ s : ℝ, 2 / 3 ≤ s → s ≤ 1 → 1 / 3 ≤ |deriv Work.OddEnvelope.profileX s| := by
  intro s hs1 hs2
  have hs0 : 0 < s := by linarith
  -- the polynomial inequality `(1 + s²)³ ≤ 9 s²` on `[2/3, 1]`
  have hkey : 9 * s ^ 2 ≥ (1 + s ^ 2) ^ 3 := by
    have hs2ge : (4 / 9 : ℝ) ≤ s ^ 2 := by nlinarith [sq_nonneg (s - 2 / 3)]
    have hs4ge : (16 / 81 : ℝ) ≤ s ^ 4 := by
      nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 4 / 9) hs2ge 2]
    have hB : 0 ≤ s ^ 4 + 4 * s ^ 2 - 1 := by nlinarith [hs4ge, hs2ge]
    have hA : 0 ≤ 1 - s ^ 2 := by
      nlinarith [mul_nonneg (le_of_lt hs0) (by linarith : (0 : ℝ) ≤ 1 - s), hs2]
    have hfac : 0 ≤ (1 - s ^ 2) * (s ^ 4 + 4 * s ^ 2 - 1) := mul_nonneg hA hB
    nlinarith [hfac, sq_nonneg s]
  have hstep : |-(s / (1 + s ^ 2)) * Work.OddEnvelope.profileX s|
      = (s / (1 + s ^ 2)) * Work.OddEnvelope.profileX s := by
    rw [abs_mul, abs_neg, abs_of_pos (div_pos hs0 (by positivity)),
      abs_of_pos (Work.OddEnvelope.profileX_pos s)]
  rw [Work.OddCurve.LowSlope.deriv_profileX_eq s, hstep]
  have ha2 : ((s / (1 + s ^ 2)) * Work.OddEnvelope.profileX s) ^ 2
      = s ^ 2 / (1 + s ^ 2) ^ 3 := by
    rw [mul_pow, div_pow, Work.OddEnvelope.profileX_sq]
    field_simp
  have hb : (1 / 3 : ℝ) ^ 2 ≤ ((s / (1 + s ^ 2)) * Work.OddEnvelope.profileX s) ^ 2 := by
    rw [ha2, le_div_iff₀ (by positivity : (0 : ℝ) < (1 + s ^ 2) ^ 3)]
    nlinarith [hkey]
  have hnn : 0 ≤ (s / (1 + s ^ 2)) * Work.OddEnvelope.profileX s :=
    mul_nonneg (le_of_lt (div_pos hs0 (by positivity)))
      (le_of_lt (Work.OddEnvelope.profileX_pos s))
  have hsq := sq_le_sq.mp hb
  rwa [abs_of_nonneg hnn, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 3)] at hsq

end Work.OddVolterra.Free
