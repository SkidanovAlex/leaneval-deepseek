import Mathlib

namespace Work.L62

/-- Auxiliary exponential estimate: for `t ≥ 0`, `exp (-t) ≤ 1 / (1 + t)`.
This is the reciprocal form of `Real.add_one_le_exp`. -/
theorem exp_neg_le_one_div_one_add {t : ℝ} (ht : 0 ≤ t) :
    Real.exp (-t) ≤ 1 / (1 + t) := by
  have hthis := one_div_le_one_div_of_le (by linarith [Real.add_one_le_exp t])
    (Real.add_one_le_exp t)
  simpa [Real.exp_neg, one_div, add_comm] using hthis

/-- Numerical shift estimate (Lemma 6.2 in Shishikura's notation): if `κ > 0`,
`δ ≥ 0`, `δ ≤ κ / 1000` and `δ ≤ 1 / 1000`, then the "shift" quantity
`8 δ / (1 - exp (-π κ / 2))` is at most `1 / 2`.

The exponential barrier is small only when `κ` is small; accordingly we use
`δ ≤ κ / 1000` when `π κ / 2 ≤ 1`, and `δ ≤ 1 / 1000` otherwise. -/
theorem num_shift {δ κ : ℝ} (hκ : 0 < κ) (hδ0 : 0 ≤ δ) (hδκ : δ ≤ κ / 1000)
    (hδ1 : δ ≤ 1 / 1000) :
    8 * δ / (1 - Real.exp (-2 * Real.pi * (κ / 4))) ≤ 1 / 2 := by
  have _hδ0 := hδ0
  clear _hδ0
  have hexp : -2 * Real.pi * (κ / 4) = -(Real.pi * κ / 2) := by ring
  rw [hexp]
  set t := Real.pi * κ / 2 with ht_def
  have htpos : 0 < t := by rw [ht_def]; positivity
  -- the denominator is positive, so clearing it is legitimate
  have hden : 0 < 1 - Real.exp (-t) := by
    have : Real.exp (-t) < 1 := by rw [Real.exp_lt_one_iff]; linarith
    linarith
  rw [div_le_iff₀ hden]
  -- it suffices to bound `16 δ` by `1 - exp (-t)`
  have hkey : 16 * δ ≤ 1 - Real.exp (-t) := by
    have hbound : Real.exp (-t) ≤ 1 / (1 + t) := exp_neg_le_one_div_one_add htpos.le
    rcases le_or_gt t 1 with ht1 | ht1
    · -- small `t`: `1 - exp (-t) ≥ t/2`, and `16 δ ≤ t/2`
      have h2 : 1 / (1 + t) ≤ 1 - t / 2 := by
        rw [div_le_iff₀ (by linarith)]
        nlinarith
      have h3 : 16 * δ ≤ t / 2 := by
        rw [ht_def]
        nlinarith [Real.pi_gt_three, hκ]
      linarith
    · -- large `t`: `1 - exp (-t) ≥ 1/2 ≥ 16 δ`
      have h2 : 1 / (1 + t) ≤ 1 / 2 := by
        rw [div_le_iff₀ (by linarith)]
        linarith
      have h3 : 16 * δ ≤ 1 / 2 := by nlinarith [hδ0, hδ1]
      linarith
  linarith

end Work.L62
