import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

theorem est16_main_arith {d h S D Tst Hp kumJ ss nz : ℝ} {J : ℕ}
    (hd : 1 ≤ d) (hS : 0 < S) (hD : 0 ≤ D) (hss0 : 0 ≤ ss)
    (hHp : Hp ≤ 0.85 * S * D)
    (hSD : Real.log 2 ≤ 0.001 * S * D) :
    h * Tst + 0.204 * (1 / d) * S * D + 1.008 * (nz / 2 ^ J) * D
        + (Hp + (1 - 1 / d) * (d * h * Tst + 0.204 * S * D) + 1.007 * (ss / 2 ^ J) * D + kumJ)
        + Real.log 2
      ≤ d * h * Tst + 1.055 * S * D + 1.008 * ((nz + ss) / 2 ^ J) * D + kumJ := by
  have hdpos : (0 : ℝ) < d := lt_of_lt_of_le zero_lt_one hd
  have hdne : d ≠ 0 := ne_of_gt hdpos
  -- The `h·Tst` and `0.204·S·D` terms combine exactly into `d·h·Tst + 0.204·S·D`.
  have hkey1 : h * Tst + 0.204 * (1 / d) * S * D + (1 - 1 / d) * (d * h * Tst + 0.204 * S * D)
      = d * h * Tst + 0.204 * S * D := by
    field_simp
    ring
  -- The `nz` and `ss` contributions: the `ss` coefficient drops from 1.008 to 1.007.
  have hpos : (0 : ℝ) < (2 : ℝ) ^ J := by positivity
  have hkey2 : 1.008 * (nz / 2 ^ J) * D + 1.007 * (ss / 2 ^ J) * D
      ≤ 1.008 * ((nz + ss) / 2 ^ J) * D := by
    rw [add_div]
    have hnn : 0 ≤ 0.001 * (ss / 2 ^ J) * D := by
      have : 0 ≤ ss / 2 ^ J := div_nonneg hss0 (le_of_lt hpos)
      nlinarith [hD]
    linarith
  -- `Hp + log 2 ≤ 0.85·S·D + 0.001·S·D`, so `0.204 + Hp + log 2 ≤ 1.055·S·D`.
  have h3 : Hp + Real.log 2 ≤ 0.85 * S * D + 0.001 * S * D := add_le_add hHp hSD
  linarith [hkey1, hkey2, h3]

end Work.BW
