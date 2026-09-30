import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- Arithmetic core of the half-step estimate `est16_half_arith` (BW §19, half-integer
points).  The exponential inequality is reduced — by taking logarithms, i.e. multiplying
`Real.exp u` by `2 = Real.exp (Real.log 2)` — to the linear inequality
`u + log 2 ≤ v`, which is then closed by explicitly expanding the two composite factors
and combining the six stated bounds with the elementary `2^r ≥ 4`.  The margin is
`(4.195 - 6.983 · 2^r) SD ≤ -23.7 SD ≤ 0`. -/
theorem est16_half_arith {d h S D Tst Hp kumJ ss A : ℝ} {r J : ℕ}
    (hr : 2 ≤ r) (hd : 1 ≤ d) (hS : 0 < S) (hD : 0 ≤ D) (hss0 : 0 ≤ ss)
    (hTs : d * h * Tst ≤ 0.735 * S * D)
    (hHp : Hp ≤ 0.85 * S * D)
    (hss : ss / 2 ^ J ≤ 2 ^ r * S)
    (hkum : kumJ ≤ 2.2 * S * D)
    (hSD : Real.log 2 ≤ 0.001 * S * D) :
    Real.exp (A + h * Tst + (0.205 * (1 / d) + 1.01 * (ss / 2 ^ J) / S - 9 * 2 ^ r) * S * D) * 2
      ≤ Real.exp (A - (Hp + (1 - 1 / d) * (d * h * Tst + 0.204 * S * D) + 1.007 * (ss / 2 ^ J) * D + kumJ)) := by
  have hdpos : (0:ℝ) < d := by linarith
  have hdne : d ≠ 0 := ne_of_gt hdpos
  have hSne : S ≠ 0 := ne_of_gt hS
  have h2r4 : (4:ℝ) ≤ (2:ℝ)^r := by
    have h : (2:ℝ)^2 ≤ (2:ℝ)^r := pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hr
    norm_num at h; exact h
  have h1dle : 1/d ≤ 1 := by rw [div_le_iff₀ hdpos]; linarith
  have hSD0 : (0:ℝ) ≤ S * D := mul_nonneg (le_of_lt hS) hD
  have h1dSD : (1/d) * (S*D) ≤ S*D := by
    have h := mul_le_mul_of_nonneg_right h1dle hSD0
    simpa using h
  have hssD : (ss/2^J) * D ≤ (2^r * S) * D := mul_le_mul_of_nonneg_right hss hD
  -- Expand the coefficient product, cancelling the `S` against the division by `S`.
  have hterm : (0.205 * (1 / d) + 1.01 * (ss / 2 ^ J) / S - 9 * 2 ^ r) * S * D
      = 0.205 * (1/d) * (S*D) + 1.01 * (ss/2^J) * D - 9 * 2^r * (S*D) := by
    have hSdiv : 1.01 * ((ss / 2^J) / S) * S * D = 1.01 * (ss/2^J) * D := by
      field_simp
    calc (0.205 * (1 / d) + 1.01 * (ss / 2 ^ J) / S - 9 * 2 ^ r) * S * D
        = 0.205 * (1/d) * S * D + 1.01 * ((ss/2^J)/S) * S * D - 9 * 2^r * S * D := by ring
      _ = 0.205 * (1/d) * (S*D) + 1.01 * (ss/2^J) * D - 9 * 2^r * (S*D) := by rw [hSdiv]; ring
  -- Expand `(1 - 1/d) * (...)`, using `(1/d) * d = 1` so that `d * h * Tst` reappears.
  have hb : (1 - 1/d) * (d * h * Tst + 0.204 * S * D)
      = (d * h * Tst - h * Tst) + (0.204 * (S*D) - 0.204 * ((1/d) * (S*D))) := by
    have hdm : (1/d) * d = 1 := by rw [one_div, inv_mul_cancel₀ hdne]
    have h1 : (1 - 1/d) * d = d - 1 := by rw [sub_mul, one_mul, hdm]
    calc (1 - 1/d) * (d * h * Tst + 0.204 * S * D)
        = (1 - 1/d) * (d * h * Tst) + (1 - 1/d) * (0.204 * S * D) := by ring
      _ = ((1 - 1/d) * d) * (h * Tst) + (0.204 * (S*D) - (1/d) * (0.204 * S*D)) := by ring
      _ = (d - 1) * (h * Tst) + (0.204 * (S*D) - 0.204 * ((1/d) * (S*D))) := by rw [h1]; ring
      _ = (d * h * Tst - h * Tst) + (0.204 * (S*D) - 0.204 * ((1/d) * (S*D))) := by ring
  have hmain : A + h * Tst + (0.205 * (1 / d) + 1.01 * (ss / 2 ^ J) / S - 9 * 2 ^ r) * S * D
        + Real.log 2
      ≤ A - (Hp + (1 - 1 / d) * (d * h * Tst + 0.204 * S * D) + 1.007 * (ss / 2 ^ J) * D + kumJ) := by
    rw [hterm, hb]
    nlinarith [hTs, hHp, hkum, hSD, h1dSD, hssD, h2r4, hSD0]
  calc Real.exp (A + h * Tst + (0.205 * (1 / d) + 1.01 * (ss / 2 ^ J) / S - 9 * 2 ^ r) * S * D) * 2
      = Real.exp (A + h * Tst + (0.205 * (1 / d) + 1.01 * (ss / 2 ^ J) / S - 9 * 2 ^ r) * S * D
          + Real.log 2) := by
        conv_rhs => rw [Real.exp_add, Real.exp_log (by norm_num : (0:ℝ) < 2)]
    _ ≤ Real.exp (A - (Hp + (1 - 1 / d) * (d * h * Tst + 0.204 * S * D)
          + 1.007 * (ss / 2 ^ J) * D + kumJ)) := Real.exp_le_exp.mpr hmain

end Work.BW
