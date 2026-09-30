import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- Arithmetic core of the half-step estimate `est_f_ge_half_g_half_arith` (BW §19,
descent level `J`, half-integer points).  The exponential inequality is reduced — by taking
logarithms, i.e. multiplying `Real.exp u` by `2 = Real.exp (Real.log 2)` — to the linear
inequality `u + log 2 ≤ v`, which is closed by explicitly expanding the two composite
factors and combining the stated bounds with `2^r ≥ 4`.

After expansion the two `h·Tst` contributions cancel (`(2^r − 1/d)·d·h·Tst − h·Tst` against
the `+ h·Tst` of the left side), leaving the margin `(2·022 − 2·965·2^r) SD ≤ 0`. -/
theorem est_f_ge_half_g_half_arith {A d h S D Tst Hp kumJ ss : ℝ} {r J : ℕ}
    (hr : 2 ≤ r) (hd : 1 ≤ d) (hS : 0 < S) (hD : 0 ≤ D) (hss0 : 0 ≤ ss)
    (hTs : d * h * Tst ≤ 0.735 * S * D)
    (hHp : Hp ≤ 0.85 * S * D)
    (hss : ss / 2 / 2 ^ J ≤ 2 * S)
    (hkum : kumJ ≤ 2.2 * S * D)
    (hSD : Real.log 2 ≤ 0.001 * S * D) :
    Real.exp (A + h * Tst + (0.205 * (1 / d) + 1.01 * (ss / 2 / 2 ^ J) / S - 9 * 2 ^ r) * S * D) * 2
      ≤ Real.exp (A - 2 ^ r * (Hp + (1 - 1 / (2 ^ r * d)) * (d * h * Tst + 0.204 * S * D) +
          1.007 * (ss / 2 / 2 ^ J) * D + 0.032 * S * D + kumJ)) := by
  have hdpos : (0:ℝ) < d := by linarith
  have hdne : d ≠ 0 := ne_of_gt hdpos
  have hSne : S ≠ 0 := ne_of_gt hS
  have h2r4 : (4:ℝ) ≤ (2:ℝ)^r := by
    have h : (2:ℝ)^2 ≤ (2:ℝ)^r := pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hr
    norm_num at h; exact h
  have h2rne : (2:ℝ)^r ≠ 0 := by positivity
  have h1dle : 1/d ≤ 1 := by rw [div_le_iff₀ hdpos]; linarith
  have hSD0 : (0:ℝ) ≤ S * D := mul_nonneg (le_of_lt hS) hD
  have h1dSD : (1/d) * (S*D) ≤ S*D := by
    have h := mul_le_mul_of_nonneg_right h1dle hSD0
    simpa using h
  have hzD : (ss / 2 / 2^J) * D ≤ (2 * S) * D := mul_le_mul_of_nonneg_right hss hD
  -- Expand the coefficient product, cancelling the `S` against the division by `S`.
  have hterm : (0.205 * (1 / d) + 1.01 * (ss / 2 / 2 ^ J) / S - 9 * 2 ^ r) * S * D
      = 0.205 * (1/d) * (S*D) + 1.01 * (ss/2/2^J) * D - 9 * (2:ℝ)^r * (S*D) := by
    have hSdiv : 1.01 * ((ss / 2 / 2^J) / S) * S * D = 1.01 * (ss/2/2^J) * D := by
      field_simp
    calc (0.205 * (1 / d) + 1.01 * (ss / 2 / 2 ^ J) / S - 9 * 2 ^ r) * S * D
        = 0.205 * (1/d) * S * D + 1.01 * ((ss/2/2^J)/S) * S * D - 9 * (2:ℝ)^r * S * D := by ring
      _ = 0.205 * (1/d) * (S*D) + 1.01 * (ss/2/2^J) * D - 9 * (2:ℝ)^r * (S*D) := by rw [hSdiv]; ring
  -- Distribute the common factor `2^r` over the bracket; `2^r·(1 - 1/(2^r d)) = 2^r - 1/d`
  -- produces the `- h·Tst` piece that cancels the left-hand `+ h·Tst`.
  have hQexpand : (2:ℝ)^r * (Hp + (1 - 1 / ((2:ℝ)^r * d)) * (d * h * Tst + 0.204 * S * D) +
          1.007 * (ss / 2 / 2^J) * D + 0.032 * S * D + kumJ)
      = (2:ℝ)^r * Hp
        + ((2:ℝ)^r * d * h * Tst - h * Tst + 0.204 * (2:ℝ)^r * (S*D) - 0.204 * (1/d) * (S*D))
        + 1.007 * (2:ℝ)^r * (ss/2/2^J) * D
        + 0.032 * (2:ℝ)^r * (S*D)
        + (2:ℝ)^r * kumJ := by
    field_simp
    ring
  have hmain : A + h * Tst + (0.205 * (1 / d) + 1.01 * (ss / 2 / 2 ^ J) / S - 9 * 2 ^ r) * S * D
        + Real.log 2
      ≤ A - 2 ^ r * (Hp + (1 - 1 / (2 ^ r * d)) * (d * h * Tst + 0.204 * S * D) +
          1.007 * (ss / 2 / 2 ^ J) * D + 0.032 * S * D + kumJ) := by
    rw [hterm, hQexpand]
    nlinarith [hTs, hHp, hkum, hSD, h1dSD, hzD, h2r4, hSD0]
  calc Real.exp (A + h * Tst + (0.205 * (1 / d) + 1.01 * (ss / 2 / 2 ^ J) / S - 9 * 2 ^ r) * S * D) * 2
      = Real.exp (A + h * Tst + (0.205 * (1 / d) + 1.01 * (ss / 2 / 2 ^ J) / S - 9 * 2 ^ r) * S * D
          + Real.log 2) := by
        conv_rhs => rw [Real.exp_add, Real.exp_log (by norm_num : (0:ℝ) < 2)]
    _ ≤ Real.exp (A - 2 ^ r * (Hp + (1 - 1 / (2 ^ r * d)) * (d * h * Tst + 0.204 * S * D) +
          1.007 * (ss / 2 / 2 ^ J) * D + 0.032 * S * D + kumJ)) := Real.exp_le_exp.mpr hmain

end Work.BW
