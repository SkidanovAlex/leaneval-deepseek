import Mathlib

namespace Work.WilC4

/--
Ratio bound for real powers.

If `y / u ^ q` and `y' / (u / 2) ^ q` are both within a factor `3/2` of the
non-zero value `a`, then `y` can be recovered from `y'` up to the factor
`2 ^ (-q) / 4`.  Concretely, `2 ^ (-q) / 4 * |y| ≤ |y'|`.

The mathematical content is that `|y / u ^ q| < 3 |a| / 2` and
`|y' / (u / 2) ^ q| > |a| / 2`, whence
`(1/4) * |y / u ^ q| < 3 |a| / 8 < |a| / 2 < |y' / (u / 2) ^ q|`,
and multiplication by the positive quantity `(u / 2) ^ q = 2 ^ (-q) * u ^ q`
gives the claim. -/
theorem rpow_ratio_bound {q : ℚ} {a y y' u : ℝ} (ha : a ≠ 0) (hu : 0 < u)
    (h1 : |y / u ^ (q : ℝ) - a| < |a| / 2)
    (h2 : |y' / (u / 2) ^ (q : ℝ) - a| < |a| / 2) :
    (2 : ℝ) ^ (-(q : ℝ)) / 4 * |y| ≤ |y'| := by
  have hu2 : (0 : ℝ) < u / 2 := by linarith
  have hru : (0 : ℝ) < u ^ (q : ℝ) := Real.rpow_pos_of_pos hu _
  have hrd : (0 : ℝ) < (u / 2) ^ (q : ℝ) := Real.rpow_pos_of_pos hu2 _
  have hrun : u ^ (q : ℝ) ≠ 0 := ne_of_gt hru
  have hrdn : (u / 2) ^ (q : ℝ) ≠ 0 := ne_of_gt hrd
  have hm : (0 : ℝ) < |a| := abs_pos.mpr ha
  -- The key relation between the two real powers.
  have hkey : (2 : ℝ) ^ (-(q : ℝ)) * u ^ (q : ℝ) = (u / 2) ^ (q : ℝ) := by
    rw [Real.div_rpow (le_of_lt hu) (by norm_num : (0 : ℝ) ≤ 2) (q : ℝ),
        Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2) (q : ℝ), div_eq_mul_inv]
    ring
  -- Upper bound for `|y / u ^ q|`.
  have hAup : |y / u ^ (q : ℝ)| < 3 * |a| / 2 := by
    have htri : |y / u ^ (q : ℝ)| - |a| ≤ |y / u ^ (q : ℝ) - a| :=
      abs_sub_abs_le_abs_sub _ _
    linarith [h1, htri]
  -- Lower bound for `|y' / (u / 2) ^ q|`.
  have h2' : |a - y' / (u / 2) ^ (q : ℝ)| < |a| / 2 := by
    rw [abs_sub_comm]; exact h2
  have hBlow : |a| / 2 < |y' / (u / 2) ^ (q : ℝ)| := by
    have htri : |a| - |y' / (u / 2) ^ (q : ℝ)| ≤ |a - y' / (u / 2) ^ (q : ℝ)| :=
      abs_sub_abs_le_abs_sub _ _
    linarith [h2', htri]
  -- Hence the quarter bound on the normalised quantities.
  have hquarter : (1 / 4) * |y / u ^ (q : ℝ)| ≤ |y' / (u / 2) ^ (q : ℝ)| := by
    have h1' : (1 / 4) * |y / u ^ (q : ℝ)| < 3 * |a| / 8 := by linarith [hAup]
    have h2'' : 3 * |a| / 8 < |y' / (u / 2) ^ (q : ℝ)| := by linarith [hBlow, hm]
    linarith
  -- Undo the normalisation on both sides.
  have hyabs : |y| = |y / u ^ (q : ℝ)| * u ^ (q : ℝ) := by
    conv_lhs => rw [show y = (y / u ^ (q : ℝ)) * u ^ (q : ℝ) from by
      rw [div_mul_cancel₀ _ hrun]]
    rw [abs_mul, abs_of_pos hru]
  have hy'abs : |y'| = |y' / (u / 2) ^ (q : ℝ)| * (u / 2) ^ (q : ℝ) := by
    conv_lhs => rw [show y' = (y' / (u / 2) ^ (q : ℝ)) * (u / 2) ^ (q : ℝ) from by
      rw [div_mul_cancel₀ _ hrdn]]
    rw [abs_mul, abs_of_pos hrd]
  calc (2 : ℝ) ^ (-(q : ℝ)) / 4 * |y|
      = (2 : ℝ) ^ (-(q : ℝ)) * |y| / 4 := by ring
    _ = (2 : ℝ) ^ (-(q : ℝ)) * (|y / u ^ (q : ℝ)| * u ^ (q : ℝ)) / 4 := by rw [hyabs]
    _ = |y / u ^ (q : ℝ)| * ((2 : ℝ) ^ (-(q : ℝ)) * u ^ (q : ℝ)) / 4 := by ring
    _ = |y / u ^ (q : ℝ)| * (u / 2) ^ (q : ℝ) / 4 := by rw [hkey]
    _ = (1 / 4) * |y / u ^ (q : ℝ)| * (u / 2) ^ (q : ℝ) := by ring
    _ ≤ |y' / (u / 2) ^ (q : ℝ)| * (u / 2) ^ (q : ℝ) :=
        mul_le_mul_of_nonneg_right hquarter (le_of_lt hrd)
    _ = |y'| := by rw [hy'abs]

end Work.WilC4
