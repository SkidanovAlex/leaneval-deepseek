import Mathlib

/-!
# The quarter-chord ratio at the axis points `±1/2 + 2ℤ`

For `0 < a < 1` and every integer `k`, the point `x = 1/2 + 2k` of the axis `1/2 + 2ℤ` satisfies
four quantitative inequalities relating its distances to the two focal points `∓ a/2`:

* `|x + a/2| ≤ ((1+a)/(1-a)) * |x - a/2|` and the mirrored inequality,
* `|x - a/2| ≥ (1-a)/2` and `|x + a/2| ≥ (1-a)/2`.

The proof rests on the single fact that every element of `1/2 + 2ℤ` has modulus at least `1/2`
(`abs_half_add_two_mul`): for `|x| ≥ 1/2` the last two estimates are the reverse triangle
inequality, while for the first two one splits into `x ≥ 1/2` (where both `x ± a/2` are
nonnegative and the claim reduces to `x ≥ 1/2`, resp. `x ≥ -1/2`) and `x ≤ -1/2` (where both are
negative and it reduces to `x ≤ 1/2`, resp. `x ≤ -1/2`).
-/

namespace Work.EQ

/-- Every integer point of the axis `1/2 + 2ℤ` has modulus at least `1/2`: for `k ≥ 0` the point
is `≥ 1/2`, and for `k ≤ -1` it is `≤ -3/2`. -/
lemma abs_half_add_two_mul (k : ℤ) : (1:ℝ)/2 ≤ |(1:ℝ)/2 + 2 * (k:ℝ)| := by
  rcases le_or_gt (0:ℤ) k with hk | hk
  · have hk' : (0:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
    rw [abs_of_nonneg (by linarith)]
    linarith
  · have hk1 : k ≤ -1 := by omega
    have hk' : (k:ℝ) ≤ -1 := by exact_mod_cast hk1
    rw [abs_of_nonpos (by linarith)]
    linarith

/-- The four quarter-chord inequalities for an arbitrary real `x` with `|x| ≥ 1/2` and
`0 < a < 1`. -/
lemma quarter_ratio_le_abs {a x : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hx : (1:ℝ)/2 ≤ |x|) :
    |x + a/2| ≤ ((1+a)/(1-a)) * |x - a/2| ∧
    |x - a/2| ≤ ((1+a)/(1-a)) * |x + a/2| ∧
    (1-a)/2 ≤ |x - a/2| ∧
    (1-a)/2 ≤ |x + a/2| := by
  have hpos : 0 < 1 - a := by linarith
  have ha2pos : 0 < a/2 := by linarith
  -- Reverse triangle inequality: `|x| ≤ |x - a/2| + a/2`.
  have hC : (1-a)/2 ≤ |x - a/2| := by
    have htri : |x| ≤ |x - a/2| + a/2 := by
      have h := abs_add_le (x - a/2) (a/2)
      rw [sub_add_cancel] at h
      rwa [abs_of_pos ha2pos] at h
    linarith
  -- Reverse triangle inequality: `|x| ≤ |x + a/2| + a/2`.
  have hD : (1-a)/2 ≤ |x + a/2| := by
    have htri : |x| ≤ |x + a/2| + a/2 := by
      have h := abs_add_le (x + a/2) (-(a/2))
      have h2 : x + a/2 + -(a/2) = x := by ring
      rw [h2] at h
      rwa [abs_neg, abs_of_pos ha2pos] at h
    linarith
  have hAB : |x + a/2| ≤ ((1+a)/(1-a)) * |x - a/2| ∧
             |x - a/2| ≤ ((1+a)/(1-a)) * |x + a/2| := by
    rcases le_or_gt ((1:ℝ)/2) x with hx1 | hx1
    · -- `x ≥ 1/2`: both `x + a/2` and `x - a/2` are nonnegative.
      have h1 : 0 ≤ x + a/2 := by linarith
      have h2 : 0 ≤ x - a/2 := by linarith
      rw [abs_of_nonneg h1, abs_of_nonneg h2]
      constructor
      · rw [div_mul_eq_mul_div, le_div_iff₀ hpos]; nlinarith [ha0, hx1]
      · rw [div_mul_eq_mul_div, le_div_iff₀ hpos]; nlinarith [ha0, hx1]
    · -- `x < 1/2` together with `|x| ≥ 1/2` forces `x ≤ -1/2`.
      have hx2 : x ≤ -(1/2) := by
        by_contra h
        push Not at h
        have : |x| < 1/2 := abs_lt.mpr ⟨h, hx1⟩
        linarith
      -- both `x + a/2` and `x - a/2` are negative.
      have h1 : x + a/2 < 0 := by linarith
      have h2 : x - a/2 < 0 := by linarith
      rw [abs_of_neg h1, abs_of_neg h2]
      constructor
      · rw [div_mul_eq_mul_div, le_div_iff₀ hpos]; nlinarith [ha0, hx2]
      · rw [div_mul_eq_mul_div, le_div_iff₀ hpos]; nlinarith [ha0, hx2]
  exact ⟨hAB.1, hAB.2, hC, hD⟩

theorem axis_ratio_quarter {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (k : ℤ) :
    |((1 / 2 + 2 * k : ℝ)) + a / 2| ≤ ((1 + a) / (1 - a)) * |((1 / 2 + 2 * k : ℝ)) - a / 2| ∧
    |((1 / 2 + 2 * k : ℝ)) - a / 2| ≤ ((1 + a) / (1 - a)) * |((1 / 2 + 2 * k : ℝ)) + a / 2| ∧
    (1 - a) / 2 ≤ |((1 / 2 + 2 * k : ℝ)) - a / 2| ∧
    (1 - a) / 2 ≤ |((1 / 2 + 2 * k : ℝ)) + a / 2| :=
  quarter_ratio_le_abs ha0 ha1 (abs_half_add_two_mul k)

end Work.EQ
