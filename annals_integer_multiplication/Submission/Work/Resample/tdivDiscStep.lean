import Mathlib

namespace Work.Resample

/-- Truncated-division remainder bound, used to control the rounding error of
`Int.tdiv`: for a positive divisor `n`, the remainder `A.tmod n` is strictly
smaller than `n` in absolute value. -/
private lemma tmod_cast_abs_lt (n : ℤ) (hn : 0 < n) (A : ℤ) :
    |((A.tmod n : ℤ) : ℝ)| < (n : ℝ) := by
  have h1 : ((A.tmod n : ℤ) : ℝ) < (n : ℝ) := by exact_mod_cast Int.tmod_lt_of_pos A hn
  have h2 : -(n : ℝ) < ((A.tmod n : ℤ) : ℝ) := by exact_mod_cast Int.lt_tmod_of_pos A hn
  exact abs_lt.mpr ⟨h2, h1⟩

/-- The `l¹` bound in the complex norm: `‖m + k·i‖ ≤ |m| + |k|` for integers. -/
private lemma norm_intCast_add_intCast_mul_I (m k : ℤ) :
    ‖((m : ℂ)) + ((k : ℂ)) * Complex.I‖ ≤ |(m : ℝ)| + |(k : ℝ)| := by
  rw [← Complex.ofReal_intCast m, ← Complex.ofReal_intCast k]
  calc ‖(((m : ℝ)) : ℂ) + (((k : ℝ)) : ℂ) * Complex.I‖
      ≤ ‖(((m : ℝ)) : ℂ)‖ + ‖(((k : ℝ)) : ℂ) * Complex.I‖ := norm_add_le _ _
    _ = |(m : ℝ)| + |(k : ℝ)| := by simp [Complex.norm_I]

/-- Truncating the real and imaginary parts of a Gaussian integer `A + B·i`
to multiples of `2^p` (rounding toward zero) costs at most `2` in the complex
norm, after scaling down by `2^p`. -/
theorem tdivDiscStep (p : ℕ) (A B : ℤ) (U : ℝ)
    (h : ‖((A : ℂ) + (B : ℂ) * Complex.I)‖ ≤ U) :
    ‖((A.tdiv ((2 : ℤ) ^ p) : ℤ) : ℂ) + ((B.tdiv ((2 : ℤ) ^ p) : ℤ) : ℂ) * Complex.I‖
      ≤ U / (2 : ℝ) ^ p + 2 := by
  set n : ℤ := (2 : ℤ) ^ p with hn
  set z : ℂ := (A : ℂ) + (B : ℂ) * Complex.I with hz
  set q : ℂ := ((A.tdiv n : ℤ) : ℂ) + ((B.tdiv n : ℤ) : ℂ) * Complex.I with hq
  have hnpos : 0 < n := by rw [hn]; positivity
  have hnn : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnpos
  have hncast : (n : ℝ) = (2 : ℝ) ^ p := by rw [hn]; push_cast; ring
  -- the rounding error `z - n q` is the pair of remainders
  have hdec : z - (n : ℂ) * q
      = ((A.tmod n : ℤ) : ℂ) + ((B.tmod n : ℤ) : ℂ) * Complex.I := by
    simp only [hz, hq, Int.tmod_def, Int.cast_sub, Int.cast_mul]
    ring
  -- each remainder is `< n` in absolute value, so the error is `< 2 n`
  have herr : ‖z - (n : ℂ) * q‖ < 2 * (n : ℝ) := by
    rw [hdec]
    calc ‖((A.tmod n : ℤ) : ℂ) + ((B.tmod n : ℤ) : ℂ) * Complex.I‖
        ≤ |((A.tmod n : ℤ) : ℝ)| + |((B.tmod n : ℤ) : ℝ)|
          := norm_intCast_add_intCast_mul_I _ _
      _ < (n : ℝ) + (n : ℝ) := add_lt_add (tmod_cast_abs_lt n hnpos A) (tmod_cast_abs_lt n hnpos B)
      _ = 2 * (n : ℝ) := by ring
  -- `‖n q‖ = n ‖q‖`
  have hmul : ‖(n : ℂ) * q‖ = (n : ℝ) * ‖q‖ := by
    rw [norm_mul, Complex.norm_intCast, abs_of_nonneg (le_of_lt hnn)]
  have hzU : ‖z‖ ≤ U := by rw [hz]; exact h
  -- triangle inequality: `n ‖q‖ ≤ ‖z‖ + ‖z - n q‖`
  have h1 : ‖(n : ℂ) * q‖ ≤ ‖z‖ + ‖z - (n : ℂ) * q‖ := by
    have := norm_sub_le z (z - (n : ℂ) * q)
    simpa using this
  have h2 : (n : ℝ) * ‖q‖ ≤ U + 2 * (n : ℝ) := by
    rw [← hmul]
    linarith
  have h3 : ‖q‖ ≤ U / (n : ℝ) + 2 := by
    rw [show U / (n : ℝ) + 2 = (U + 2 * (n : ℝ)) / (n : ℝ) by
      rw [add_div, mul_div_cancel_right₀ _ (ne_of_gt hnn)]]
    rw [le_div_iff₀ hnn]
    linarith
  rw [← hncast]
  exact h3

end Work.Resample
