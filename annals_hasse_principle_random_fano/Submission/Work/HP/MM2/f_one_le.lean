import Mathlib

namespace Work.HP.MM2

/-- For `1 ≤ T` the `j`-th summand telescopes to `2 * A 1`, so the sum over
`j < J+1` is `((J:ℝ)+1) * (2 * A 1)`, whence it is bounded by
`4 * ((J:ℝ)+1) * A 1` for `0 ≤ A 1`. -/
lemma f_one_le (J : ℕ) (T : ℝ) (A : ℕ → ℝ) (hT : 1 ≤ T) (hA1 : 0 ≤ A 1) :
    (∑ j ∈ Finset.range (J+1), ((2:ℝ)^(j+1)/T) * ((T/(2:ℝ)^j)^1 * A 1)) ≤ 4 * ((J:ℝ)+1) * A 1 := by
  have hterm : ∀ j ∈ Finset.range (J+1), ((2:ℝ)^(j+1)/T) * ((T/(2:ℝ)^j)^1 * A 1) = 2 * A 1 := by
    intro j _
    have h2j : (2:ℝ)^j ≠ 0 := by positivity
    have h2j1 : (2:ℝ)^(j+1) = 2^j * 2 := by rw [pow_succ]
    rw [h2j1, pow_one]
    field_simp
  rw [Finset.sum_congr rfl hterm]
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  push_cast
  have hJ : (0:ℝ) ≤ (J:ℝ) + 1 := by positivity
  nlinarith [hA1, hJ]

end Work.HP.MM2
