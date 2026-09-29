import Mathlib

namespace Work.CNum

/-- The term-by-term step in the Taylor series of `cos`: the `(i+1)`-st summand of
`cos z` is the `i`-th summand multiplied by `-(z*z) * 1/((2i+1)(2i+2))`. -/
theorem cosTermStep (z : ℝ) (i : ℕ) :
    (-1 : ℝ) ^ (i + 1) * z ^ (2 * (i + 1)) / ((2 * (i + 1)).factorial : ℝ)
      = -(((-1 : ℝ) ^ i * z ^ (2 * i) / ((2 * i).factorial : ℝ)) * (z * z)) *
          (1 / (((2 * i + 1) * (2 * i + 2) : ℕ) : ℝ)) := by
  have hfac : ((2 * (i + 1)).factorial : ℝ)
      = ((2 * i).factorial : ℝ) * ((2 * i + 1 : ℕ) : ℝ) * ((2 * i + 2 : ℕ) : ℝ) := by
    have h : 2 * (i + 1) = 2 * i + 2 := by ring
    rw [h, show 2 * i + 2 = (2 * i + 1) + 1 from by ring, Nat.factorial_succ,
      Nat.factorial_succ]
    push_cast
    ring
  rw [hfac, show (2 : ℕ) * (i + 1) = 2 * i + 2 from by ring, pow_succ, pow_add, pow_two]
  push_cast
  have h0 : ((2 * i).factorial : ℝ) ≠ 0 := by positivity
  have h1 : ((2 * i + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have h2 : ((2 * i + 2 : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp

end Work.CNum
