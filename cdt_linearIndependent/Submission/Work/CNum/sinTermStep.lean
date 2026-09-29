import Mathlib

namespace Work.CNum

/-- Second-order step identity for the odd (sine) Taylor terms. -/
theorem sinTermStep (z : ℝ) (i : ℕ) :
    (-1 : ℝ) ^ (i + 1) * z ^ (2 * (i + 1) + 1) / ((2 * (i + 1) + 1).factorial : ℝ)
      = -(((-1 : ℝ) ^ i * z ^ (2 * i + 1) / ((2 * i + 1).factorial : ℝ)) * (z * z)) *
          (1 / (((2 * i + 2) * (2 * i + 3) : ℕ) : ℝ)) := by
  have hf : ((2 * (i + 1) + 1).factorial : ℝ)
      = ((2 * i + 1).factorial : ℝ) * ((2 * i + 2 : ℕ) : ℝ) * ((2 * i + 3 : ℕ) : ℝ) := by
    have h : 2 * (i + 1) + 1 = 2 * i + 3 := by ring
    rw [h, show 2 * i + 3 = (2 * i + 2) + 1 by ring, Nat.factorial_succ, Nat.factorial_succ]
    push_cast
    ring
  rw [hf]
  have hD : (((2 * i + 2) * (2 * i + 3) : ℕ) : ℝ)
      = ((2 * i + 2 : ℕ) : ℝ) * ((2 * i + 3 : ℕ) : ℝ) := by push_cast; ring
  rw [hD]
  have h1 : (((2 * i + 1).factorial : ℝ)) ≠ 0 := by positivity
  have h2 : ((2 * i + 2 : ℕ) : ℝ) ≠ 0 := by positivity
  have h3 : ((2 * i + 3 : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp
  ring

end Work.CNum
