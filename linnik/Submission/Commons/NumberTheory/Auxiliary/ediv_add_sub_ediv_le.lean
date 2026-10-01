import Mathlib

set_option linter.unusedVariables false

namespace Commons.NumberTheory.Auxiliary

/-- For positive `l` and any integers `X, Y`,
`(X + Y) / l - X / l ≤ Y / l + 1`. -/
theorem ediv_add_sub_ediv_le {l : ℤ} (hl : 0 < l) (X Y : ℤ) (hY : 0 ≤ Y) :
    (X + Y) / l - X / l ≤ Y / l + 1 := by
  rw [Int.add_ediv_of_pos hl]
  split <;> omega

end Commons.NumberTheory.Auxiliary
