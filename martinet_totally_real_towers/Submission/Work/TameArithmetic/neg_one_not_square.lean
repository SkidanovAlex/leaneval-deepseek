import Mathlib

/-!
# `Work.TameArithmetic.neg_one_not_square`

`-1` is not a square in `ℚˣ`.  Together with `neg_one_mem_VS` and `VS_eq_pm_squares` this pins
down the `𝔽₂`-dimension of `V_S/ℚ^{×2}`: the classes of `1` and `-1` are exactly the two elements
of `V_S/ℚ^{×2}`.
-/

set_option autoImplicit false

namespace Work.TameArithmetic

/-- **`-1` is not a square in `ℚ`** (so `V_S/ℚ^{×2}` has at least two elements, and with
`VS_eq_pm_squares` exactly two). -/
theorem neg_one_not_square : ¬ ∃ y : ℚˣ, (-1 : ℚˣ) = y * y := by
  rintro ⟨y, hy⟩
  have h : (-1 : ℚ) = (y : ℚ) * (y : ℚ) := by
    have h1 : ((-1 : ℚˣ) : ℚ) = ((y : ℚˣ) : ℚ) * ((y : ℚˣ) : ℚ) := by
      rw [hy, Units.val_mul]
    simpa using h1
  nlinarith [sq_nonneg (y : ℚ)]

end Work.TameArithmetic
