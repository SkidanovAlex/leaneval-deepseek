import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

theorem factorial_sq_identity (X : ℕ) (hX : 1 ≤ X) :
    ((X.factorial : ℕ) : ℝ) ^ 2 =
      (X : ℝ) ^ 2 * ((((X - 1).factorial : ℕ)) : ℝ) ^ 2 := by
  have h : X.factorial = X * (X - 1).factorial :=
    (Nat.mul_factorial_pred (by omega)).symm
  rw [h]
  push_cast
  ring

end Work.BW
