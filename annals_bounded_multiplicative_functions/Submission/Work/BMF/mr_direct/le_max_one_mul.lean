import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.mr_direct

/-- For `0 ≤ K` and `0 ≤ X, Y`: `X + K * Y ≤ max 1 K * (X + Y)`. -/
theorem le_max_one_mul (K X Y : ℝ) (hK : 0 ≤ K) (hX : 0 ≤ X) (hY : 0 ≤ Y) :
    X + K * Y ≤ max 1 K * (X + Y) := by
  have h1 : (1 : ℝ) ≤ max 1 K := le_max_left 1 K
  have h2 : K ≤ max 1 K := le_max_right 1 K
  have hmaxnn : (0 : ℝ) ≤ max 1 K := le_trans hK h2
  have hX' : X ≤ max 1 K * X := by
    calc X = 1 * X := (one_mul X).symm
      _ ≤ max 1 K * X := mul_le_mul_of_nonneg_right h1 hX
  have hY' : K * Y ≤ max 1 K * Y := mul_le_mul h2 le_rfl hY hmaxnn
  have hExp : max 1 K * (X + Y) = max 1 K * X + max 1 K * Y := mul_add _ _ _
  linarith [hX', hY']

end Work.BMF.mr_direct
