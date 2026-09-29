import Mathlib.Data.Int.ConditionallyCompleteOrder
import Submission.Commons.FieldTheory.RatFunc.ordInfT_mul

namespace Commons.FieldTheory.RatFunc

theorem ordInfT_add_le_max {K : Type*} [Field K] (x y : RatFunc K) (hxy : x + y ≠ 0) :
    ordInfT (x + y) ≤ max (ordInfT x) (ordInfT y) := by
  rcases eq_or_ne x 0 with rfl | hx
  · rw [zero_add]
    simp [ordInfT]
  rcases eq_or_ne y 0 with rfl | hy
  · rw [add_zero]
    simp [ordInfT]
  rw [ordInfT_eq_coe_intDegree hxy, ordInfT_eq_coe_intDegree hx, ordInfT_eq_coe_intDegree hy,
    ← WithTop.coe_max]
  exact WithTop.coe_le_coe.mpr (RatFunc.intDegree_add_le hy hxy)

end Commons.FieldTheory.RatFunc