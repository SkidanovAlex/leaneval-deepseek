import Submission.ZagierHoffmanProof.ATIntegral

set_option autoImplicit false
set_option maxHeartbeats 2000000

open Polynomial RatFunc
open scoped BigOperators

/-!
# Regression checks for the Anderson–Thakur integrality at special indices

The shape `N = (0,1,0)` at `n = 3` over `F_2` (so `m = atIndex + 1 = 6`, the case checked by
hand in the SESSION 296 log: `α_6 = (X^4+X)(θ + t^2)^2`).
-/

namespace ZagierHoffmanPositiveChar

section Reg

attribute [local instance 100] Classical.decEq

lemma card_zmod2'' : Nat.card (ZMod 2) = 2 := by rw [Nat.card_eq_fintype_card, ZMod.card]

/-- The shape `N = (0,1,0)`. -/
abbrev shape310 : ℕ → ℕ := fun i => if i = 1 then 1 else 0

lemma shape310_sum : (∑ i ∈ Finset.range 3, shape310 i) ≤ Nat.card (ZMod 2) - 1 := by
  rw [card_zmod2'']
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, shape310]
  norm_num

/-- The special index is `6`. -/
example : atIndex (ZMod 2) 3 shape310 + 1 = 6 := by
  rw [atIndex, card_zmod2'']
  norm_num [shape310, Finset.sum_range_succ]

/-- ★ `α_6` is a polynomial in `θ` and `t`. -/
example : ∃ P : (ZMod 2)[X][X],
    atAlpha (ZMod 2) (atIndex (ZMod 2) 3 shape310 + 1)
      = algebraMap ((ZMod 2)[X][X]) (atQ (ZMod 2)) P :=
  atAlpha_atIndex_mem (ZMod 2) 3 (by norm_num) shape310 shape310_sum

end Reg

end ZagierHoffmanPositiveChar
