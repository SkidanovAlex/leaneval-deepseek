import Submission.ZagierHoffmanProof.AFormulaDegree

set_option autoImplicit false
set_option maxHeartbeats 2000000

open Polynomial
open scoped BigOperators

/-!
# Regression checks for `natDegree A_n` and the closed form of `jMin`
-/

namespace ZagierHoffmanPositiveChar

section Reg

attribute [local instance 100] Classical.decEq

lemma card_zmod2' : Nat.card (ZMod 2) = 2 := by rw [Nat.card_eq_fintype_card, ZMod.card]
lemma card_zmod3' : Nat.card (ZMod 3) = 3 := by rw [Nat.card_eq_fintype_card, ZMod.card]

/-- The degree formula over `F_2` at `n = 3`. -/
example : (A (ZMod 2) 3).natDegree = (2 - 1) * 2 * mStar (ZMod 2) 3 := by
  rw [natDegree_A (ZMod 2) 3 (by norm_num), card_zmod2']

/-- The degree formula over `F_3` at `n = 4` (where `A_4 = 1 - [1]^2`). -/
example : (A (ZMod 3) 4).natDegree = (3 - 1) * 3 * mStar (ZMod 3) 4 := by
  rw [natDegree_A (ZMod 3) 4 (by norm_num), card_zmod3']

/-- Thakur's `jMin` in closed form over `F_2` at `n = 5`. -/
example : jMin (ZMod 2) 5 = (2 - 1) * (5 - 2 * mStar (ZMod 2) 5) := by
  have h := jMin_eq_mStar (ZMod 2) 5
  rw [card_zmod2'] at h
  simpa using h

/-- `mStar` is admissible: `q · mStar n ≤ n`. -/
example : 2 * mStar (ZMod 2) 7 ≤ 7 := by
  have := card_mul_mStar_le (ZMod 2) 7
  rwa [card_zmod2'] at this

end Reg

end ZagierHoffmanPositiveChar
