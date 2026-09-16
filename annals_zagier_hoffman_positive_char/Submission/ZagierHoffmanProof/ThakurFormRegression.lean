/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Submission.ZagierHoffmanProof.ThakurForm

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Polynomial
open scoped BigOperators

/-!
# Regression checks for Thakur's polynomial form of the level-one shuffle relation

`ThakurForm.thakurPoly_mul` was validated numerically in exact `F_q[T]` arithmetic for
`q ∈ {2,3,4,5,8,9}` and `a, b ≤ 5` (script `/tmp/ses299/tf.py`).
-/

namespace ThakurFormRegression

attribute [local instance 100] Classical.decEq

open ZagierHoffmanPositiveChar

/-- `b_0 = 1` over `F₂`. -/
example : thakurPoly (ZMod 2) 0 = 1 := thakurPoly_zero (ZMod 2)

/-- `b_1 = -1` over `F₂`. -/
example : thakurPoly (ZMod 2) 1 = -1 := thakurPoly_one (ZMod 2)

/-- The specialisation recovers `A_n` over `F₂`. -/
example : Phi (ZMod 2) (thakurPoly (ZMod 2) 3) = A (ZMod 2) 3 :=
  Phi_thakurPoly (ZMod 2) 3 (by norm_num)

/-- The easy range over `F₃`. -/
example : thakurPoly (ZMod 3) 3 = (-1 : (ZMod 3)[X]) ^ 3 :=
  thakurPoly_eq_neg_one_pow (ZMod 3) 3 (by norm_num) (by norm_num)

/-- Thakur's polynomial shuffle relation over `F₂` at weights `2 × 2`. -/
example : thakurPoly (ZMod 2) 2 * thakurPoly (ZMod 2) 2 = thakurPoly (ZMod 2) 4 +
    ∑ k ∈ Finset.Icc 1 ((2 + 2 - 1) / (Nat.card (ZMod 2) - 1)),
      Polynomial.C (ChenDeltaZ (ZMod 2) 2 2 ((Nat.card (ZMod 2) - 1) * k) : ZMod 2) *
        Polynomial.X ^ k * thakurPoly (ZMod 2) (2 + 2 - (Nat.card (ZMod 2) - 1) * k) :=
  thakurPoly_mul (ZMod 2) 2 2 (by norm_num) (by norm_num)

/-- Thakur's polynomial shuffle relation over `F₃` at weights `3 × 2`. -/
example : thakurPoly (ZMod 3) 3 * thakurPoly (ZMod 3) 2 = thakurPoly (ZMod 3) 5 +
    ∑ k ∈ Finset.Icc 1 ((3 + 2 - 1) / (Nat.card (ZMod 3) - 1)),
      Polynomial.C (ChenDeltaZ (ZMod 3) 3 2 ((Nat.card (ZMod 3) - 1) * k) : ZMod 3) *
        Polynomial.X ^ k * thakurPoly (ZMod 3) (3 + 2 - (Nat.card (ZMod 3) - 1) * k) :=
  thakurPoly_mul (ZMod 3) 3 2 (by norm_num) (by norm_num)

/-- The Thakur–Pascal recursion over `F₂` at `n = 3`. -/
example : thakurPoly (ZMod 2) 3 + thakurPoly (ZMod 2) 2 =
    Polynomial.X * thakurPoly (ZMod 2) (3 - Nat.card (ZMod 2)) :=
  thakurPoly_rec (ZMod 2) 3 (by norm_num)

end ThakurFormRegression
