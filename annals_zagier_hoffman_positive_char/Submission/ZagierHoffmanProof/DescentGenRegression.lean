import Submission.ZagierHoffmanProof.DescentGenCor

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Polynomial
open scoped BigOperators

/-!
# Regression tests for the general Frobenius descent

Concrete instances of `atCoeff_descend` and `atCoeff_mul_card_add_pred` over `F₂` and `F₃`.
-/

namespace ZagierHoffmanPositiveChar

attribute [local instance 100] Classical.decEq

section ZMod2

example : Nat.card (ZMod 2) = 2 := by rw [Nat.card_eq_fintype_card, ZMod.card]

/-- The one-residue descent over `F₂`: `c_3 = (c_1)^2` (both are `1`). -/
example : atCoeff (ZMod 2) 3 = (atCoeff (ZMod 2) 1) ^ 2 :=
  by simpa [Nat.card_eq_fintype_card] using atCoeff_mul_card_add_pred (ZMod 2) 1

/-- `c_7 = (c_3)^2` over `F₂`. -/
example : atCoeff (ZMod 2) 7 = (atCoeff (ZMod 2) 3) ^ 2 :=
  by simpa [Nat.card_eq_fintype_card] using atCoeff_mul_card_add_pred (ZMod 2) 3

/-- `c_15 = (c_7)^2` over `F₂`. -/
example : atCoeff (ZMod 2) 15 = (atCoeff (ZMod 2) 7) ^ 2 :=
  by simpa [Nat.card_eq_fintype_card] using atCoeff_mul_card_add_pred (ZMod 2) 7

/-- The general descent over `F₂` at `N = 5`: the residue set consists of `(1,0,…)` and `(1,2,…)`. -/
example : atCoeff (ZMod 2) 5 =
    ∑ res ∈ residueSet (ZMod 2) 5 6,
      (((Nat.multinomial Finset.univ res : ℕ) : atQ (ZMod 2))
          * ∏ i : Fin 6, atE (ZMod 2) ((i : ℕ)) ^ (res i))
        * (atCoeff (ZMod 2) ((5 - ∑ i, res i * Nat.card (ZMod 2) ^ (i : ℕ)) / Nat.card (ZMod 2))) ^ 2 :=
  by simpa [Nat.card_eq_fintype_card] using atCoeff_descend (ZMod 2) 5 6 (by norm_num)

end ZMod2

section ZMod3

example : Nat.card (ZMod 3) = 3 := by rw [Nat.card_eq_fintype_card, ZMod.card]

/-- The one-residue descent over `F₃`: `c_{11} = (c_3)^3`. -/
example : atCoeff (ZMod 3) 11 = (atCoeff (ZMod 3) 3) ^ 3 :=
  by simpa [Nat.card_eq_fintype_card] using atCoeff_mul_card_add_pred (ZMod 3) 3

/-- `c_{17} = (c_5)^3` over `F₃`. -/
example : atCoeff (ZMod 3) 17 = (atCoeff (ZMod 3) 5) ^ 3 :=
  by simpa [Nat.card_eq_fintype_card] using atCoeff_mul_card_add_pred (ZMod 3) 5

/-- The one-residue residue set over `F₃` is a single point. -/
example : residueSet (ZMod 3) (3 * 4 + (3 - 1)) 14 = {deltaRes (ZMod 3) (B := 14)} :=
  by simpa [Nat.card_eq_fintype_card] using residueSet_eq_singleton (ZMod 3) 4 14 (by norm_num)

end ZMod3

end ZagierHoffmanPositiveChar
