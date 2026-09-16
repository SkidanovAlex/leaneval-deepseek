import Submission.ZagierHoffmanProof.Descent

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Polynomial
open scoped BigOperators

/-!
# Regression tests for the Frobenius descent

Concrete instances of `atCoeff_card_pow_sub_one` over `ZMod 2`, `ZMod 3` and the non-prime field
`GaloisField 2 2` (cardinality `4`).
-/

section Concrete

attribute [local instance 100] Classical.decEq

open ZagierHoffmanPositiveChar

example : atCoeff (ZMod 2) 0 = 1 := by
  simpa [Nat.card_eq_fintype_card] using atCoeff_card_pow_sub_one (ZMod 2) 0

example : atCoeff (ZMod 2) 1 = 1 := by
  simpa [Nat.card_eq_fintype_card] using atCoeff_card_pow_sub_one (ZMod 2) 1

example : atCoeff (ZMod 2) 15 = 1 := by
  simpa [Nat.card_eq_fintype_card] using atCoeff_card_pow_sub_one (ZMod 2) 4

example : atCoeff (ZMod 3) 2 = 1 := by
  simpa [Nat.card_eq_fintype_card] using atCoeff_card_pow_sub_one (ZMod 3) 1

example : atCoeff (ZMod 3) 8 = 1 := by
  simpa [Nat.card_eq_fintype_card] using atCoeff_card_pow_sub_one (ZMod 3) 2

example : atCoeff (ZMod 3) 26 = 1 := by
  simpa [Nat.card_eq_fintype_card] using atCoeff_card_pow_sub_one (ZMod 3) 3

/-- `H_{q^2-1} = Γ_{q^2}` over `F_4`, i.e. `atCoeff 15 = 1` for `q = 4`. -/
example : atCoeff (GaloisField 2 2) 15 = 1 := by
  simpa [Nat.card_eq_fintype_card, GaloisField.card] using
    atCoeff_card_pow_sub_one (GaloisField 2 2) 2

/-- The descent step in a concrete case: `c_{26} = (c_8)^3` over `F_3`. -/
example : atCoeff (ZMod 3) 26 = (atCoeff (ZMod 3) 8) ^ 3 := by
  simpa [Nat.card_eq_fintype_card] using atCoeff_card_pow_sub_one_succ (ZMod 3) 2

end Concrete
