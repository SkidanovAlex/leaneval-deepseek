import Submission.ZagierHoffmanProof.ATSeries

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Polynomial
open scoped BigOperators

/-!
# Regression tests for the Anderson–Thakur generating series

Concrete instances of `atCoeff_eq_coeff_inv` and `atCoeff_eq_sum_seq` over `ZMod 2` / `ZMod 3`.
-/

namespace ZagierHoffmanPositiveChar

attribute [local instance 100] Classical.decEq

open PowerSeries

/-- The easy range: `c_n = 1` for `n < q`. -/
example : atCoeff (ZMod 3) 2 = 1 := atCoeff_eq_one_of_lt _ (by norm_num)

/-- `α_n = 1` for `1 ≤ n ≤ q`. -/
example : atAlpha (ZMod 3) 3 = 1 := atAlpha_eq_one_of_le _ (by norm_num) (by norm_num)

/-- The generating-function form of the Anderson–Thakur coefficients, at `q = 2`. -/
example : atCoeff (ZMod 2) 5 = PowerSeries.coeff 5 ((1 - atS (ZMod 2))⁻¹) :=
  atCoeff_eq_coeff_inv _ 5

/-- The ordered-partition form, at `q = 2`. -/
example : atCoeff (ZMod 2) 4 = ∑ m ∈ Finset.range (4 + 1), ∑ a : Fin m → Fin 5,
    (if (∑ i, (2 : ℕ) ^ ((a i : ℕ))) = 4 then
      ∏ i, (atGamma (ZMod 2) ((a i : ℕ))) * (atD (ZMod 2) ((a i : ℕ)))⁻¹ else 0) := by
  have h := atCoeff_eq_sum_seq (ZMod 2) 4 5 (by norm_num)
  rw [h]
  refine Finset.sum_congr rfl (fun m _ => Finset.sum_congr rfl (fun a _ => ?_))
  rw [show Nat.card (ZMod 2) = 2 from by rw [Nat.card_eq_fintype_card, ZMod.card]]

end ZagierHoffmanPositiveChar
