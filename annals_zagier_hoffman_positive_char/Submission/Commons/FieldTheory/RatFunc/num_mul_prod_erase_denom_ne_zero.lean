import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

namespace Commons.FieldTheory.RatFunc

theorem num_mul_prod_erase_denom_ne_zero {K : Type*} [Field K] {ι : Type*} [DecidableEq ι]
    (T : Finset ι) (c : ι → RatFunc K) {i : ι} (hi : i ∈ T) (hci : c i ≠ 0) :
    RatFunc.num (c i) * ∏ j ∈ T.erase i, RatFunc.denom (c j) ≠ 0 := by
  apply mul_ne_zero (RatFunc.num_ne_zero hci)
  rw [Finset.prod_ne_zero_iff]
  intro j _
  exact RatFunc.denom_ne_zero (c j)

end Commons.FieldTheory.RatFunc