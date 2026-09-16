import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.RingTheory.SimpleRing.Principal

namespace Commons.FieldTheory.RatFunc

theorem num_mul_prod_erase_denom {K : Type*} [Field K] {ι : Type*} [DecidableEq ι] (T : Finset ι)
    (c : ι → RatFunc K) {i : ι} (hi : i ∈ T) :
    ((RatFunc.num (c i) * ∏ j ∈ T.erase i, RatFunc.denom (c j) : Polynomial K) : RatFunc K)
      = c i * ((∏ j ∈ T, RatFunc.denom (c j) : Polynomial K) : RatFunc K) := by
  have hD : algebraMap (Polynomial K) (RatFunc K) (RatFunc.denom (c i)) ≠ 0 :=
    RatFunc.algebraMap_ne_zero (RatFunc.denom_ne_zero (c i))
  have hnum : algebraMap (Polynomial K) (RatFunc K) (RatFunc.num (c i))
      = c i * algebraMap (Polynomial K) (RatFunc K) (RatFunc.denom (c i)) :=
    (div_eq_iff hD).mp (RatFunc.num_div_denom (c i))
  have hQ : algebraMap (Polynomial K) (RatFunc K) (∏ j ∈ T, RatFunc.denom (c j))
      = algebraMap (Polynomial K) (RatFunc K) (RatFunc.denom (c i))
        * algebraMap (Polynomial K) (RatFunc K) (∏ j ∈ T.erase i, RatFunc.denom (c j)) := by
    rw [← Finset.mul_prod_erase T (fun j => RatFunc.denom (c j)) hi]
    exact map_mul (algebraMap (Polynomial K) (RatFunc K)) _ _
  show algebraMap (Polynomial K) (RatFunc K) (RatFunc.num (c i) * ∏ j ∈ T.erase i, RatFunc.denom (c j))
      = c i * algebraMap (Polynomial K) (RatFunc K) (∏ j ∈ T, RatFunc.denom (c j))
  rw [map_mul (algebraMap (Polynomial K) (RatFunc K)), hQ, hnum]
  ring

end Commons.FieldTheory.RatFunc