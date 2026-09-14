import Mathlib.NumberTheory.Height.NumberField

namespace Commons.NumberTheory.Height.NumberField

open scoped BigOperators

/-- The multiplicative height of a positive natural number inside a number field `K` is
`n ^ [K : ℚ]`. -/
theorem mulHeight1_natCast {K : Type*} [Field K] [NumberField K] (n : ℕ) (hn : 1 ≤ n) :
    Height.mulHeight₁ (n : K) = (n : ℝ) ^ Height.totalWeight K := by
  rw [NumberField.mulHeight₁_eq]
  have hmax : ∀ v : NumberField.InfinitePlace K, max (v (n : K)) 1 = (n : ℝ) := by
    intro v
    rw [NumberField.InfinitePlace.map_natCast]
    exact max_eq_left (by exact_mod_cast hn)
  have hfin : (∏ᶠ v : NumberField.FinitePlace K, max (v (n : K)) 1) = 1 := by
    refine finprod_eq_one_of_forall_eq_one fun v => ?_
    have hv : IsNonarchimedean (v : K → ℝ) := fun a b => map_add_le_max v a b
    have hle : v (n : K) ≤ 1 := IsNonarchimedean.apply_natCast_le_one hv
    rw [max_eq_right hle]
  have harch : (∏ v : NumberField.InfinitePlace K, max (v (n : K)) 1 ^ v.mult)
      = (n : ℝ) ^ Height.totalWeight K := by
    simp_rw [hmax]
    rw [Finset.prod_pow_eq_pow_sum, ← NumberField.totalWeight_eq_sum_mult]
  rw [harch, hfin, mul_one]

end Commons.NumberTheory.Height.NumberField