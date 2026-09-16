import Mathlib.FieldTheory.Finite.Basic

open scoped BigOperators

namespace Commons.FieldTheory.Finite

/-- The sum of the `m`-th powers of the inverses of all units of a finite field `K`
is `-1` if `Fintype.card K - 1 ∣ m`, and `0` otherwise. -/
theorem sum_units_inv_pow {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (m : ℕ) (hm : 0 < m) :
    (∑ u : Kˣ, ((u : K)⁻¹) ^ m) = if Fintype.card K - 1 ∣ m then (-1 : K) else 0 := by
  calc
    (∑ u : Kˣ, ((u : K)⁻¹) ^ m) = ∑ u : Kˣ, ((u⁻¹ : Kˣ) : K) ^ m := by
      apply Finset.sum_congr rfl
      intro u _
      simp
    _ = ∑ u : Kˣ, (u : K) ^ m := by
      exact Equiv.sum_comp (Equiv.inv Kˣ) (fun v : Kˣ => (v : K) ^ m)
    _ = if Fintype.card K - 1 ∣ m then (-1 : K) else 0 := by
      exact FiniteField.sum_pow_units K m

end Commons.FieldTheory.Finite
