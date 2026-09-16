import Mathlib.LinearAlgebra.Lagrange

open Polynomial Finset

namespace Commons.Algebra.Polynomial

/-- **Lagrange / partial-fraction identity**, with `DecidableEq ι` as an explicit type-class
binder (rather than a baked-in `Classical.decEq`, which would make the statement unusable when
specialised to concrete types such as `ℕ`).  For a nonempty finset `s` of indices whose nodal
values `v i` are pairwise distinct (`Set.InjOn v s`), the sum of the reciprocals of the products of
the differences `v i - v j` (`j ≠ i`, `j ∈ s`) equals `1` when `s` is a singleton and `0`
otherwise. -/
theorem sum_inv_prod_sub_decEq {ι : Type*} [DecidableEq ι] {K : Type*} [Field K]
    (s : Finset ι) (v : ι → K) (hs : s.Nonempty) (hvs : Set.InjOn v s) :
    ∑ i ∈ s, (∏ j ∈ s.erase i, (v i - v j))⁻¹ = if s.card = 1 then 1 else 0 := by
  have hcard : 0 < s.card := Finset.card_pos.mpr hs
  -- Each reciprocal is the coefficient of `X ^ (#s - 1)` in the corresponding Lagrange basis
  -- polynomial: that coefficient is its leading coefficient, and its degree is exactly `#s - 1`.
  have hstep : ∑ i ∈ s, (∏ j ∈ s.erase i, (v i - v j))⁻¹
      = ∑ i ∈ s, (Lagrange.basis s v i).coeff (s.card - 1) := by
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [← Lagrange.leadingCoeff_basis hvs hi, leadingCoeff,
      Lagrange.natDegree_basis hvs hi]
  rw [hstep, ← Polynomial.finsetSum_coeff, Lagrange.sum_basis hvs hs, Polynomial.coeff_one]
  by_cases h : s.card = 1
  · rw [if_pos h, if_pos (by omega : s.card - 1 = 0)]
  · rw [if_neg h, if_neg (by omega : ¬ s.card - 1 = 0)]

end Commons.Algebra.Polynomial