import Mathlib

namespace Work.ORFinal.OreField

open SkewMonoidAlgebra
open Multiplicative (ofAdd toAdd)

/-- Coefficient extraction for a product of an element of the skew monoid algebra `D[ℤ]` with a
finite sum of `single`-terms: expanding the product and reading off the `m`-th coefficient collects,
for each summand `j`, the `(m - j)`-th coefficient of `f`, twisted by the action of `m`. -/
theorem coeff_mul_finset_sum_single {D : Type*} [DivisionRing D]
    [MulSemiringAction (Multiplicative ℤ) D] (N : ℕ) (f : SkewMonoidAlgebra D (Multiplicative ℤ))
    (C : Fin N → D) (m : ℤ) :
    (f * ∑ j : Fin N, SkewMonoidAlgebra.single (Multiplicative.ofAdd ((j : ℕ) : ℤ))
        (Multiplicative.ofAdd ((j : ℕ) : ℤ) • C j)).coeff (Multiplicative.ofAdd m)
      = ∑ j : Fin N, f.coeff (Multiplicative.ofAdd (m - ((j : ℕ) : ℤ))) *
          (Multiplicative.ofAdd m • C j) := by
  classical
  rw [Finset.mul_sum]
  rw [show (∑ j : Fin N, f * SkewMonoidAlgebra.single (Multiplicative.ofAdd ((j : ℕ) : ℤ))
        (Multiplicative.ofAdd ((j : ℕ) : ℤ) • C j)).coeff
      = ∑ j : Fin N, (f * SkewMonoidAlgebra.single (Multiplicative.ofAdd ((j : ℕ) : ℤ))
        (Multiplicative.ofAdd ((j : ℕ) : ℤ) • C j)).coeff from
    map_sum SkewMonoidAlgebra.coeffAddEquiv _ _]
  rw [Finsupp.finsetSum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [SkewMonoidAlgebra.coeff_mul_single, ← div_eq_mul_inv, ← ofAdd_sub]
  congr 1
  rw [← mul_smul]
  rw [show Multiplicative.ofAdd (m - ((j : ℕ) : ℤ)) * Multiplicative.ofAdd (((j : ℕ) : ℤ))
      = Multiplicative.ofAdd m from by rw [← ofAdd_add, sub_add_cancel]]

end Work.ORFinal.OreField
