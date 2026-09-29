import Mathlib

namespace Work.Holonomy3

open scoped BigOperators

/-- The denominator of a finite product of rationals divides the product of the denominators. -/
theorem den_finsetProd_dvd {ι : Type*} (s : Finset ι) (g : ι → ℚ) :
    (∏ i ∈ s, g i).den ∣ ∏ i ∈ s, (g i).den := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.prod_insert ha]
      exact (Rat.mul_den_dvd (g a) (∏ i ∈ s, g i)).trans (Nat.mul_dvd_mul_left _ ih)

end Work.Holonomy3
