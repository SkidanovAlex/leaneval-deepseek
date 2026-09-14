import Mathlib.NumberTheory.NumberField.Discriminant.Basic
import Mathlib.Algebra.Ring.Parity

namespace Commons.NumberTheory.NumberField

/-- The number of complex places of a number field is odd exactly when its discriminant is
negative. This is the sign formula `discr K = (-1) ^ nrComplexPlaces K · |discr K|`
(`NumberField.sign_discr`): a negative discriminant forces an odd number of conjugate pairs
of complex embeddings. -/
theorem nrComplexPlaces_odd_of_discr_neg (K : Type*) [Field K] [NumberField K]
    (h : NumberField.discr K < 0) : Odd (NumberField.InfinitePlace.nrComplexPlaces K) := by
  have hsign := NumberField.sign_discr K
  rw [Int.sign_eq_neg_one_of_neg h] at hsign
  exact (neg_one_pow_eq_neg_one_iff_odd (by norm_num : (-1 : ℤ) ≠ 1)).mp hsign.symm

end Commons.NumberTheory.NumberField
