import Mathlib
import Submission.Commons.NumberTheory.NumberField.nrComplexPlaces_odd_of_discr_neg

namespace Commons.NumberTheory.NumberField

/-- A number field of degree `3` with negative discriminant has exactly one complex place.
The sign formula forces the number of complex places to be odd, while
`nrRealPlaces + 2 * nrComplexPlaces = finrank ℚ K = 3` forces it to be at most one; the only odd
possibility is `1`. -/
theorem nrComplexPlaces_eq_one_of_finrank_three_of_discr_neg {K : Type*} [Field K] [NumberField K]
    (hfin : Module.finrank ℚ K = 3) (hneg : NumberField.discr K < 0) :
    NumberField.InfinitePlace.nrComplexPlaces K = 1 := by
  obtain ⟨k, hk⟩ := nrComplexPlaces_odd_of_discr_neg K hneg
  have hrank := NumberField.InfinitePlace.card_add_two_mul_card_eq_rank K
  rw [hfin] at hrank
  omega

end Commons.NumberTheory.NumberField
