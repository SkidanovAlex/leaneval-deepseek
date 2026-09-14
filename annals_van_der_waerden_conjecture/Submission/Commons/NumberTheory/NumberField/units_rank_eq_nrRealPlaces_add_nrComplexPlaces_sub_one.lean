import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem

namespace Commons.NumberTheory.NumberField

theorem units_rank_eq_nrRealPlaces_add_nrComplexPlaces_sub_one (K : Type*) [Field K] [NumberField K] : NumberField.InfinitePlace.nrRealPlaces K + NumberField.InfinitePlace.nrComplexPlaces K - 1 = NumberField.Units.rank K := by
  rw [NumberField.Units.rank, NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces]

end Commons.NumberTheory.NumberField