import Mathlib
import Submission.Work.CFT.Kummer.Defs

namespace Work.CFT.Kummer
/-- Dirichlet's unit theorem for a totally real cubic field: `r₁ = 3`, `r₂ = 0`, so the unit rank
`r₁ + r₂ - 1` is `2`. -/
theorem units_rank_eq_two_of_totallyReal_cubic (K : Type*) [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (h : Module.finrank ℚ K = 3) :
    NumberField.Units.rank K = 2 := by
  -- Dirichlet: rank = #(infinite places) - 1; totally real ⇒ all 3 places are real.
  have h1 : Fintype.card (NumberField.InfinitePlace K) = 3 := by
    rw [NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
      NumberField.IsTotallyReal.nrComplexPlaces_eq_zero, add_zero,
      ← NumberField.IsTotallyReal.finrank]
    exact h
  rw [NumberField.Units.rank, h1]

end Work.CFT.Kummer
