import Mathlib
import Submission.Work.ClassFieldTower.Defs
import Submission.Work.ClassFieldTower.WitnessField
import Submission.Work.ClassFieldTower.unitTwoRank_eq_one_of_imaginaryQuadratic

namespace Work.ClassFieldTower

/-- **`d₂(O_{Kc}^×) = 1` for the explicit witness field `Kc = ℚ(√-30030)`** (equality, sharpening
`Work.ClassFieldTower.unitTwoRank_witness_le_one`): `unitTwoRank F = NumberField.Units.rank F + 1`
is `r₁ + r₂`, which is `1` for an imaginary quadratic field.

Immediate from `Work.ClassFieldTower.unitTwoRank_eq_one_of_imaginaryQuadratic` applied to
`Kc` (`Module.finrank ℚ Kc = 2`), whose `NumberField.IsTotallyComplex` instance is
`Work.ClassFieldTower.isTotallyComplex` (`WitnessField.lean`). -/
theorem unitTwoRank_witness_eq_one : unitTwoRank Kc = 1 := by
  have htc : NumberField.IsTotallyComplex Kc := isTotallyComplex
  exact unitTwoRank_eq_one_of_imaginaryQuadratic Kc finrank_eq_two

end Work.ClassFieldTower
