import Mathlib
import Submission.Work.ClassFieldTower.Defs

/-!
# `unitTwoRank` of an imaginary quadratic field

`unitTwoRank F = NumberField.Units.rank F + 1` is the `𝔽₂`-dimension of
`O_F^× / (O_F^×)² = r₁ + r₂` (`r₁` = number of real places, `r₂` = number of
complex places).  Mathlib computes the unit rank as
`NumberField.Units.rank F = Fintype.card (InfinitePlace F) - 1`, so it suffices
to know that an imaginary quadratic field has exactly one infinite place.

Totally complex of degree `2` means `r₁ = 0` and `2 * r₂ = [F : ℚ] = 2`, i.e.
`r₂ = 1`, so `Fintype.card (InfinitePlace F) = r₁ + r₂ = 1` and
`unitTwoRank F = 1 - 1 + 1 = 1`.
-/

open NumberField

namespace Work.ClassFieldTower

theorem unitTwoRank_eq_one_of_imaginaryQuadratic (F : Type*) [Field F] [NumberField F]
    [NumberField.IsTotallyComplex F] (h2 : Module.finrank ℚ F = 2) : unitTwoRank F = 1 := by
  -- `r₂ = 1`: `[F : ℚ] = 2 = 2 * r₂` for a totally complex field.
  have hnr : InfinitePlace.nrComplexPlaces F = 1 := by
    have h := NumberField.IsTotallyComplex.finrank F
    rw [h2] at h
    omega
  -- `r₁ = 0`: all infinite places are complex.
  have hreal : InfinitePlace.nrRealPlaces F = 0 := by simp
  -- hence `F` has exactly one infinite place.
  have hcard : Fintype.card (InfinitePlace F) = 1 := by
    rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces, hreal, hnr, zero_add]
  -- `rank F = 1 - 1 = 0`, so `unitTwoRank F = 0 + 1 = 1`.
  simp only [unitTwoRank, NumberField.Units.rank, hcard]

end Work.ClassFieldTower
