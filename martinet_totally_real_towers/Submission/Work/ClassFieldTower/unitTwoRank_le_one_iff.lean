import Mathlib
import Submission.Work.ClassFieldTower.Defs
import Submission.Work.ClassFieldTower.Invariants

/-!
# `d₂(O_F^×) ≤ 1` if and only if `F` is `ℚ` or an imaginary quadratic field

`unitTwoRank F = NumberField.Units.rank F + 1` is the `𝔽₂`-dimension of
`O_F^× / (O_F^×)²`, equal to `r₁ + r₂` (`r₁` = number of real places,
`r₂` = number of complex places) and hence to the number of infinite places of `F`.

Since `r₁ + 2 r₂ = [F : ℚ]` and `F` always has at least one infinite place,
`r₁ + r₂ ≤ 1` forces `(r₁, r₂) = (1, 0)` or `(0, 1)`.  The first case has
`[F : ℚ] = 1`, i.e. `F = ℚ`; the second has `r₁ = 0`, so `F` is totally complex,
and `[F : ℚ] = 2 r₂ = 2`.  Conversely both `ℚ` (`r₁ = 1`, `r₂ = 0`) and an
imaginary quadratic field (`r₁ = 0`, `r₂ = 1`) have exactly one infinite place.
-/

open NumberField

namespace Work.ClassFieldTower

theorem unitTwoRank_le_one_iff (F : Type*) [Field F] [NumberField F] :
    Work.ClassFieldTower.unitTwoRank F ≤ 1 ↔
      (Module.finrank ℚ F = 1 ∨
        (NumberField.IsTotallyComplex F ∧ Module.finrank ℚ F = 2)) := by
  rw [unitTwoRank_eq_card_infinitePlace F]
  set r1 := InfinitePlace.nrRealPlaces F with hr1def
  set r2 := InfinitePlace.nrComplexPlaces F with hr2def
  have hcard : Fintype.card (NumberField.InfinitePlace F) = r1 + r2 :=
    InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces F
  have hdeg : r1 + 2 * r2 = Module.finrank ℚ F :=
    InfinitePlace.card_add_two_mul_card_eq_rank F
  have hpos : 0 < r1 + r2 := by
    rw [← hcard]
    exact Fintype.card_pos_iff.mpr inferInstance
  constructor
  · intro h
    have h1 : r1 + r2 = 1 := by omega
    rcases Nat.eq_zero_or_pos r2 with h2 | h2
    · left
      omega
    · right
      have hr1 : r1 = 0 := by omega
      have hr2 : r2 = 1 := by omega
      exact ⟨NumberField.nrRealPlaces_eq_zero_iff.mp hr1, by omega⟩
  · rintro (h | ⟨hc, h2⟩)
    · have hA := InfinitePlace.nrRealPlaces_eq_one_of_finrank_eq_one (K := F) h
      have hB := InfinitePlace.nrComplexPlaces_eq_zero_of_finrank_eq_one (K := F) h
      omega
    · have hr1 : r1 = 0 := NumberField.nrRealPlaces_eq_zero_iff.mpr hc
      omega

end Work.ClassFieldTower
