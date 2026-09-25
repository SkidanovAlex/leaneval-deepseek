import Mathlib
import Submission.Work.ClassFieldTower.Defs

/-!
# `unitTwoRank` equals the number of infinite places

`unitTwoRank F = NumberField.Units.rank F + 1` is the `𝔽₂`-dimension of
`O_F^× / (O_F^×)²`, namely `r₁ + r₂` (`r₁` = number of real places, `r₂` = number
of complex places).  Since Mathlib defines the unit rank as
`NumberField.Units.rank F = Fintype.card (InfinitePlace F) - 1` and a number field
has at least one infinite place, we get
`unitTwoRank F = (card - 1) + 1 = card`.
-/

open NumberField

namespace Work.ClassFieldTower

/-- **`unitTwoRank F = #(InfinitePlace F)`.**

`unitTwoRank F` is defined as `NumberField.Units.rank F + 1` and Mathlib's unit
rank is `card (InfinitePlace F) - 1`; a number field has at least one infinite
place (via any complex embedding), so the subtraction is harmless. -/
theorem unitTwoRank_eq_card_infinitePlace (F : Type*) [Field F] [NumberField F] :
    unitTwoRank F = Fintype.card (NumberField.InfinitePlace F) := by
  have hpos : 0 < Fintype.card (NumberField.InfinitePlace F) :=
    Fintype.card_pos_iff.mpr inferInstance
  rw [unitTwoRank, NumberField.Units.rank]
  exact Nat.sub_add_cancel hpos

end Work.ClassFieldTower
