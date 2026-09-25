import Mathlib
import Submission.Work.ClassFieldTower.Defs
import Submission.Work.ClassFieldTower.two_pow_classGroupTwoRank
import Submission.Work.ClassFieldTower.card_quotient_squareSubgroup_eq_card_twoTorsion
import Submission.Work.ClassFieldTower.unitTwoRank_eq_card_infinitePlace
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import Mathlib.NumberTheory.NumberField.ClassNumber

/-!
# `Work.ClassFieldTower.Invariants` -- values and bounds for the two invariants

* `unitTwoRank_eq_nrRealPlaces_add_nrComplexPlaces` : `d₂(O_F^×) = r₁ + r₂`;
* `unitTwoRank_rat` : `d₂(O_ℚ^×) = 1`;
* `classGroupTwoRank_le_log_classNumber` : `rank₂ Cl(F) ≤ log₂ h_F` (the `2`-rank is bounded by
  the logarithm of the class number -- the only "computable" upper bound).
-/

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open scoped Classical
open scoped NumberField
open NumberField

noncomputable section

namespace Work.ClassFieldTower

/-- **`d₂(O_F^×) = r₁ + r₂`**, the number of archimedean places. -/
theorem unitTwoRank_eq_nrRealPlaces_add_nrComplexPlaces (F : Type*) [Field F] [NumberField F] :
    unitTwoRank F = NumberField.InfinitePlace.nrRealPlaces F +
      NumberField.InfinitePlace.nrComplexPlaces F := by
  rw [unitTwoRank_eq_card_infinitePlace F,
    InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces]

/-- **`d₂(O_ℚ^×) = 1`**: `O_ℚ^× = {±1}` and `±1 mod squares` has rank `1`. -/
theorem unitTwoRank_rat : unitTwoRank ℚ = 1 := by
  rw [unitTwoRank_eq_card_infinitePlace ℚ]
  haveI : Unique (NumberField.InfinitePlace ℚ) := inferInstance
  simp

/-- **`rank₂ Cl(F) ≤ log₂ h_F`.**  The `2`-rank of the class group is bounded by the base-`2`
logarithm of the class number. -/
theorem classGroupTwoRank_le_log_classNumber (F : Type*) [Field F] [NumberField F] :
    classGroupTwoRank F ≤ Nat.log 2 (NumberField.classNumber F) := by
  rw [classGroupTwoRank, NumberField.classNumber, ← Nat.card_eq_fintype_card]
  exact Nat.log_mono_right (Nat.card_le_card_of_surjective _
    (QuotientGroup.mk'_surjective (Subgroup.closure
      (Set.range (fun x : ClassGroup (𝓞 F) => x ^ 2)))))

/-- **`rank₂ Cl(F) = log₂ #Cl(F)[2]`.**  The `2`-rank of the class group is the base-`2`
logarithm of the number of `2`-torsion classes -- the form in which genus theory is usually
proved (exhibit `2^k` distinct `2`-torsion classes, conclude `rank ≥ k`). -/
theorem classGroupTwoRank_eq_log_card_twoTorsion (F : Type*) [Field F] [NumberField F] :
    classGroupTwoRank F = Nat.log 2 (Nat.card {x : ClassGroup (𝓞 F) // x ^ 2 = 1}) := by
  rw [classGroupTwoRank, card_quotient_squareSubgroup_eq_card_twoTorsion]

/-- **`rank₂ Cl(F) ≥ 5` from 32 distinct `2`-torsion classes.** -/
theorem card_twoTorsion_ge_of_classGroupTwoRank_ge {F : Type*} [Field F] [NumberField F]
    (h : 5 ≤ classGroupTwoRank F) :
    2 ^ 5 ≤ Nat.card {x : ClassGroup (𝓞 F) // x ^ 2 = 1} := by
  calc 2 ^ 5 ≤ 2 ^ classGroupTwoRank F := Nat.pow_le_pow_right (by norm_num) h
    _ = Nat.card {x : ClassGroup (𝓞 F) // x ^ 2 = 1} := by
      rw [two_pow_classGroupTwoRank F, card_quotient_squareSubgroup_eq_card_twoTorsion]

end Work.ClassFieldTower
