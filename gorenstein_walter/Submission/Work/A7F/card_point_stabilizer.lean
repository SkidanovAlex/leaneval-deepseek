import Mathlib
import Submission.Work.A7F.Defs

namespace Work.A7F

open scoped MatrixGroups

/-- The cardinality of the alternating group on seven letters. -/
theorem nat_card_alternatingGroup_fin_seven : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
  simp only [nat_card_alternatingGroup, Nat.card_fin]
  norm_num

/-- `A₇` acts transitively on the seven points. -/
theorem isPretransitive_alternatingGroup_fin_seven :
    MulAction.IsPretransitive (alternatingGroup (Fin 7)) (Fin 7) :=
  alternatingGroup.isPretransitive_of_three_le_card (Fin 7) (by norm_num)

/-- The stabilizer of a point in `A₇` has order `360` (it is `A₆`).
Proved by the orbit-stabilizer theorem: the action is transitive on the `7` points, so the
stabilizer has index `7` in `A₇`, whence its order is `2520 / 7 = 360`. -/
theorem card_point_stabilizer (p : Fin 7) :
    Nat.card (MulAction.stabilizer (alternatingGroup (Fin 7)) p) = 360 := by
  have : MulAction.IsPretransitive (alternatingGroup (Fin 7)) (Fin 7) :=
    isPretransitive_alternatingGroup_fin_seven
  have hindex : (MulAction.stabilizer (alternatingGroup (Fin 7)) p).index = 7 := by
    rw [MulAction.index_stabilizer_of_transitive]
    simp
  have h := Subgroup.card_mul_index (MulAction.stabilizer (alternatingGroup (Fin 7)) p)
  rw [hindex, nat_card_alternatingGroup_fin_seven] at h
  omega

end Work.A7F
