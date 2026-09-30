import Mathlib
import Submission.Work.BW.sieg2KernelDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

theorem cardIndexEqFinrank {F : Type*} [Field F] [NumberField F] :
    Fintype.card (NumberField.mixedEmbedding.index F) = Module.finrank ℚ F := by
  rw [← NumberField.InfinitePlace.card_add_two_mul_card_eq_rank F]
  simp [NumberField.mixedEmbedding.index, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin,
    NumberField.InfinitePlace.nrRealPlaces, NumberField.InfinitePlace.nrComplexPlaces,
    Nat.mul_comm]

end Work.BW
