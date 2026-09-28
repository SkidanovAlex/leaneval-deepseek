import Mathlib
import Submission.Work.HP.Defs

/-!
# The rank of a sublattice of `ℤ^ι` (`Work.HP.rk_le_card`)

The rank `rk L = finrank ℤ L` of a `ℤ`-sublattice `L ⊆ ℤ^ι` is at most `Fintype.card ι`.
Used to bound the number of terms of the Schmidt/Schanuel upper-bound sums by a constant
depending only on the ambient type `ι`.
-/

set_option autoImplicit false

noncomputable section

namespace Work.HP

variable {ι : Type*} [Fintype ι]

/-- The rank of a sublattice of `ℤ^ι` is at most the number of coordinates. -/
lemma rk_le_card (L : Submodule ℤ (ι → ℤ)) : rk L ≤ Fintype.card ι := by
  rw [rk]
  calc Module.finrank ℤ L ≤ Module.finrank ℤ (ι → ℤ) := Submodule.finrank_le L
    _ = Fintype.card ι := Module.finrank_eq_card_basis (Pi.basisFun ℤ ι)

end Work.HP
