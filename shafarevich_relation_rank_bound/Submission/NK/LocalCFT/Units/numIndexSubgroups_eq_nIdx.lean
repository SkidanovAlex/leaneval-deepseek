import Mathlib
import Submission.NK.LocalAnabelian.Basic
import Submission.NK.LocalCFT.Units.EllRank.Defs

namespace NK.LocalCFT.Units

/-- Counting subgroups of index `n` is the same in multiplicative and in additive
notation: the order isomorphism `Subgroup A ≃o AddSubgroup (Additive A)` preserves
indices (`Subgroup.index_toAddSubgroup`), so it restricts to an equivalence of the
types of index-`n` subgroups. -/
theorem numIndexSubgroups_eq_nIdx (n : ℕ) (A : Type*) [CommGroup A] :
    NK.LocalAnabelian.numIndexSubgroups n A = NK.LocalCFT.Units.EllRank.nIdx n (Additive A) := by
  unfold NK.LocalAnabelian.numIndexSubgroups NK.LocalCFT.Units.EllRank.nIdx
  refine Nat.card_congr (Equiv.subtypeEquiv Subgroup.toAddSubgroup.toEquiv ?_)
  intro H
  rw [show (Subgroup.toAddSubgroup.toEquiv H).index = H.index from Subgroup.index_toAddSubgroup]

end NK.LocalCFT.Units
