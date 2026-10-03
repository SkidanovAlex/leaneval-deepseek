import Mathlib
import Submission.Work.ORLocInd.Basic

namespace Work.ORLocInd.TF

/-- A subgroup of a torsion-free group is torsion-free: an element of the subgroup that has finite
order in the subgroup has the same order in the ambient group (`Subgroup.orderOf_coe`), hence is
trivial there. -/
theorem isTorsionFree_subgroup {G : Type*} [Group G] (h : Work.ORLocInd.IsTorsionFree G)
    (H : Subgroup G) : Work.ORLocInd.IsTorsionFree H := by
  intro x hx
  apply Subtype.ext
  apply h
  rw [← orderOf_pos_iff, Subgroup.orderOf_coe]
  exact hx.orderOf_pos

end Work.ORLocInd.TF
