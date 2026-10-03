import Mathlib
import Submission.Work.ORLocInd.Basic

namespace Work.ORLocInd.TF

/-- A finite torsion-free group is trivial: in a finite group every element has finite order, so
torsion-freeness forces every element to be the identity. -/
theorem isTorsionFree_subsingleton_of_finite {G : Type*} [Group G] [Finite G]
    (h : Work.ORLocInd.IsTorsionFree G) : Subsingleton G :=
  Subsingleton.intro fun a b => by
    rw [h a (isOfFinOrder_of_finite a), h b (isOfFinOrder_of_finite b)]

end Work.ORLocInd.TF
