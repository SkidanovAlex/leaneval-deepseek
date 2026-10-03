import Mathlib
import Submission.Work.ORReductions.Coherent.SubgroupRestriction
import Submission.Work.ORReductions.SubgroupAlg
import Submission.Work.ORReductions.SubgroupAlg.ker_le_span_of_subgroup

namespace Work.ORReductions.Coherent

open MonoidAlgebra

/-- `restrictToSubgroup` is a retraction of the canonical inclusion `subgroupAlgMap`. -/
theorem restrictToSubgroup_subgroupAlgMap {G : Type*} [Group G] (H : Subgroup G) (K : Type*)
    [Semiring K] (t : MonoidAlgebra K H) :
    Work.ORReductions.Coherent.restrictToSubgroup H K
      (Work.ORReductions.subgroupAlgMap H K t) = t := by
  classical
  refine Finsupp.induction (motive := fun c : H →₀ K =>
    Work.ORReductions.Coherent.restrictToSubgroup H K
        (Work.ORReductions.subgroupAlgMap H K (MonoidAlgebra.ofCoeff c)) =
      MonoidAlgebra.ofCoeff c) t.coeff ?_ ?_
  · simp
  · intro h e f _ _ ih
    have h1 : MonoidAlgebra.ofCoeff (Finsupp.single h e + f) =
        MonoidAlgebra.single h e + MonoidAlgebra.ofCoeff f := by
      rw [MonoidAlgebra.ofCoeff_add, MonoidAlgebra.ofCoeff_single]
    have h2 : Work.ORReductions.subgroupAlgMap H K (MonoidAlgebra.single h e) =
        MonoidAlgebra.single (h : G) e :=
      Work.ORReductions.SubgroupAlg.subgroupAlgMap_single H K h e
    have h3 : Work.ORReductions.Coherent.restrictToSubgroup H K
        (MonoidAlgebra.single (h : G) e) = MonoidAlgebra.single h e := by
      rw [Work.ORReductions.Coherent.restrictToSubgroup_single_of_mem H K (h : G) e h.2]
    rw [h1, map_add, map_add, h2, ih, h3]

end Work.ORReductions.Coherent
