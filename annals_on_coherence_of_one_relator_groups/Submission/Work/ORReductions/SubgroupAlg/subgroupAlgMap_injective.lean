import Mathlib
import Submission.Work.ORReductions.SubgroupAlg

namespace Work.ORReductions.SubgroupAlg

theorem subgroupAlgMap_injective {G : Type*} [Group G] (H : Subgroup G) (K : Type*) [Semiring K] :
    Function.Injective (Work.ORReductions.subgroupAlgMap H K) := by
  show Function.Injective (MonoidAlgebra.mapDomain (R := K) H.subtype)
  exact MonoidAlgebra.mapDomain_injective H.subtype_injective

end Work.ORReductions.SubgroupAlg
