import Mathlib
import Submission.Work.ORReductions.SubgroupAlg

namespace Work.ORReductions.SubgroupAlg

theorem subgroupAlgMap_mem_range_iff {G : Type*} [Group G] (H : Subgroup G) (K : Type*)
    [Semiring K] (x : MonoidAlgebra K G) :
    x ∈ Set.range (Work.ORReductions.subgroupAlgMap H K) ↔ ↑x.coeff.support ⊆ (H : Set G) := by
  constructor
  · rintro ⟨y, rfl⟩
    intro g hg
    simp only [Finset.mem_coe] at hg
    rw [Finsupp.mem_support_iff] at hg
    have hy : (Work.ORReductions.subgroupAlgMap H K y).coeff
        = Finsupp.mapDomain (⇑H.subtype) y.coeff := MonoidAlgebra.coeff_mapDomain _ _
    rw [hy] at hg
    have := Finsupp.mem_range_of_mapDomain_ne_zero hg
    rwa [show Set.range (⇑H.subtype) = (H : Set G) from Subtype.range_coe] at this
  · intro hx
    refine ⟨MonoidAlgebra.comapDomain (⇑H.subtype) H.subtype_injective x, ?_⟩
    show MonoidAlgebra.mapDomain (⇑H.subtype)
      (MonoidAlgebra.comapDomain (⇑H.subtype) H.subtype_injective x) = x
    apply MonoidAlgebra.mapDomain_comapDomain
    rwa [show Set.range (⇑H.subtype) = (H : Set G) from Subtype.range_coe]

end Work.ORReductions.SubgroupAlg
