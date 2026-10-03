import Mathlib
import Submission.Work.ORHughesFree.Section6.RatStruct

namespace Work.Section6

theorem codRestrict_subtype_comp_Phi {K : Type} [Field K] {G : Type} [Group G] {U : Type} [Ring U]
    (φ : MonoidAlgebra K G →+* U) :
    ((Work.ORHughesFree.divisionClosure (Set.range φ)).subtype.comp
        (Work.ORHughesFree.Phi φ)).codRestrict
      (Work.ORHughesFree.divisionClosure (Set.range φ))
      (fun α => (Work.ORHughesFree.Phi φ α).2) =
      Work.ORHughesFree.Phi φ := by
  rfl

end Work.Section6
