import Mathlib
import Submission.Work.ORTorsion.Defs
import Submission.Work.ORTorsion.Support.exists_mapToG_eq

namespace Work.ORTorsion.Support

open Work.ORTorsion

/-- `mapToG H` is injective, hence it preserves the cardinality of the support. -/
theorem card_support_mapToG {K : Type*} [Field K] {G : Type*} [Group G] {H : Subgroup G}
    (x : MonoidAlgebra K H) :
    (mapToG H x).coeff.support.card = x.coeff.support.card := by
  classical
  rw [coeff_mapToG,
    Finsupp.mapDomain_support_of_injective (f := ⇑H.subtype) (fun a b h => Subtype.ext h) x.coeff,
    Finset.card_image_of_injective (f := ⇑H.subtype) x.coeff.support
      (fun a b h => Subtype.ext h)]

end Work.ORTorsion.Support
