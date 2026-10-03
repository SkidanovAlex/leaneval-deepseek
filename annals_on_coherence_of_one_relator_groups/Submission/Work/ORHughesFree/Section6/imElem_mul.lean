import Mathlib
import Submission.Work.ORHughesFree.Section6.ClosureBasic

namespace Work.ORHughesFree.Section6

theorem imElem_mul {K : Type} [Field K] {G : Type} [Group G] {U : Type} [Ring U]
    (φ : MonoidAlgebra K G →+* U) (u v : Kˣ × G) :
    Work.ORHughesFree.imElem φ (u * v) =
      Work.ORHughesFree.imElem φ u * Work.ORHughesFree.imElem φ v := by
  apply Subtype.ext
  simp only [Work.ORHughesFree.imElem, Subring.coe_mul]
  rw [Work.ORHughesFree.unitOf_mul, map_mul]

end Work.ORHughesFree.Section6
