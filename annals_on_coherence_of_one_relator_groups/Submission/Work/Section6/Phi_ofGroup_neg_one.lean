import Mathlib
import Submission.Work.ORHughesFree.Section6.RatStruct
import Submission.Work.ORHughesFree.Section6.UnitOf
import Submission.Work.ORHughesFree.Rat.OfGroup

namespace Work.Section6

/-- The group-like unit `(-1, 1) : Kˣ × H` of `K[H]` is `-1`: indeed
`unitOf (-1, 1) = single 1 (-1) = -1`. -/
theorem unitOf_neg_one {K : Type} [Field K] {H : Type} [Group H] :
    Work.ORHughesFree.unitOf ((-1 : Kˣ), (1 : H)) = -1 := by
  rw [Work.ORHughesFree.unitOf]
  simp [MonoidAlgebra.one_def]

/-- The element `(-1, 1) : Kˣ × H` is sent to `-1` by `Φ` followed by the inclusion of the
division closure into `U`.

Indeed `Φ φ (ofGroup u) = imElem φ u` has underlying element `φ (unitOf u)`
(`Work.ORHughesFree.Phi_ofGroup`, `Work.ORHughesFree.imElem`), and for `u = (-1, 1)` we have
`unitOf u = -1` in `K[H]`, whence `φ (unitOf u) = -1` in `U`. -/
theorem Phi_ofGroup_neg_one {K : Type} [Field K] {H : Type} [Group H] {U : Type} [Ring U]
    (φ : MonoidAlgebra K H →+* U) :
    ∃ u : Kˣ × H,
      ((Work.ORHughesFree.divisionClosure (Set.range φ)).subtype.comp
        (Work.ORHughesFree.Phi φ)) (Work.ORHughesFree.RatU.ofGroup u) = -1 := by
  refine ⟨((-1 : Kˣ), (1 : H)), ?_⟩
  rw [RingHom.comp_apply, Work.ORHughesFree.Phi_ofGroup]
  show φ (MonoidAlgebra.single (1 : H) (-1 : K)) = -1
  rw [show MonoidAlgebra.single (1 : H) (-1 : K) = -1 by
        simp [MonoidAlgebra.one_def],
    map_neg, map_one]

end Work.Section6
