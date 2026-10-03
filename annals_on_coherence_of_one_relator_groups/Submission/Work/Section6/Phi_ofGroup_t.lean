import Mathlib
import Submission.Work.ORHughesFree.Section6.RatStruct
import Submission.Work.ORHughesFree.Section6.UnitOf
import Submission.Work.ORHughesFree.SkewLaurentSeries
import Submission.Work.ORHughesFree.SkewLaurentSeriesInstances

namespace Work.Section6

theorem Phi_ofGroup_t {K : Type} [Field K] {H : Type} [Group H] {P : Type} [Ring P]
    {DN : Subring P} [MulSemiringAction (Multiplicative ℤ) ↥DN]
    (φP : MonoidAlgebra K H →+* P) (t : H)
    (laurentEmbed : Work.ORHughesFree.SkewLaurentSeries ↥DN →+* P)
    (ht : φP (MonoidAlgebra.single t (1 : K)) =
      laurentEmbed (Work.ORHughesFree.skewLaurentSeriesT ↥DN :
        Work.ORHughesFree.SkewLaurentSeries ↥DN)) :
    ((Work.ORHughesFree.divisionClosure (Set.range φP)).subtype.comp
      (Work.ORHughesFree.Phi φP)) (Work.ORHughesFree.RatU.ofGroup ((1 : Kˣ), t)) =
      laurentEmbed (Work.ORHughesFree.skewLaurentSeriesT ↥DN :
        Work.ORHughesFree.SkewLaurentSeries ↥DN) := by
  -- `Φ` sends the group-like unit `(1, t)` to `φP (unitOf (1, t)) = φP (single t 1)`.
  rw [RingHom.comp_apply, Work.ORHughesFree.Phi_ofGroup]
  simp only [Work.ORHughesFree.imElem, Work.ORHughesFree.unitOf]
  simpa using ht

end Work.Section6
