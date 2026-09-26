import Submission.Work.CoreTopology.IntersectionNumber
import Submission.Work.CoreTopology.compressing_winding_dichotomy
import Submission.Work.CoreTopology.min_le_encard_inter_standardCurve

/-!
# Pardon's invariant for the standard torus: `I(F, β) = min p q`

This file assembles the two geometric ingredients proved in the sibling files

* `Work.CoreTopology.compressing_winding_dichotomy` — every essential loop of the standard
  torus bounding a disc in the complement of the torus has winding vector `(a, 0)` or
  `(0, b)` (it is homotopic in the torus to a multiple of the meridian or of the longitude);
* `Work.CoreTopology.min_le_encard_inter_standardCurve` — such a curve meets the standard
  `(p,q)`-curve (for `p, q > 0` coprime) in at least `min p q` points,

to obtain Pardon's computation `I(F, β) = min p q` for the standard torus of revolution and
the standard `(p,q)`-curve.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.CoreTopology

noncomputable section

/-- The classification of compressing loops, packaged as the predicate
`CompressingLoopsAreMeridianOrLongitude`. -/
theorem compressingLoopsAreMeridianOrLongitude_holds :
    CompressingLoopsAreMeridianOrLongitude :=
  fun α hess hb => compressing_winding_dichotomy α hess hb

/-- The intersection lower bound, packaged as the predicate `IntersectionLowerBound p q`. -/
theorem intersectionLowerBound_holds (p q : ℕ) (hp : 0 < p) (hq : 0 < q)
    (hc : Nat.Coprime p q) : IntersectionLowerBound p q := by
  intro α hsimple hess hdich
  obtain ⟨L, hw⟩ := hess
  rcases hdich with h | h
  · exact min_le_encard_inter_standardCurve p q hp hq hc α hsimple L hw (Or.inr (h L))
  · exact min_le_encard_inter_standardCurve p q hp hq hc α hsimple L hw (Or.inl (h L))

/-- The geometric input `CompressingLoopsMeetOften p q` for the standard torus and the
standard `(p,q)`-curve. -/
theorem compressingLoopsMeetOften_holds (p q : ℕ) (hp : 0 < p) (hq : 0 < q)
    (hc : Nat.Coprime p q) : CompressingLoopsMeetOften p q :=
  compressingLoopsMeetOften_of p q compressingLoopsAreMeridianOrLongitude_holds
    (intersectionLowerBound_holds p q hp hq hc)

/-- **Pardon's invariant for the standard torus and the standard `(p,q)`-curve.**

For the standard torus of revolution (major radius `2`, minor radius `1`) and the standard
`(p,q)`-curve `β` with `p, q > 0` coprime, `I(F, β) = min p q`: the meridian and longitude
circles bound discs in the complement of the torus and meet `β` in `p` resp. `q` points, and
conversely every simple compressing loop of `F` is homotopic to a multiple of the meridian or
of the longitude and therefore meets `β` at least `min p q` times. -/
theorem pardonsI_standard (p q : ℕ) (hp : 0 < p) (hq : 0 < q) (hc : Nat.Coprime p q) :
    pardonsI standard (standardCurve p q) = (Nat.min p q : ℕ∞) :=
  pardonsI_standard_of_input p q hp hq hc (compressingLoopsMeetOften_holds p q hp hq hc)

end

end Work.CoreTopology
