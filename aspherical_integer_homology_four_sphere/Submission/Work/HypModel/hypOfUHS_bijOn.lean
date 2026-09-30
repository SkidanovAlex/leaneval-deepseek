import Mathlib
import Submission.Work.HypModel.Basic
import Submission.Work.HypModel.lorentz_hypOfUHS_self
import Submission.Work.HypModel.hypOfUHS_four_pos
import Submission.Work.HypModel.hypOfUHS_injOn
import Submission.Work.HypModel.hypOfUHS_uhsOfHyp
import Submission.Work.HypModel.uhsOfHyp_three_pos

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.HypModel

/-- **The upper half space chart of hyperbolic 4-space is a bijection onto the upper sheet of the
hyperboloid.**  The three components of `Set.BijOn` are:

* `Set.MapsTo`: for `q ∈ upperHalfSpace`, i.e. `0 < q 3`, the lifted point `hypOfUHS q` lies on the
  hyperboloid (`lorentz_hypOfUHS_self`, using `q 3 ≠ 0`) and has positive last coordinate
  (`hypOfUHS_four_pos`);
* `Set.InjOn`: `hypOfUHS_injOn`, following from the fact that the difference of the last two
  coordinates of the image is the reciprocal `(q 3)⁻¹` of the height;
* `Set.SurjOn`: a point `P ∈ upperSheet` is the image of its upper half space position
  `q := uhsOfHyp P`, which lies in the upper half space (`uhsOfHyp_three_pos`) and satisfies
  `hypOfUHS (uhsOfHyp P) = P` (`hypOfUHS_uhsOfHyp`). -/
theorem hypOfUHS_bijOn : Set.BijOn hypOfUHS upperHalfSpace upperSheet := by
  refine ⟨fun q hq => ?_, hypOfUHS_injOn, fun P hP => ?_⟩
  · exact ⟨lorentz_hypOfUHS_self (ne_of_gt hq), hypOfUHS_four_pos hq⟩
  · exact ⟨uhsOfHyp P, uhsOfHyp_three_pos hP, hypOfUHS_uhsOfHyp hP⟩

end Work.HypModel
