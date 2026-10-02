/-
# Jordan curves from two arcs

A set is a Jordan curve iff it is the image of an injective continuous map of the circle.  Two
injective arcs with the same endpoints which meet only in those endpoints glue to such a curve.
This is the form in which the endgame builds its curves: see `Work.Top.pinch_curve_jordan`,
whose curve `J_r` is the union of two such arcs.
-/
import Mathlib
import Submission.Work.Top.Jordan
import Submission.Work.TopJordan.CurveModel
import Submission.Commons.Topology.Jordan.exists_injective_circle_map_of_two_arcs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false

open Set

namespace Work.TopJordan

noncomputable section

/-- **Two injective arcs with the same endpoints, meeting only in those endpoints, form a Jordan
curve**: their union is the image of an injective continuous map of the circle. -/
theorem isJordanCurve_of_two_arcs (P Q : C(Set.Icc (0:ℝ) 1, ℂ))
    (hP : Function.Injective P) (hQ : Function.Injective Q)
    (hP0 : P 0 = Q 0) (hP1 : P 1 = Q 1) (hne : P 0 ≠ P 1)
    (hdisj : ∀ s t : Set.Icc (0:ℝ) 1, P s = Q t → s = 0 ∨ s = 1) :
    Work.Top.IsJordanCurve (Set.range P ∪ Set.range Q) := by
  obtain ⟨γ, hγ, hrange⟩ :=
    Commons.Topology.Jordan.exists_injective_circle_map_of_two_arcs P Q hP hQ hP0 hP1 hne hdisj
  rw [← hrange]
  exact isJordanCurve_range γ hγ

end

end Work.TopJordan
