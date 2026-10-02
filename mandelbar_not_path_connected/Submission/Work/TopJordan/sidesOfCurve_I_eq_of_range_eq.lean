import Mathlib
import Submission.Work.Top.Jordan
import Submission.Work.TopJordan.Sides
import Submission.Work.TopJordan.SidesAPI

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

/-- The bounded side of a Jordan curve depends only on the curve as a set, not on the chosen
injective parametrisation of the circle. -/
theorem sidesOfCurve_I_eq_of_range_eq {γ δ : C(Circle, ℂ)} (hγ : Function.Injective γ)
    (hδ : Function.Injective δ) (h : Set.range γ = Set.range δ) :
    (sidesOfCurve γ hγ).I = (sidesOfCurve δ hδ).I := by
  have hCγ : Work.Top.IsJordanCurve (Set.range γ) := isJordanCurve_range γ hγ
  -- Transport the sides of `δ` along `Set.range γ = Set.range δ`, field by field, so that the
  -- bounded piece is literally the same set.
  let Sδ : Work.Top.Sides (Set.range γ) :=
    { I := (sidesOfCurve δ hδ).I
      O := (sidesOfCurve δ hδ).O
      isOpen_I := (sidesOfCurve δ hδ).isOpen_I
      isOpen_O := (sidesOfCurve δ hδ).isOpen_O
      union_eq := by rw [h]; exact (sidesOfCurve δ hδ).union_eq
      disjoint := (sidesOfCurve δ hδ).disjoint
      preconnected_I := (sidesOfCurve δ hδ).preconnected_I
      preconnected_O := (sidesOfCurve δ hδ).preconnected_O
      bounded_I := (sidesOfCurve δ hδ).bounded_I
      unbounded_O := (sidesOfCurve δ hδ).unbounded_O
      frontier_I := by rw [h]; exact (sidesOfCurve δ hδ).frontier_I
      frontier_O := by rw [h]; exact (sidesOfCurve δ hδ).frontier_O }
  -- The two sides of a Jordan curve are unique, so the bounded pieces agree.
  exact (sides_ext hCγ (S := sidesOfCurve γ hγ) (S' := Sδ)).1

end

end Work.TopJordan
