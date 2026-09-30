import Mathlib
import Submission.Work.CurveBasics.All

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false

universe u

namespace Work.Charts

/-- The complement of a nonempty open subset of a curve contains only finitely many closed
points: the complement is a proper closed subset of a one-dimensional Noetherian integral
scheme, hence avoids the generic point, and the finitely many points missing from a nonempty
open are precisely the closed points of that complement. -/
theorem finite_places_notMem_of_ne_bot {k : Type u} [Field k] (C : Work.CurveBasics.Curve k)
    (U : C.left.Opens) (hU : U ≠ ⊥) :
    {P : C.Place | P.point ∉ U}.Finite := by
  classical
  have hUne : (U : Set C.left).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro hemp
    exact hU (TopologicalSpace.Opens.ext (by simp [hemp]))
  have hgenU : genericPoint C.left ∈ (U : Set C.left) :=
    Specializes.mem_open ((genericPoint_spec C.left).specializes (Set.mem_univ _))
      U.isOpen hUne.some_mem
  have hcl : IsClosed (((U : Set C.left))ᶜ) := U.isOpen.isClosed_compl
  have hgen : genericPoint C.left ∉ ((U : Set C.left))ᶜ := by
    rw [Set.notMem_compl_iff]
    exact hgenU
  have hfin : (((U : Set C.left))ᶜ).Finite :=
    Work.CurveBasics.Order.finite_of_isClosed_of_genericPoint_notMem _
      hcl hgen (fun z => C.coheight_le_one z)
  refine Set.Finite.of_finite_image (hfin.subset ?_) (fun P _ P' _ h => Subtype.ext h)
  rintro z ⟨P, hP, rfl⟩
  exact Set.mem_compl fun hmem => hP hmem

end Work.Charts
