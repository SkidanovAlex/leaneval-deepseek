import Mathlib
import Submission.Work.SpecLin.Points.Setup

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false

namespace Work.SpecLin.Points

universe u

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

variable {K : Type u} [Field K] {C : Work.CurveBasics.Curve K} {F : Type u} [Field F]
  [Algebra K F]

/-- `ptLeft p` is a section of the structure morphism `C_F ⟶ Spec F` of the base change. -/
theorem ptLeft_comp_hom (p : Work.SpecLin.CurveFPt C F) :
    Work.SpecLin.ptLeft p ≫ (C.baseChange F).hom = 𝟙 (Spec (CommRingCat.of F)) := by
  rw [Work.CurveBasics.Curve.baseChange_hom]
  simp only [Work.CurveBasics.Curve.baseChangeHom, Work.CurveBasics.Curve.baseChangeOver,
    Over.pullback_obj_hom]
  rw [show Work.SpecLin.ptLeft p = pullback.lift p.left (𝟙 (Spec (CommRingCat.of F))) _ from rfl]
  rw [pullback.lift_snd]

/-- `ptLeft p` is a closed immersion, being a section of the separated morphism
`(C.baseChange F).hom`. -/
theorem isClosedImmersion_ptLeft (p : Work.SpecLin.CurveFPt C F) :
    IsClosedImmersion (Work.SpecLin.ptLeft p) := by
  have hci : IsClosedImmersion (Work.SpecLin.ptLeft p ≫ (C.baseChange F).hom) := by
    rw [ptLeft_comp_hom]; infer_instance
  have hsep : IsSeparated (C.baseChange F).hom := inferInstance
  exact IsClosedImmersion.of_comp (Work.SpecLin.ptLeft p) (C.baseChange F).hom

/-- The range of `ptLeft p` is the singleton `{ptToPoint p}`: `Spec F` has a single point. -/
theorem range_ptLeft (p : Work.SpecLin.CurveFPt C F) :
    Set.range ⇑(Work.SpecLin.ptLeft p) = {Work.SpecLin.ptToPoint p} := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    simp only [Set.mem_singleton_iff]
    unfold Work.SpecLin.ptToPoint
    congr 1
    exact Subsingleton.elim _ _
  · rintro rfl
    exact ⟨IsLocalRing.closedPoint F, rfl⟩

/-- An `F`-point of the curve `C` (a morphism `Spec F ⟶ C` over `Spec K`) induces a point of
the base-changed curve `C_F = C ×_K Spec F`; that point is *closed*, hence a place of `C_F`
and the source of the "point divisor" `ptDiv` used to state specialisation of linear
equivalence (`Work.SpecLin.linEquiv_of_sections`, `Work.SpecLin.specLin`).

Suggested route: `ptLeft p` (see `Submission/Work/SpecLin/Points/Setup.lean`) is a section of
the separated morphism `(C.baseChange F).hom`, hence a closed immersion (Mathlib has the
anonymous instance in `AlgebraicGeometry/Morphisms/Separated.lean`: a section of a separated
morphism is a closed immersion), so its range is closed; `Spec F` has a single point
(`IsLocalRing.closedPoint F` is the unique point of `Spec F`), so the range is
`{Work.SpecLin.ptToPoint p}`. -/
theorem ptToPoint_isClosed {K : Type u} [Field K] {C : Work.CurveBasics.Curve K}
    {F : Type u} [Field F] [Algebra K F] (p : Work.SpecLin.CurveFPt C F) :
    IsClosed {Work.SpecLin.ptToPoint p} := by
  rw [← range_ptLeft p]
  have hci : IsClosedImmersion (Work.SpecLin.ptLeft p) := isClosedImmersion_ptLeft p
  exact (Scheme.Hom.isClosedEmbedding (Work.SpecLin.ptLeft p)).isClosed_range

end Work.SpecLin.Points
