import Mathlib
import Submission.Work.BcDiv.Points
import Submission.Work.Universal.Basic
import Submission.Work.JacFinal.Basic
import Submission.Work.Charts.Step3Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.



open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

universe u

namespace Work.JacClose

/-- **The base point of `C_{k'}` pulls back to the base point of `C`.**

For `K → L → F`, the `F`-point `P0Pt (C_L) (bcPt C P0 L) F` of the base change `C_L`
supported at the base point `bcPt C P0 L` pushes forward, along the projection `C_L ⟶ C`, to
the `F`-point `P0Pt C P0 F` of `C` supported at `P0`.

The proof computes both sides as morphisms of schemes.  Writing
`bcPt C P0 L = (preservesTerminalIso (bcFun K L)).inv ≫ (bcFun K L).map P0`, and using
* `Over.w` for the underlying morphism of `toUnit`,
* the naturality `Work.Descent.baseChange_map_fst' P0` of the base-change projection,
* `Over.w` for the terminal comparison (whose underlying morphism followed by the projection
  `bcπ` on the terminal is the structure morphism `Spec L ⟶ Spec K`),
* `Spec.map_comp`, `CommRingCat.ofHom_comp` and `IsScalarTower.algebraMap_eq K L F`,
both sides reduce to `Spec.map (algebraMap K F) ≫ P0.left`. -/
theorem bcPtK_P0Pt {K : Type u} [Field K] {C : Work.CurveBasics.Curve K}
    {L : Type u} [Field L] [Algebra K L]
    {F : Type u} [Field F] [Algebra L F] [Algebra K F] [IsScalarTower K L F]
    (P0 : Work.Charts.unitSch K ⟶ C.toOver) :
    Work.BcDiv.bcPtK (Work.Universal.P0Pt (C.baseChange L) (Work.JacFinal.bcPt C P0 L) F)
      = Work.Universal.P0Pt C P0 F := by
  -- The underlying morphism of `bcPt C P0 L`, split over the base-change functor.
  have h1 : Over.Hom.left (Work.JacFinal.bcPt C P0 L)
      = Over.Hom.left ((CartesianMonoidalCategory.preservesTerminalIso (Work.DescentGeom.bcFun K L)).inv)
        ≫ Over.Hom.left ((Work.DescentGeom.bcFun K L).map P0) := by
    rw [Work.JacFinal.bcPt, Over.comp_left]
  -- The terminal comparison followed by the projection `bcπ` on the terminal is `Spec L ⟶ Spec K`.
  have hB : Over.Hom.left (CartesianMonoidalCategory.preservesTerminalIso
        (Work.DescentGeom.bcFun K L)).inv
      ≫ Work.Descent.baseChangeπ (Work.Charts.unitSch K)
      = Work.Descent.specMap K L := by
    have hw := Over.w ((CartesianMonoidalCategory.preservesTerminalIso
      (Work.DescentGeom.bcFun K L)).inv)
    simp only [Work.DescentGeom.bcFun, Work.Descent.baseChangeFunctor,
      Work.Descent.baseChangeπ, Over.pullback_obj_hom] at hw ⊢
    have hcond : pullback.fst (Over.hom (Work.Charts.unitSch K)) (Work.Descent.specMap K L)
        = pullback.snd (Over.hom (Work.Charts.unitSch K)) (Work.Descent.specMap K L)
            ≫ Work.Descent.specMap K L := by
      rw [← Category.comp_id (pullback.fst _ _), ← pullback.condition]
      rfl
    rw [hcond, ← Category.assoc, hw]
    simp
  -- The underlying morphism of `toUnit (specOf K F)` is the structure morphism `Spec F ⟶ Spec K`.
  have hA : Over.Hom.left (Work.GroupChunk.toUnit (Work.GCBasics.specOf L F))
      = Spec.map (CommRingCat.ofHom (algebraMap L F)) := by
    simpa using Over.w (Work.GroupChunk.toUnit (Work.GCBasics.specOf L F))
  have hA' : Over.Hom.left (Work.GroupChunk.toUnit (Work.GCBasics.specOf K F))
      = Spec.map (CommRingCat.ofHom (algebraMap K F)) := by
    simpa using Over.w (Work.GroupChunk.toUnit (Work.GCBasics.specOf K F))
  -- Naturality of the base-change projection along `P0`.
  have hnat : Over.Hom.left ((Work.DescentGeom.bcFun K L).map P0)
      ≫ Work.Descent.baseChangeπ C.toOver
      = Work.DescentGeom.bcπ L (Work.Charts.unitSch K) ≫ Over.Hom.left P0 :=
    Work.Descent.baseChange_map_fst' P0
  -- Combining the two: `bcPt C P0 L` followed by the projection to `C`.
  have hstep : Over.Hom.left (Work.JacFinal.bcPt C P0 L) ≫ Work.Descent.baseChangeπ C.toOver
      = Over.Hom.left ((CartesianMonoidalCategory.preservesTerminalIso (Work.DescentGeom.bcFun K L)).inv)
        ≫ (Work.DescentGeom.bcπ L (Work.Charts.unitSch K) ≫ Over.Hom.left P0) := by
    erw [h1]
    simp only [Category.assoc]
    rw [hnat]
  apply Over.OverMorphism.ext
  rw [Work.BcDiv.bcPtK_left]
  rw [show (C.bcSquare L).π = Work.Descent.baseChangeπ C.toOver from rfl]
  simp only [Work.Universal.P0Pt]
  rw [Over.comp_left]
  simp only [Category.assoc]
  erw [hstep]
  rw [hA]
  rw [Over.comp_left, hA']
  rw [← Category.assoc (f := Over.Hom.left (CartesianMonoidalCategory.preservesTerminalIso
        (Work.DescentGeom.bcFun K L)).inv)
      (g := Work.DescentGeom.bcπ L (Work.Charts.unitSch K))
      (h := Over.Hom.left P0), hB]
  -- `Spec.map (algebraMap L F) ≫ Spec.map (algebraMap K L) = Spec.map (algebraMap K F)`.
  have hfin : Spec.map (CommRingCat.ofHom (algebraMap L F)) ≫ Work.Descent.specMap K L
      = Spec.map (CommRingCat.ofHom (algebraMap K F)) := by
    rw [Work.Descent.specMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← IsScalarTower.algebraMap_eq K L F]
  rw [← Category.assoc (f := Spec.map (CommRingCat.ofHom (algebraMap L F)))
      (g := Work.Descent.specMap K L) (h := Over.Hom.left P0), hfin]

end Work.JacClose
