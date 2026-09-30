import Mathlib
import Submission.Work.BcDiv.SymPts

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


namespace Work.BcDiv

open Work.CurveBasics CategoryTheory Limits AlgebraicGeometry

universe u

/-- **B5, naturality of `ptsK` in the field.** For `e : F →ₐ[L] F'` (with `F'` also a
`K`-algebra, compatibly), the point-level comparison `Work.BcDiv.ptsK n` commutes with the base
change of points: `ptsK (RPt.map e p) = RPt.map (e.restrictScalars K) (ptsK p)`.

Suggested proof: `Over.OverMorphism.ext` reduces to the underlying scheme morphisms, where both
sides are literally `Spec.map (ofHom e.toRingHom) ≫ p.left ≫ βK` (`AlgHom.coe_restrictScalars` is
`rfl`); `simp only [RPt.map, ptsK_left, Over.comp_left, specOfMap, specOfMapHom, Over.homMk_left,
AlgHom.coe_restrictScalars, Category.assoc]` followed by `rfl` closes it.

Namespace `Work.BcDiv`; file `Submission/Work/BcDiv/ptsK_map.lean`; imports
`Submission.Work.BcDiv.SymPts`. -/
theorem ptsK_map {K : Type u} [Field K] {C : Work.CurveBasics.Curve K} {L : Type u} [Field L]
    [Algebra K L] {F : Type u} [Field F] [Algebra L F] [Algebra K F] [IsScalarTower K L F]
    {F' : Type u} [Field F'] [Algebra L F'] [Algebra K F'] [IsScalarTower K L F']
    (e : F →ₐ[L] F') (n : ℕ) [Work.SymQuot.CurveAffineCover C]
    [Work.SymQuot.CurveAffineCover (C.baseChange L)]
    (p : Work.SpecLin.FPt (Work.SymQuot.Sym (C.baseChange L) n) F) :
    Work.BcDiv.ptsK (K := K) (L := L) (F := F') n (Work.SpecLin.RPt.map e p)
      = Work.SpecLin.RPt.map (e.restrictScalars K)
          (Work.BcDiv.ptsK (K := K) (L := L) (F := F) n p) := by
  apply Over.OverMorphism.ext
  rfl


end Work.BcDiv
