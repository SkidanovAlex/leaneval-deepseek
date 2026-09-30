import Mathlib
import Submission.Work.Charts.SymBC
import Submission.Work.Charts.Step3Defs
import Submission.Work.Universal.Basic
import Submission.Work.GCBasics.All
import Submission.Work.SpecLin.Points.ptDiv_deg

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


namespace Work.BcDiv

universe u

/-- The divisor-level computation underlying `pic0Map_picAJ`: `bcDiv` sends the degree-zero
divisor `divOf q - g • ptDiv P0'` of `C_L` to `divOf (B.pts q) - g • ptDiv P0` on `C`. -/
theorem bcDiv_divOf_sub_ptDiv {K : Type u} [Field K] {C : Work.CurveBasics.Curve K}
    [Work.SpecLin.DivBase C] {R : Work.Charts.RochData C} [Work.SpecLin.SymGeom C R.g]
    {L : Type u} [Field L] [Algebra K L] [Work.SpecLin.DivBase (C.baseChange L)]
    {R' : Work.Charts.RochData (C.baseChange L)} [Work.SpecLin.SymGeom (C.baseChange L) R'.g]
    (hg : R'.g = R.g) (B : Work.Charts.SymBC R L R')
    {P0 : Work.Charts.unitSch K ⟶ C.toOver}
    {P0' : Work.Charts.unitSch L ⟶ (C.baseChange L).toOver}
    (hP0 : ∀ {F : Type u} [Field F] [Algebra L F] [Algebra K F] [IsScalarTower K L F],
      B.bcDiv (Work.SpecLin.ptDiv (Work.Universal.P0Pt (C.baseChange L) P0' F))
        = Work.SpecLin.ptDiv (Work.Universal.P0Pt C P0 F))
    {F : Type u} [Field F] [Algebra L F] [Algebra K F] [IsScalarTower K L F]
    (q : Work.GCBasics.FPt (Work.Charts.Sym (C.baseChange L) R'.g) F) :
    B.bcDiv (Work.SpecLin.SymGeom.divOf q - (R'.g : ℤ) •
        Work.SpecLin.ptDiv (Work.Universal.P0Pt (C.baseChange L) P0' F))
      = Work.SpecLin.SymGeom.divOf (B.pts q) - (R.g : ℤ) •
        Work.SpecLin.ptDiv (Work.Universal.P0Pt C P0 F) := by
  have hg' : (R'.g : ℤ) = (R.g : ℤ) := by rw [hg]
  rw [map_sub, map_zsmul, B.pts_divOf, hP0, hg']

theorem pic0Map_picAJ {K : Type u} [Field K] {C : Work.CurveBasics.Curve K}
    [Work.SpecLin.DivBase C] {R : Work.Charts.RochData C} [Work.SpecLin.SymGeom C R.g]
    {L : Type u} [Field L] [Algebra K L] [Work.SpecLin.DivBase (C.baseChange L)]
    {R' : Work.Charts.RochData (C.baseChange L)} [Work.SpecLin.SymGeom (C.baseChange L) R'.g]
    (hg : R'.g = R.g) (B : Work.Charts.SymBC R L R')
    {P0 : Work.Charts.unitSch K ⟶ C.toOver}
    {P0' : Work.Charts.unitSch L ⟶ (C.baseChange L).toOver}
    (hP0 : ∀ {F : Type u} [Field F] [Algebra L F] [Algebra K F] [IsScalarTower K L F],
      B.bcDiv (Work.SpecLin.ptDiv (Work.Universal.P0Pt (C.baseChange L) P0' F))
        = Work.SpecLin.ptDiv (Work.Universal.P0Pt C P0 F))
    {F : Type u} [Field F] [Algebra L F] [Algebra K F] [IsScalarTower K L F]
    (q : Work.GCBasics.FPt (Work.Charts.Sym (C.baseChange L) R'.g) F) :
    B.pic0Map (Work.GCBasics.Pic0.mk
        (Work.SpecLin.SymGeom.divOf q - (R'.g : ℤ) •
          Work.SpecLin.ptDiv (Work.Universal.P0Pt (C.baseChange L) P0' F))
        (by rw [map_sub, map_zsmul,
              show (Work.GCBasics.Ddeg (C.baseChange L) F) (Work.SpecLin.SymGeom.divOf q) = (R'.g : ℤ)
                from (inferInstance : Work.SpecLin.SymGeom (C.baseChange L) R'.g).divOf_deg q,
              show (Work.GCBasics.Ddeg (C.baseChange L) F)
                    (Work.SpecLin.ptDiv (Work.Universal.P0Pt (C.baseChange L) P0' F)) = 1
                from Work.SpecLin.Points.ptDiv_deg _]
            simp))
      = Work.GCBasics.Pic0.mk
        (Work.SpecLin.SymGeom.divOf (B.pts q) - (R.g : ℤ) •
          Work.SpecLin.ptDiv (Work.Universal.P0Pt C P0 F))
        (by rw [map_sub, map_zsmul,
              show (Work.GCBasics.Ddeg C F) (Work.SpecLin.SymGeom.divOf (B.pts q)) = (R.g : ℤ)
                from (inferInstance : Work.SpecLin.SymGeom C R.g).divOf_deg (B.pts q),
              show (Work.GCBasics.Ddeg C F)
                    (Work.SpecLin.ptDiv (Work.Universal.P0Pt C P0 F)) = 1
                from Work.SpecLin.Points.ptDiv_deg _]
            simp) := by
  rw [B.pic0Map_mk]
  congr 1
  exact bcDiv_divOf_sub_ptDiv hg B hP0 q

end Work.BcDiv
