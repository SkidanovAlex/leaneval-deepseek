import Mathlib
import Submission.Work.GroupChunk.Interface
import Submission.Work.GroupChunk.AbelJacobi

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option linter.style.haveILetI false

namespace Work.GroupChunk.Genus

universe u
open CategoryTheory in
theorem one_le_g {K : Type u} [Field K] {C : Work.CurveBasics.Curve K}
    {P0 : MonoidalCategoryStruct.tensorUnit (Work.GCBasics.Sch K) ⟶ C.toOver}
    [Work.SpecLin.DivBase C] (D : Work.GroupChunk.Input C P0) : 1 ≤ D.g := by
  -- The genus of the chart datum is at least one: if `D.g = 0`, then `g • [P0] = 0`, and
  -- evaluating the interface field `Input.curveAdd_divOf` at a residue-field point `z` of `C`
  -- would express the degree-one divisor `ptDiv z` as the divisor of a point of `Sym^0 C`,
  -- which has degree `0`.
  by_contra h
  have hg : D.g = 0 := Nat.lt_one_iff.mp (Nat.not_le.mp h)
  obtain ⟨z⟩ := (inferInstance : Nonempty C.toOver.left)
  let F := Work.GCBasics.resField C.toOver z
  letI : Algebra K F := Work.GCBasics.resFieldAlgebra C.toOver z
  let p : Work.GCBasics.FPt C.toOver F := Work.GCBasics.resPt C.toOver z
  have h1 : (C.baseChange F).deg (Work.SpecLin.ptDiv p) = 1 :=
    Work.SpecLin.Points.ptDiv_deg p
  have h2 : (C.baseChange F).deg ((D.symGeom D.g).divOf (p ≫ D.curveAdd)) = (D.g : ℤ) :=
    (D.symGeom D.g).divOf_deg (p ≫ D.curveAdd)
  have h3 : (D.symGeom D.g).divOf (p ≫ D.curveAdd) = Work.SpecLin.ptDiv p := by
    rw [D.curveAdd_divOf (F := F) p, hg]
    simp
  rw [h3] at h2
  rw [h1] at h2
  omega

end Work.GroupChunk.Genus
