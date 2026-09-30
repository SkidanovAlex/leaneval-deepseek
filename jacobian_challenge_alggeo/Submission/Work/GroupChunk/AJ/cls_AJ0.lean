import Mathlib
import Submission.Work.GroupChunk.AJ0Basic
import Submission.Work.GroupChunk.AJSym
import Submission.Work.GroupChunk.AbelJacobi

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


namespace Work.GroupChunk.AJ

universe u
open CategoryTheory in
open scoped AlgebraicGeometry in
theorem cls_AJ0 {K : Type u} [Field K] {C : Work.CurveBasics.Curve K}
    {P0 : MonoidalCategoryStruct.tensorUnit (Work.GCBasics.Sch K) ⟶ C.toOver}
    [Work.SpecLin.DivBase C] (D : Work.GroupChunk.Input C P0) {F : Type u} [Field F]
    [Algebra K F] (x : Work.GCBasics.FPt C.toOver F) :
    Work.GroupChunk.Input.cls D (x ≫ Work.GroupChunk.Input.AJ₀ D) =
      Work.GCBasics.Pic0.mk
        (Work.SpecLin.ptDiv x - Work.GroupChunk.bcKF F D.P0Div)
        (Work.GroupChunk.Input.ddeg_ptDiv_sub_bcKF_P0Div (D := D) x) := by
  -- The Abel–Jacobi map is the composite `curveAdd ≫ AJSym`, so the class is `picAJ` of
  -- the point `x ≫ curveAdd`.
  rw [show Work.GroupChunk.Input.cls D (x ≫ Work.GroupChunk.Input.AJ₀ D)
      = Work.GroupChunk.Input.picAJ D (x ≫ D.curveAdd) from by
    rw [Work.GroupChunk.Input.AJ₀, ← Category.assoc]
    exact Work.GroupChunk.Input.cls_AJSym D (x ≫ D.curveAdd)]
  show Work.GCBasics.Pic0.mk
      (D.divOf D.g (x ≫ D.curveAdd) - Work.GroupChunk.bcKF F D.P0g) _
    = Work.GCBasics.Pic0.mk
        (Work.SpecLin.ptDiv x - Work.GroupChunk.bcKF F D.P0Div)
        (Work.GroupChunk.Input.ddeg_ptDiv_sub_bcKF_P0Div (D := D) x)
  -- The two degree-zero divisors are linearly equivalent, so their classes agree.
  rw [Work.GCBasics.Pic0.mk_eq_iff]
  -- `divOf (x + (g-1)P0) = [x] + (g-1)[P0]`.
  have hdiv := D.curveAdd_divOf x
  -- Base change commutes with the `ℕ`-multiple `g • P0Div`.
  have hbc : Work.GroupChunk.bcKF F D.P0g
      = D.g • Work.GroupChunk.bcKF F D.P0Div := by
    rw [Work.GroupChunk.Input.P0g]
    let f : Work.GCBasics.Dv C K →+ Work.GCBasics.Dv C F :=
      { toFun := Work.GroupChunk.bcKF F
        map_zero' := Work.SpecLin.DivBase.bc_zero (Algebra.ofId K F)
        map_add' := fun A B => Work.SpecLin.DivBase.bc_add (Algebra.ofId K F) A B }
    change f (D.g • D.P0Div) = D.g • f D.P0Div
    rw [map_nsmul]
  -- The genus is at least one: the degree of `[x] + (g-1)[P0]` is `g`, i.e.
  -- `g = 1 + (g-1)`.
  have hg : 1 ≤ D.g := by
    have hgdeg : (D.g : ℤ) = 1 + ((D.g - 1 : ℕ) : ℤ) := by
      have h := (D.symGeom D.g).divOf_deg (x ≫ D.curveAdd)
      rw [hdiv] at h
      have h' : Work.GCBasics.Ddeg C F (Work.SpecLin.ptDiv x
          + (D.g - 1) • Work.GroupChunk.bcKF F D.P0Div) = (D.g : ℤ) := h
      rw [map_add,
        show Work.GCBasics.Ddeg C F (Work.SpecLin.ptDiv x) = 1 from
          Work.SpecLin.Points.ptDiv_deg x,
        map_nsmul,
        show Work.GCBasics.Ddeg C F (Work.GroupChunk.bcKF F D.P0Div) = 1 from by
          rw [Work.GroupChunk.deg_bcKF, D.P0Div_deg]] at h'
      rw [nsmul_eq_mul, mul_one] at h'
      exact h'.symm
    omega
  -- `ptDiv x + (g-1)E - gE = ptDiv x - E` since `g = (g-1) + 1`.
  rw [show D.divOf D.g (x ≫ D.curveAdd)
      = Work.SpecLin.ptDiv x + (D.g - 1) • Work.GroupChunk.bcKF F D.P0Div from hdiv, hbc]
  have hsmul : (D.g - 1) • Work.GroupChunk.bcKF F D.P0Div
      + Work.GroupChunk.bcKF F D.P0Div = D.g • Work.GroupChunk.bcKF F D.P0Div := by
    conv_rhs => rw [← Nat.sub_add_cancel hg]
    rw [add_nsmul, one_nsmul]
  rw [show Work.SpecLin.ptDiv x + (D.g - 1) • Work.GroupChunk.bcKF F D.P0Div
        - D.g • Work.GroupChunk.bcKF F D.P0Div
      = Work.SpecLin.ptDiv x - Work.GroupChunk.bcKF F D.P0Div from by
    rw [← hsmul]; abel]
  exact Work.GCBasics.LinEquiv.refl _

end Work.GroupChunk.AJ
