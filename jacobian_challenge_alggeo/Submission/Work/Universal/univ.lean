import Mathlib
import Submission.Work.Universal.Factor
import Submission.Work.Universal.epi
import Submission.Work.Universal.factor_value
import Submission.Work.Universal.sumDiv_ptDiv
import Submission.Work.Universal.sumDiv_P0Div

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry
open scoped Classical MonObj
open scoped Work.GCBasics

namespace Work.Universal

noncomputable section

open Work.GCBasics Work.GroupChunk

/-- **The universal property of the Abel–Jacobi map.**

For a morphism `f : C ⟶ A` into an abelian variety sending the base point `P0` to the origin,
there is a unique morphism `g : G D ⟶ A` with `f = AJ₀ ≫ g`; the witness is the glued morphism
`factor f : G D ⟶ A` and uniqueness is the epimorphism statement `epi`.

Existence is checked at residue-field points of `C`, where `x ≫ AJ₀` is factored through a chart
of `G D`; the chart formula for `factor` (`factor_value`) evaluates `AJ₀ ≫ factor f` at `x` as
`Σ f([x]) / Σ f(P0Div) = f(x) / 1 = f(x)`. -/
theorem univ {K : Type _} [Field K] {C : Work.CurveBasics.Curve K}
    {P0 : Work.AbVar.Point C.toOver} [Work.SpecLin.DivBase C]
    [D : Work.GroupChunk.Input C P0] [U : Work.Universal.Input C P0]
    {A : Work.GCBasics.Sch K} [CategoryTheory.GrpObj A] [Work.AbVar.IsAbelianVariety A]
    (f : C.toOver ⟶ A)
    (hf : CategoryTheory.CategoryStruct.comp P0 f = CategoryTheory.MonObj.one (X := A)) :
    ∃! g : U.glued.G ⟶ A, f = CategoryTheory.CategoryStruct.comp U.AJ₀ g := by
  haveI hcomm : CategoryTheory.IsCommMonObj A := Work.AbVar.isCommMonObj_of_isAbelianVariety A
  haveI hsep : IsSeparated A.hom := Work.Universal.isSeparated_hom_of_grpObj A
  have key : f = U.AJ₀ ≫ factor (D := D) f := by
    apply GCBasics.hom_ext_of_resPt (K := K) (X := C.toOver) (Y := A)
    intro x
    let F := Work.GCBasics.resField C.toOver x
    letI : Algebra K F := Work.GCBasics.resFieldAlgebra C.toOver x
    let xF : Work.GCBasics.FPt C.toOver F := Work.GCBasics.resPt C.toOver x
    -- The value of `factor f` at the point `xF ≫ AJ₀`, computed by the chart formula.
    have hfv := factor_value (D := D) f (F := F) (p := xF ≫ U.AJ₀)
      (D₁ := Work.SpecLin.ptDiv xF) (D₂ := Work.GroupChunk.bcKF F D.P0Div)
      (Work.SpecLin.ptDiv_isEffective xF) (Work.Universal.bcKF_isEffective (D := D)) 1
      (Work.SpecLin.Points.ptDiv_deg xF) (Work.Universal.bcKF_P0Div_deg (D := D))
      (U.cls_AJ₀ xF)
    have h1 : Work.Universal.sumDiv D f (Work.SpecLin.ptDiv xF)
        (Work.SpecLin.ptDiv_isEffective xF) 1 (Work.SpecLin.Points.ptDiv_deg xF)
        = xF ≫ f := Work.Universal.sumDiv_ptDiv D f xF
    have h2 : Work.Universal.sumDiv D f (Work.GroupChunk.bcKF F D.P0Div)
        (Work.Universal.bcKF_isEffective (D := D)) 1
        (Work.Universal.bcKF_P0Div_deg (D := D))
        = Work.Universal.zeroPt A F := Work.Universal.sumDiv_P0Div (D := D) f hf
    have hval : (xF ≫ U.AJ₀) ≫ factor (D := D) f = xF ≫ f := by
      rw [hfv, h1, h2]
      unfold Work.Universal.divPt Work.Universal.zeroPt
      rw [show (Work.GroupChunk.toUnit (Work.GCBasics.specOf K F)
          ≫ MonObj.one (X := A) : Work.GCBasics.specOf K F ⟶ A) = 1 from rfl, div_one]
    rw [← Category.assoc]
    exact hval.symm
  refine ⟨factor (D := D) f, key, ?_⟩
  intro y hy
  exact epi (D := D) (U := U) y (factor (D := D) f) (hy.symm.trans key)

end

end Work.Universal
