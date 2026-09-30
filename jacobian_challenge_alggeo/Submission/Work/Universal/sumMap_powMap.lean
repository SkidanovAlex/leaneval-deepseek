import Mathlib
import Submission.Work.Universal.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry
open scoped Classical MonObj
open scoped Work.GCBasics

namespace Work.Universal

theorem sumMap_powMap {K : Type _} [Field K] {C : Work.CurveBasics.Curve K}
    {P0 : Work.AbVar.Point C.toOver} [Work.SpecLin.DivBase C]
    (D : Work.GroupChunk.Input C P0) [Work.Universal.SymQuotData C P0 D]
    {A : Work.GCBasics.Sch K} [CategoryTheory.GrpObj A] [CategoryTheory.IsCommMonObj A]
    (f : C.toOver ⟶ A) (n : ℕ) {T : Work.GCBasics.Sch K} (x : Fin n → (T ⟶ C.toOver)) :
    CategoryTheory.CategoryStruct.comp ((D.symGeom n).powMap x) (Work.Universal.sumMap D f n)
      = Work.Universal.prodHom (A := A) (X := T)
          (fun m => CategoryTheory.CategoryStruct.comp (x m) f) := by
  have hpow : (D.symGeom n).powMap x = Limits.Pi.lift x ≫ quotMap D n := by
    have h1 : x = (fun m => Limits.Pi.lift x ≫ proj C n m) :=
      funext (fun m => (Limits.Pi.lift_comp_π (f := fun _ : Fin n => C.toOver) x m).symm)
    calc (D.symGeom n).powMap x
        = (D.symGeom n).powMap (fun m => Limits.Pi.lift x ≫ proj C n m) :=
          congrArg (fun z : Fin n → (T ⟶ C.toOver) => (D.symGeom n).powMap z) h1
      _ = Limits.Pi.lift x ≫ (D.symGeom n).powMap (fun m => proj C n m) :=
          (D.symGeom n).powMap_comp (Limits.Pi.lift x) (fun m => proj C n m)
      _ = Limits.Pi.lift x ≫ quotMap D n := rfl
  calc (D.symGeom n).powMap x ≫ sumMap D f n
      = (Limits.Pi.lift x ≫ quotMap D n) ≫ sumMap D f n := by rw [hpow]
    _ = Limits.Pi.lift x ≫ (quotMap D n ≫ sumMap D f n) := Category.assoc _ _ _
    _ = Limits.Pi.lift x ≫ sumTerm C f n :=
        congrArg (fun u => Limits.Pi.lift x ≫ u) (sumMap_spec D f n)
    _ = ∏ m, (x m ≫ f) := by
        show Limits.Pi.lift x ≫ (∏ m, (proj C n m ≫ f)) = ∏ m, (x m ≫ f)
        exact (comp_prod (Limits.Pi.lift x) (fun m => proj C n m ≫ f)).trans
          (Finset.prod_congr rfl (fun m _ => (Category.assoc _ _ _).symm.trans
            (congrArg (fun u => u ≫ f)
              (Limits.Pi.lift_comp_π (f := fun _ : Fin n => C.toOver) x m))))

end Work.Universal
