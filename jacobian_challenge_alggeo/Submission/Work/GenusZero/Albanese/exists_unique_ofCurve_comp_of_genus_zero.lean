import Mathlib
import Submission.Work.GenusZero.Rigidity

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


universe u

namespace Work.GenusZero.Albanese

open CategoryTheory
open scoped CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.MonObj

theorem exists_unique_ofCurve_comp_of_genus_zero {k : Type u} [Field k] (C : Work.CurveBasics.Curve k) (hg : Work.RiemannRoch.Curve.genus C = 0) (P : 𝟙_ (Work.GenusZero.Sch k) ⟶ C.toOver) {A : Work.GenusZero.Sch k} [AlgebraicGeometry.Smooth A.hom] [AlgebraicGeometry.IsProper A.hom] [AlgebraicGeometry.GeometricallyIrreducible A.hom] [CategoryTheory.GrpObj A] (f : C.toOver ⟶ A) (hf : P ≫ f = η[A]) : ∃! g : 𝟙_ (Work.GenusZero.Sch k) ⟶ A, f = Work.GenusZero.toUnit C.toOver ≫ g := by
  have h1 : P ≫ Work.GenusZero.toUnit C.toOver = 𝟙 (𝟙_ (Work.GenusZero.Sch k)) :=
    (Work.GenusZero.toUnit_unique _ _).trans Work.GenusZero.toUnit_tensorUnit
  refine ⟨η[A], Work.GenusZero.eq_const_of_genus_zero C hg P f hf, ?_⟩
  intro g hg'
  calc g = 𝟙 (𝟙_ (Work.GenusZero.Sch k)) ≫ g := (Category.id_comp g).symm
    _ = (P ≫ Work.GenusZero.toUnit C.toOver) ≫ g := by rw [h1]
    _ = P ≫ (Work.GenusZero.toUnit C.toOver ≫ g) := Category.assoc _ _ _
    _ = P ≫ f := by rw [← hg']
    _ = η[A] := hf

end Work.GenusZero.Albanese
