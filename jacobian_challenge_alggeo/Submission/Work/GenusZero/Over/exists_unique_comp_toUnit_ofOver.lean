import Mathlib
import Submission.Work.GenusZero.Trivial

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


universe u

namespace Work.GenusZero.Over

open scoped CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.MonObj

theorem exists_unique_comp_toUnit_ofOver {k : Type u} [Field k] (C : Work.GenusZero.Sch k) [AlgebraicGeometry.SmoothOfRelativeDimension 1 C.hom] [AlgebraicGeometry.IsProper C.hom] [AlgebraicGeometry.GeometricallyIrreducible C.hom] (hred : AlgebraicGeometry.GeometricallyReduced C.hom) (hdim : ∀ z : C.left, Ring.KrullDimLE 1 (C.left.presheaf.stalk z)) (hnt : Nontrivial C.left) (hg : Work.RiemannRoch.Curve.genus (Work.CurveBasics.Curve.ofOver C hred hdim hnt) = 0) (P0 : 𝟙_ (Work.GenusZero.Sch k) ⟶ C) {A : Work.GenusZero.Sch k} [AlgebraicGeometry.Smooth A.hom] [AlgebraicGeometry.IsProper A.hom] [AlgebraicGeometry.GeometricallyIrreducible A.hom] [CategoryTheory.GrpObj A] (f : C ⟶ A) (hf : P0 ≫ f = η[A]) : ∃! g : 𝟙_ (Work.GenusZero.Sch k) ⟶ A, f = Work.GenusZero.toUnit C ≫ g := by
  have hmain : f = Work.GenusZero.toUnit C ≫ η[A] :=
    Work.GenusZero.eq_const_of_genus_zero_ofOver C hred hdim hnt hg P0 f hf
  refine ⟨η[A], hmain, ?_⟩
  intro g hg'
  exact Work.GenusZero.eq_of_comp_toUnit_eq P0 g η[A] (by rw [← hg', hmain])

end Work.GenusZero.Over
