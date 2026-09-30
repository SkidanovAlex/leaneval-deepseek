import Mathlib
import Submission.Work.GenusZero.Rigidity

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


namespace Work.GenusZero.Rigid

open scoped CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.MonObj

universe u

theorem isConstant_of_genus_zero {k : Type u} [Field k] (C : Work.CurveBasics.Curve k) (hg : Work.RiemannRoch.Curve.genus C = 0) (hP : Nonempty (Work.KeyLemma.Curve.Point C)) {A : Work.GenusZero.Sch k} [AlgebraicGeometry.Smooth A.hom] [AlgebraicGeometry.IsProper A.hom] [AlgebraicGeometry.GeometricallyIrreducible A.hom] [CategoryTheory.GrpObj A] (f : C.toOver ⟶ A) : ∃ c : 𝟙_ (Work.GenusZero.Sch k) ⟶ A, f = Work.GenusZero.toUnit C.toOver ≫ c := by
  obtain ⟨P⟩ := hP
  exact ⟨P ≫ f, Work.GenusZero.const_of_genus_zero_hasPoint C hg P f⟩

end Work.GenusZero.Rigid
