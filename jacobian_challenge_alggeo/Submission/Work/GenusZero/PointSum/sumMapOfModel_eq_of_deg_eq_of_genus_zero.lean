import Mathlib
import Submission.Work.GenusZero.Const

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


universe u

namespace Work.GenusZero.PointSum

open scoped CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.MonObj

/-- **The sum map at genus zero is constant in the degree.**  On a curve of genus zero, two
effective divisors which are split over `k` and have the same degree have the same sum of images
in a proper commutative group scheme.

The proof is `Work.GenusZero.principal_of_deg_zero` applied to `D - E` (of degree
`deg D - deg E = 0`) followed by the key lemma of area `KL`
(`Work.KeyLemma.Curve.sumMapOfModel_eq_of_linEquiv`). -/
theorem sumMapOfModel_eq_of_deg_eq_of_genus_zero {k : Type u} [Field k]
    (C : Work.CurveBasics.Curve k) (hg : Work.RiemannRoch.Curve.genus C = 0)
    {A : Work.GenusZero.Sch k} [CategoryTheory.GrpObj A]
    [AlgebraicGeometry.IsProper A.hom] [CategoryTheory.IsCommMonObj A]
    (f : C.toOver ⟶ A) {D E : C.Div} (hD : Work.KeyLemma.Curve.HasModel C D)
    (hE : Work.KeyLemma.Curve.HasModel C E) (hd : C.deg D = C.deg E) :
    Work.KeyLemma.Curve.sumMapOfModel C f D hD =
      Work.KeyLemma.Curve.sumMapOfModel C f E hE := by
  refine Work.KeyLemma.Curve.sumMapOfModel_eq_of_linEquiv C f
    (Work.KeyLemma.Curve.keyLemmaInput C f) hD hE ?_
  exact Work.GenusZero.principal_of_deg_zero C hg (D - E) (by
    rw [CurveBasics.Curve.deg_sub, hd, sub_self])

end Work.GenusZero.PointSum
