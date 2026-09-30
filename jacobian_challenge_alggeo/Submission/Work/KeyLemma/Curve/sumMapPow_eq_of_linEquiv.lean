import Mathlib
import Submission.Work.KeyLemma.SymPow
import Submission.Work.KeyLemma.General
import Submission.Work.KeyLemma.Curve.isSplit_of_isAlgClosed
import Submission.Work.KeyLemma.Curve.sumMapPow_toDiv
import Submission.Work.KeyLemma.Curve.sumMapPow_baseChange

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


open CategoryTheory Limits AlgebraicGeometry
open scoped Classical MonObj MonoidalCategory CartesianMonoidalCategory
-- Mathlib's transport of (commutative) group objects along a monoidal functor:
open scoped CategoryTheory.Obj

namespace Work.KeyLemma.Curve

universe u

/-- **The sum `Σ f` over `L` computed by the base-changed sum morphism agrees with the sum
of the images of the points of a model.**  If `s` is a multiset of `L`-points of `C_L` whose
attached divisor is the pullback `divMap C L D` of `D`, then the value of the base-changed
sum morphism `Φ` at the point of `Sym^n C_L` classified by `divMap C L D` is the sum
`Σ f(s)` of the images of the points of `s`.

This is the base-changed form of `Curve.sumMapPow_toDiv`: `sumMapPowBC` is by definition the
value of the base-changed sum morphism at the classified point of `divMap C L D`, and
`Curve.sumMapPow_toDiv` computes that value on a divisor presented by a multiset. -/
theorem sumMapPowBC_eq_sumOfPoints {k : Type u} [Field k] {C : Work.CurveBasics.Curve k} {n : ℕ}
    (G : Work.KeyLemma.Curve.SymPow C n)
    {A : CategoryTheory.Over (AlgebraicGeometry.Spec (CommRingCat.of k))}
    [CategoryTheory.GrpObj A] [CategoryTheory.IsCommMonObj A]
    {Φ : G.S ⟶ A} {f : C.toOver ⟶ A}
    {L : Type u} [Field L] [Algebra k L] (bc : G.BaseChange L)
    (hΦL : Work.KeyLemma.Curve.IsSumMorphismBC G Φ bc f)
    (D : C.Div) (hD : D.IsEffective) (hn : C.deg D = (n : ℤ))
    (s : Work.KeyLemma.Curve.SumDiv (C.baseChange L))
    (hs : Work.KeyLemma.Curve.SumDiv.toDiv (C.baseChange L) s = C.divMap L D) :
    Work.KeyLemma.Curve.sumMapPowBC G Φ bc D hD hn =
      Work.KeyLemma.Curve.SumDiv.sumOfPoints (C.baseChange L)
        ((Work.KeyLemma.Curve.baseChangeFunctor k L).map f) s := by
  have h1 : Work.KeyLemma.Curve.sumMapPowBC G Φ bc D hD hn =
      Work.KeyLemma.Curve.sumMap bc.G'
        (bc.iso.inv ≫ (Work.KeyLemma.Curve.baseChangeFunctor k L).map Φ)
        ⟨C.divMap L D, bc.divMap_isEffective hD, (bc.divMap_deg D).trans hn⟩ := rfl
  rw [h1]
  exact Work.KeyLemma.Curve.sumMapPow_toDiv bc.G' hΦL s _ hs

theorem sumMapPow_eq_of_linEquiv {k : Type u} [Field k] {C : Work.CurveBasics.Curve k} {n : ℕ}
    (G : Work.KeyLemma.Curve.SymPow C n)
    {A : CategoryTheory.Over (AlgebraicGeometry.Spec (CommRingCat.of k))}
    [CategoryTheory.GrpObj A] [CategoryTheory.IsCommMonObj A] [AlgebraicGeometry.IsProper A.hom]
    (f : C.toOver ⟶ A) {Φ : G.S ⟶ A}
    {L : Type u} [Field L] [Algebra k L] [IsAlgClosed L] (bc : G.BaseChange L)
    (hΦL : Work.KeyLemma.Curve.IsSumMorphismBC G Φ bc f)
    (hgeo : Work.KeyLemma.Curve.PencilGeometricBaseChange L f)
    (D D' : Work.KeyLemma.Curve.EffDiv C n) (h : Work.KeyLemma.Curve.EffDiv.LinEquiv D D') :
    Work.KeyLemma.Curve.sumMap G Φ D = Work.KeyLemma.Curve.sumMap G Φ D' := by
  -- Over the algebraically closed field `L` every effective divisor is split, so
  -- `divMap C L D` and `divMap C L D'` have models `s`, `s'`.
  have hsplitD : Work.KeyLemma.Curve.IsSplit (C.baseChange L) (C.divMap L D.1) :=
    Work.KeyLemma.Curve.isSplit_of_isAlgClosed (C.divMap L D.1)
      (bc.divMap_isEffective D.isEffective)
  obtain ⟨s, hs⟩ := (Work.KeyLemma.Sum.isSplit_iff (C.baseChange L)
    (bc.divMap_isEffective D.isEffective)).mp hsplitD
  have hsplitD' : Work.KeyLemma.Curve.IsSplit (C.baseChange L) (C.divMap L D'.1) :=
    Work.KeyLemma.Curve.isSplit_of_isAlgClosed (C.divMap L D'.1)
      (bc.divMap_isEffective D'.isEffective)
  obtain ⟨s', hs'⟩ := (Work.KeyLemma.Sum.isSplit_iff (C.baseChange L)
    (bc.divMap_isEffective D'.isEffective)).mp hsplitD'
  -- The base change of `Σ f(D)` is the sum of the images of the points of the model `s`.
  have hbcD : Work.KeyLemma.Curve.Pt.baseChange L (Work.KeyLemma.Curve.sumMap G Φ D) =
      Work.KeyLemma.Curve.SumDiv.sumOfPoints (C.baseChange L)
        ((Work.KeyLemma.Curve.baseChangeFunctor k L).map f) s := by
    rw [Work.KeyLemma.Curve.sumMap_apply]
    change Work.KeyLemma.Curve.sumMapPowBaseChange G Φ D.1 D.isEffective D.deg_eq =
      Work.KeyLemma.Curve.SumDiv.sumOfPoints (C.baseChange L)
        ((Work.KeyLemma.Curve.baseChangeFunctor k L).map f) s
    rw [Work.KeyLemma.Curve.sumMapPow_baseChange G Φ bc D.1 D.isEffective D.deg_eq]
    exact sumMapPowBC_eq_sumOfPoints G bc hΦL D.1 D.isEffective D.deg_eq s hs
  have hbcD' : Work.KeyLemma.Curve.Pt.baseChange L (Work.KeyLemma.Curve.sumMap G Φ D') =
      Work.KeyLemma.Curve.SumDiv.sumOfPoints (C.baseChange L)
        ((Work.KeyLemma.Curve.baseChangeFunctor k L).map f) s' := by
    rw [Work.KeyLemma.Curve.sumMap_apply]
    change Work.KeyLemma.Curve.sumMapPowBaseChange G Φ D'.1 D'.isEffective D'.deg_eq =
      Work.KeyLemma.Curve.SumDiv.sumOfPoints (C.baseChange L)
        ((Work.KeyLemma.Curve.baseChangeFunctor k L).map f) s'
    rw [Work.KeyLemma.Curve.sumMapPow_baseChange G Φ bc D'.1 D'.isEffective D'.deg_eq]
    exact sumMapPowBC_eq_sumOfPoints G bc hΦL D'.1 D'.isEffective D'.deg_eq s' hs'
  -- The key lemma over `L` (area `KL`, `Curve.sumOfPoints_eq_of_linEquiv_baseChange`).
  have key := Work.KeyLemma.Curve.sumOfPoints_eq_of_linEquiv_baseChange C L f hgeo h hs hs'
  -- Descend the equality from `L` to `k`.
  exact Work.KeyLemma.Curve.Pt.baseChange_injective L (hbcD.trans (key.trans hbcD'.symm))

end Work.KeyLemma.Curve
