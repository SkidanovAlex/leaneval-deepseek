/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Area KL: the key lemma for divisors which are only split over a field extension

The key lemma is stated in `Submission/Work/KeyLemma/Pencil.lean` for divisors which are split
over the *base* field (they are presented by a multiset of `k`-points).  This file covers the
general case of blueprint items 1, 4 and the equality half of item 5:

> `D`, `D'` effective on `C_F`, `D - D' = div h`.  Choose a field extension `L/F` over which
> `D` and `D'` become split, i.e. models `s`, `s'` of `divMap F L D`, `divMap F L D'` exist.
> Then the sums `Σ f(D)`, `Σ f(D')` in `A(F)` — specified as the elements of `A(F)` whose base
> change to `A(L)` is the sum over the chosen models — are equal.

The proof is: the base change of divisors is compatible with principal divisors
(`Work.CurveBasics.BaseChange.divMap_div`, area `CB`), so
`div (functionFieldMap h) = toDiv s - toDiv s'`; then apply the split key lemma over `L`; and
descend the resulting equality with `Work.KeyLemma.Curve.Pt.baseChange_injective`.

The hypothesis `IsSumOfAt C L f D sumD` is the *existence half of blueprint item 5* ("the sum
over the algebraic closure descends to `A(F)`"): it says that `sumD ∈ A(F)` base changes to the
sum computed over `L`.  It is a named hypothesis because the Galois descent of points of an
abelian variety, which produces such `sumD`, belongs to area `DS`.
-/
import Submission.Work.KeyLemma.Main
import Submission.Work.KeyLemma.Sum.isSplit_iff
import Submission.Work.CurveBasics.BaseChange.divMap_div

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry
open scoped Classical MonObj MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.Obj

universe u

namespace Work.KeyLemma

open Work.CurveBasics

namespace Curve

noncomputable section

variable {k : Type u} [Field k]

/-- **The key lemma over a splitting field.**  If `D`, `D'` are linearly equivalent effective
divisors of `C` whose base changes to `C_L` are split over `L`, with models `s`, `s'`, then the
sums of the images of the points of `s` and `s'` in `A_L(L)` agree.

This is the field-extension form of the key lemma: the split key lemma is applied to the curve
`C_L` over `L`; the hypothesis `D - D' = div h` for `C` becomes
`div (functionFieldMap h) = toDiv s - toDiv s'` over `L` by
`Work.CurveBasics.BaseChange.divMap_div`. -/
theorem sumOfPoints_eq_of_linEquiv_baseChange (C : Curve k) (L : Type u) [Field L] [Algebra k L]
    {A : Over (Spec (CommRingCat.of k))} [GrpObj A] [IsProper A.hom] [IsCommMonObj A]
    (f : C.toOver ⟶ A)
    (hgeo : PencilGeometric (Curve.baseChange C L) ((baseChangeFunctor k L).map f))
    {D D' : C.Div} (h : LinEquiv C D D')
    {s s' : SumDiv (Curve.baseChange C L)}
    (hs : SumDiv.toDiv (Curve.baseChange C L) s = Curve.divMap C L D)
    (hs' : SumDiv.toDiv (Curve.baseChange C L) s' = Curve.divMap C L D') :
    SumDiv.sumOfPoints (Curve.baseChange C L) ((baseChangeFunctor k L).map f) s =
      SumDiv.sumOfPoints (Curve.baseChange C L) ((baseChangeFunctor k L).map f) s' := by
  haveI : IsProper ((baseChangeFunctor k L).obj A).hom := by
    change IsProper (pullback.snd A.hom (Work.CurveBasics.Curve.specMap k L))
    infer_instance
  obtain ⟨h, hh, hdiv⟩ := h
  have hhL : (C.functionFieldMap L).hom h ≠ 0 := by
    intro h0
    exact hh (Curve.functionFieldMap_injective C L (by rw [h0, map_zero]))
  have hdivL : (C.baseChange L).div ((C.functionFieldMap L).hom h) =
      SumDiv.toDiv (C.baseChange L) s - SumDiv.toDiv (C.baseChange L) s' := by
    rw [← Work.CurveBasics.BaseChange.divMap_div L hh, hdiv, map_sub, hs, hs']
  exact sumOfPoints_eq_of_linEquiv (C.baseChange L) ((baseChangeFunctor k L).map f)
    (keyLemmaInput_of_pencil (C.baseChange L) ((baseChangeFunctor k L).map f) hgeo)
    hhL hdivL

/-- The specification of `Σ f(D) ∈ A(k)` for a divisor `D` of `C` which need not be split over
`k`: `sumD` is the element of `A(k)` whose base change along `L/k` is the sum of the images of
the points of every model over `L` of the base-changed divisor `divMap k L D`. -/
def IsSumOfAt (C : Curve k) (L : Type u) [Field L] [Algebra k L]
    {A : Over (Spec (CommRingCat.of k))} [GrpObj A] [IsCommMonObj A]
    (f : C.toOver ⟶ A) (D : C.Div) (sumD : Pt k A) : Prop :=
  ∀ s : SumDiv (C.baseChange L),
    SumDiv.toDiv (C.baseChange L) s = Curve.divMap C L D →
      Pt.baseChange L sumD =
        SumDiv.sumOfPoints (C.baseChange L) ((baseChangeFunctor k L).map f) s

/-- **The key lemma `KL` for divisors split only over an extension `L/k`.**  Let `D`, `D'` be
effective divisors of `C` which are linearly equivalent and whose base changes to `C_L` are
split over `L`, and let `sumD`, `sumD' ∈ A(k)` be the sums `Σ f(D)`, `Σ f(D')` (specified by
their base changes to `A(L)`, `IsSumOfAt`).  Then `sumD = sumD'`.

The geometric inputs are the same as for the split case, but over `L`: `PencilGeometric` for the
base-changed curve `C_L` and `P1CONST` over `L`. -/
theorem linEquiv_sum_eq_of_isSumOf (C : Curve k) (L : Type u) [Field L] [Algebra k L]
    {A : Over (Spec (CommRingCat.of k))} [GrpObj A] [IsProper A.hom] [IsCommMonObj A]
    (f : C.toOver ⟶ A)
    (hgeo : PencilGeometric (Curve.baseChange C L) ((baseChangeFunctor k L).map f))
    {D D' : C.Div} (hD : D.IsEffective) (hD' : D'.IsEffective) (h : LinEquiv C D D')
    (hsD : IsSplit (Curve.baseChange C L) (Curve.divMap C L D))
    (hsD' : IsSplit (Curve.baseChange C L) (Curve.divMap C L D'))
    {sumD sumD' : Pt k A}
    (hsumD : IsSumOfAt C L f D sumD) (hsumD' : IsSumOfAt C L f D' sumD') :
    sumD = sumD' := by
  obtain ⟨s, hs⟩ := (Work.KeyLemma.Sum.isSplit_iff (Curve.baseChange C L)
    (D := Curve.divMap C L D) (Work.CurveBasics.BaseChange.divMap_isEffective L hD)).mp hsD
  obtain ⟨s', hs'⟩ := (Work.KeyLemma.Sum.isSplit_iff (Curve.baseChange C L)
    (D := Curve.divMap C L D') (Work.CurveBasics.BaseChange.divMap_isEffective L hD')).mp hsD'
  have key := sumOfPoints_eq_of_linEquiv_baseChange C L f hgeo h hs hs'
  have hbc : Pt.baseChange L sumD = Pt.baseChange L sumD' := by
    rw [hsumD s hs, hsumD' s' hs', key]
  exact Pt.baseChange_injective L hbc

end

end Curve

end Work.KeyLemma
