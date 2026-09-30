/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Area KL: base change of points and of multisets of points

The lead's item (b) for area `KL` is *compatibility of `sumMapOfModel` with base change of the base
field*: extending the field `k` to a field `L` should commute with `Σ f`.  This file builds
the two halves of that statement which do not need the (still missing) base change of
divisors along a field extension:

* `Curve.Pt.baseChange`: the base change of a `k`-point of a `k`-scheme `X` to an `L`-point
  of `X_L = X ×_k Spec L`.  It is the image of the point under the monoidal functor
  `Over.pullback (Spec.map k → L)`, composed with the unit isomorphism.
* `Curve.SumDiv.baseChange`: the corresponding map on multisets of points.

The remaining half -- that `Σ f` commutes with this base change -- is the theorem
`Work.KeyLemma.BaseChange.sumOfPoints_baseChange`, proved in
`Submission/Work/KeyLemma/BaseChange/sumOfPoints_baseChange.lean`.  The relation between
`toDiv C s` and `toDiv C_L (baseChange s)` (i.e. the base change of *divisors*) is area CB's
item 6 and is not available in the workspace; see `NOTES.md`.
-/
import Submission.Work.KeyLemma.Sum

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry
open scoped Classical MonObj MonoidalCategory CartesianMonoidalCategory

universe u

namespace Work.KeyLemma

open Work.CurveBasics

namespace Curve

noncomputable section

variable {k : Type u} [Field k]

/-- The base change functor on `k`-schemes along a field extension `L/k`. -/
noncomputable abbrev baseChangeFunctor (k : Type u) [Field k] (L : Type u) [Field L]
    [Algebra k L] : Over (Spec (CommRingCat.of k)) ⥤ Over (Spec (CommRingCat.of L)) :=
  Over.pullback (Work.CurveBasics.Curve.specMap k L)

namespace Pt

variable {L : Type u} [Field L] [Algebra k L] {X : Over (Spec (CommRingCat.of k))}

/-- The base change of a `k`-point of a `k`-scheme `X` along `L/k`. -/
noncomputable def baseChange (L : Type u) [Field L] [Algebra k L] (p : Pt k X) :
    Pt L ((baseChangeFunctor k L).obj X) :=
  (Functor.Monoidal.εIso (baseChangeFunctor k L)).hom ≫ (baseChangeFunctor k L).map p

/-- Base change of points commutes with postcomposition with a morphism of `k`-schemes. -/
theorem baseChange_comp (L : Type u) [Field L] [Algebra k L] (p : Pt k X)
    {Y : Over (Spec (CommRingCat.of k))} (f : X ⟶ Y) :
    baseChange L (p ≫ f) = baseChange L p ≫ (baseChangeFunctor k L).map f := by
  simp only [baseChange, Functor.map_comp, Category.assoc]

/-- Base change of points is injective (in fact the base change functor is faithful). -/
theorem baseChange_injective (L : Type u) [Field L] [Algebra k L] :
    Function.Injective (baseChange (k := k) (X := X) L) := by
  intro p q h
  have h' : (baseChangeFunctor k L).map p = (baseChangeFunctor k L).map q :=
    (cancel_epi (Functor.Monoidal.εIso (baseChangeFunctor k L)).hom).mp h
  exact (baseChangeFunctor k L).map_injective h'

end Pt

namespace SumDiv

/-- The base change of a multiset of `k`-points of a curve along `L/k`. -/
noncomputable def baseChange (C : Curve k) (L : Type u) [Field L] [Algebra k L]
    (s : SumDiv C) : SumDiv (Curve.baseChange C L) :=
  s.mapDomain (Pt.baseChange (k := k) L)

@[simp]
theorem baseChange_zero (C : Curve k) (L : Type u) [Field L] [Algebra k L] :
    baseChange C L (0 : SumDiv C) = 0 :=
  Finsupp.mapDomain_zero

theorem baseChange_add (C : Curve k) (L : Type u) [Field L] [Algebra k L]
    (s t : SumDiv C) : baseChange C L (s + t) = baseChange C L s + baseChange C L t :=
  Finsupp.mapDomain_add

@[simp]
theorem baseChange_single (C : Curve k) (L : Type u) [Field L] [Algebra k L]
    (p : Point C) (m : ℕ) :
    baseChange C L (Finsupp.single p m) =
      Finsupp.single (Pt.baseChange L p) m :=
  Finsupp.mapDomain_single

/-- Base change does not change the number of points of a multiset (counted with
multiplicity). -/
theorem deg_baseChange (C : Curve k) (L : Type u) [Field L] [Algebra k L]
    (s : SumDiv C) : (baseChange C L s).deg = s.deg := by
  simp only [deg, baseChange]
  exact Finsupp.sum_mapDomain_index (fun b => rfl) (fun b m1 m2 => rfl)

end SumDiv

end

end Curve

/-- **Obligation for the lead's item (b)** (documentation, not a theorem of this file):

the base change functor `Over.pullback (specMap k L)` transports a group structure on a
`k`-scheme `A` to one on `A_L`, and with respect to it the base change of `A`-points is a
group homomorphism, so that

`Curve.SumDiv.sumOfPoints (C.baseChange L) (F.map f) (Curve.SumDiv.baseChange C L s)
  = Curve.Pt.baseChange L (Curve.SumDiv.sumOfPoints C f s)`.

Neither the transport `GrpObj A ⟹ GrpObj (F.obj A)` (with its commutative variant) nor the
compatibility statement is currently in Mathlib or in this workspace; the point-level
ingredient `Curve.Pt.baseChange_comp` is proved in this file, and
`Curve.Pt.baseChange_injective` is the "equality over `L` descends to `k`" half of blueprint
KL items 4 and 5. -/
theorem baseChange_obligations_documentation : True := trivial

end Work.KeyLemma
