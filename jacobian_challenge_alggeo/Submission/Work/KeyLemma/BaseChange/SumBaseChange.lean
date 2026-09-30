/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Area KL: base change of the base field commutes with `Σ f`

The lead's item (b) for area `KL`: extending the base field `k` to a field `L` commutes with
the sum `Σ f` of the images of the points of a multiset of `k`-points.  The base-changed
"abelian variety" `A_L = A ×_k Spec L` carries the group structure transported along the
monoidal functor `Over.pullback (Spec.map k → L)` (Mathlib's `Functor.grpObjObj`, in the
scope `CategoryTheory.Obj`), and base change of points is a homomorphism for it.

## Main results

* `Work.KeyLemma.Curve.Pt.baseChange_mul`, `…baseChange_one`: base change of points is a
  homomorphism.
* `Work.KeyLemma.Curve.SumDiv.prod_mapDomain_baseChange`: the fibrewise form.
* `Work.KeyLemma.Curve.SumDiv.sumOfPoints_baseChange`: **`Σ f` commutes with base change**.

The corresponding *divisor-level* statement (that `Curve.sumMap` commutes with base change)
needs in addition the base change of divisors along a field extension, which relates
`toDiv C s` to `toDiv C_L (SumDiv.baseChange C L s)`; that is area `CB`'s item 6 and is not
available in the workspace (see `Submission/Work/KeyLemma/NOTES.md`).
-/
import Submission.Work.KeyLemma.BaseChange

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

variable {k : Type u} [Field k] {L : Type u} [Field L] [Algebra k L]

/-- The base change of `k`-points of a `k`-scheme is multiplicative, for the group structure
on the `L`-points of the base change. -/
theorem Pt.baseChange_mul {A : Over (Spec (CommRingCat.of k))} [GrpObj A] (p q : Pt k A) :
    Pt.baseChange L (p * q) = Pt.baseChange L p * Pt.baseChange L q := by
  unfold Pt.baseChange
  rw [Functor.map_mul, MonObj.comp_mul]

/-- The base change of points preserves the unit. -/
theorem Pt.baseChange_one {A : Over (Spec (CommRingCat.of k))} [GrpObj A] :
    Pt.baseChange L (1 : Pt k A) = 1 := by
  unfold Pt.baseChange
  rw [Functor.map_one]
  exact MonObj.comp_one _

/-- The fibrewise form of the compatibility of `Σ f` with base change: the product of the
images of the base-changed points is the product of the base changes of the images. -/
theorem SumDiv.prod_mapDomain_baseChange (C : Curve k)
    {A : Over (Spec (CommRingCat.of k))} [GrpObj A] [IsCommMonObj A]
    (f : C.toOver ⟶ A) (s : SumDiv C) :
    (s.mapDomain (Pt.baseChange L)).prod
        (fun p m => (p ≫ (baseChangeFunctor k L).map f) ^ m) =
      s.prod (fun p m => (Pt.baseChange L (p ≫ f)) ^ m) := by
  rw [Finsupp.prod_mapDomain_index (fun b => by simp) (fun b m₁ m₂ => by rw [pow_add])]
  exact Finsupp.prod_congr fun p _ => by rw [Pt.baseChange_comp]

/-- **Compatibility of `Σ f` with base change of the base field.**  For a morphism
`f : C ⟶ A` of `k`-schemes, a multiset `s` of `k`-points of `C` and a field extension
`L/k`, the sum of the images of the base-changed points of `s` in `A_L` (with the group
structure transported along `Over.pullback`) is the base change of the sum in `A`. -/
theorem SumDiv.sumOfPoints_baseChange (C : Curve k) {A : Over (Spec (CommRingCat.of k))}
    [GrpObj A] [IsCommMonObj A] (f : C.toOver ⟶ A) (s : SumDiv C) :
    SumDiv.sumOfPoints (Curve.baseChange C L) ((baseChangeFunctor k L).map f)
        (SumDiv.baseChange C L s) =
      Pt.baseChange L (SumDiv.sumOfPoints C f s) := by
  classical
  let Φ : Pt k A →* Pt L ((baseChangeFunctor k L).obj A) :=
    { toFun := Pt.baseChange L
      map_one' := Pt.baseChange_one
      map_mul' := Pt.baseChange_mul }
  show (s.mapDomain (Pt.baseChange L)).prod
        (fun p m => (p ≫ (baseChangeFunctor k L).map f) ^ m) =
      Φ (s.prod (fun p m => (p ≫ f) ^ m))
  rw [SumDiv.prod_mapDomain_baseChange C f s]
  show s.prod (fun p m => (Pt.baseChange L (p ≫ f)) ^ m) =
      Φ (s.prod (fun p m => (p ≫ f) ^ m))
  rw [Finsupp.prod, Finsupp.prod, map_prod Φ]
  refine Finset.prod_congr rfl fun p _ => ?_
  rw [map_pow]
  rfl

end

end Curve

end Work.KeyLemma
