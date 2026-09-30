import Mathlib
import Submission.Work.KeyLemma.BaseChange

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

namespace Work.KeyLemma.BaseChange

universe u

/-!
# The place of a base changed point

Extending the base field `k` to a field `L` is compatible with the construction
`Curve.placeOfPoint` which attaches to a `k`-point of a curve its image, a closed point
(a *place*) of the curve.

The mathematical content is the commutativity of the square

```
Spec L --q--> C_L
  |            |
  |            |
Spec k --p--> C
```

where `q = Pt.baseChange L p` is the base change of the `k`-point `p` and `C_L ⟶ C` is the
projection `Curve.baseChangeFst C L`; both vertical maps are the structure morphisms.  Since
`Spec k` is a single point, this says that the image of `q` in `C_L` projects to the image of
`p` in `C`.

The point level statement is `Pt_leftHom_baseChange` below, from which the result for places
follows immediately, because `placeOfPoint` only depends on the underlying morphism of
schemes and the unique point of `Spec` of a field.
-/

/-- **Base change of points commutes with the projection of the base changed scheme.**
For a `k`-point `p : Spec k ⟶ X` of a `k`-scheme `X` and a field extension `L/k`, the base
changed `L`-point `Pt.baseChange L p : Spec L ⟶ X_L` of `X_L = X ×_k Spec L` makes the
square

```
Spec L --Pt.baseChange L p--> X_L
  |                              |
  v                              v
Spec k ------p----------------> X
```

commute, i.e. `baseChange L p ≫ fst = specMap k L ≫ p`.

Both sides are computed from the definition of `Pt.baseChange` as
`ε ≫ (Over.pullback (specMap k L)).map p`: the naturality square of the pullback functor
evaluated at `p`, together with `Over.ε_pullback_left`, which identifies the `left`
component of `ε` with the inverse of the canonical isomorphism
`pullback (𝟙 _) (specMap k L) ≅ Spec L`. -/
theorem Pt_leftHom_baseChange {k : Type u} [Field k] {L : Type u} [Field L] [Algebra k L]
    {X : Over (Spec (CommRingCat.of k))} (p : Work.KeyLemma.Curve.Pt k X) :
    Over.Hom.left (Work.KeyLemma.Curve.Pt.baseChange (k := k) L p) ≫
        pullback.fst X.hom (Work.CurveBasics.Curve.specMap k L) =
      Work.CurveBasics.Curve.specMap k L ≫ Over.Hom.left p := by
  -- the `left` component of `Pt.baseChange L p`
  have hA : Over.Hom.left (Work.KeyLemma.Curve.Pt.baseChange (k := k) L p) =
      inv (pullback.snd (𝟙 (Spec (CommRingCat.of k)))
            (Work.CurveBasics.Curve.specMap k L)) ≫
        Over.Hom.left ((Work.KeyLemma.Curve.baseChangeFunctor k L).map p) := by
    rw [Work.KeyLemma.Curve.Pt.baseChange, CategoryTheory.Over.comp_left,
      Functor.Monoidal.εIso_hom, CategoryTheory.Over.ε_pullback_left]
  -- the naturality square of the pullback functor `Over.pullback (specMap k L)`
  have hB : Over.Hom.left ((Work.KeyLemma.Curve.baseChangeFunctor k L).map p) ≫
      pullback.fst X.hom (Work.CurveBasics.Curve.specMap k L) =
      pullback.fst (𝟙 (Spec (CommRingCat.of k)))
        (Work.CurveBasics.Curve.specMap k L) ≫ Over.Hom.left p := by
    simp only [Work.KeyLemma.Curve.baseChangeFunctor, CategoryTheory.Over.pullback_map_left,
      CategoryTheory.Over.tensorUnit_hom, pullback.lift_fst]
  -- the canonical isomorphism `pullback (𝟙 _) (specMap k L) ≅ Spec L` is compatible
  -- with the two projections
  have hC : inv (pullback.snd (𝟙 (Spec (CommRingCat.of k)))
        (Work.CurveBasics.Curve.specMap k L)) ≫
      pullback.fst (𝟙 (Spec (CommRingCat.of k))) (Work.CurveBasics.Curve.specMap k L) =
      Work.CurveBasics.Curve.specMap k L := by
    have hfst : pullback.fst (𝟙 (Spec (CommRingCat.of k)))
          (Work.CurveBasics.Curve.specMap k L) =
        pullback.snd (𝟙 (Spec (CommRingCat.of k)))
          (Work.CurveBasics.Curve.specMap k L) ≫ Work.CurveBasics.Curve.specMap k L := by
      calc pullback.fst (𝟙 (Spec (CommRingCat.of k)))
              (Work.CurveBasics.Curve.specMap k L)
          = pullback.fst (𝟙 (Spec (CommRingCat.of k)))
              (Work.CurveBasics.Curve.specMap k L) ≫ 𝟙 (Spec (CommRingCat.of k)) :=
            (Category.comp_id _).symm
        _ = pullback.snd (𝟙 (Spec (CommRingCat.of k)))
              (Work.CurveBasics.Curve.specMap k L) ≫
              Work.CurveBasics.Curve.specMap k L := pullback.condition
    rw [hfst, ← Category.assoc, IsIso.inv_hom_id, Category.id_comp]
  calc Over.Hom.left (Work.KeyLemma.Curve.Pt.baseChange (k := k) L p) ≫
        pullback.fst X.hom (Work.CurveBasics.Curve.specMap k L)
      = (inv (pullback.snd (𝟙 (Spec (CommRingCat.of k)))
            (Work.CurveBasics.Curve.specMap k L)) ≫
          Over.Hom.left ((Work.KeyLemma.Curve.baseChangeFunctor k L).map p)) ≫
            pullback.fst X.hom (Work.CurveBasics.Curve.specMap k L) := by rw [hA]
    _ = inv (pullback.snd (𝟙 (Spec (CommRingCat.of k)))
            (Work.CurveBasics.Curve.specMap k L)) ≫
          (Over.Hom.left ((Work.KeyLemma.Curve.baseChangeFunctor k L).map p) ≫
            pullback.fst X.hom (Work.CurveBasics.Curve.specMap k L)) := by rw [Category.assoc]
    _ = inv (pullback.snd (𝟙 (Spec (CommRingCat.of k)))
            (Work.CurveBasics.Curve.specMap k L)) ≫
          (pullback.fst (𝟙 (Spec (CommRingCat.of k)))
            (Work.CurveBasics.Curve.specMap k L) ≫ Over.Hom.left p) := by rw [hB]
    _ = Work.CurveBasics.Curve.specMap k L ≫ Over.Hom.left p := by
        rw [← Category.assoc, hC]

theorem proj_placeOfPoint_baseChange {k : Type u} [Field k] (C : Work.CurveBasics.Curve k)
    (L : Type u) [Field L] [Algebra k L] (p : Work.KeyLemma.Curve.Point C) :
    Work.CurveBasics.Curve.baseChangeFst C L
      ((Work.KeyLemma.Curve.placeOfPoint (Work.CurveBasics.Curve.baseChange C L)
        (Work.KeyLemma.Curve.Pt.baseChange L p)).point) =
    (Work.KeyLemma.Curve.placeOfPoint C p).point := by
  -- `placeOfPoint` only remembers the underlying morphism of schemes
  show Work.CurveBasics.Curve.baseChangeFst C L
      (Over.Hom.left (Work.KeyLemma.Curve.Pt.baseChange (k := k) L p)
        (IsLocalRing.closedPoint L)) =
    Over.Hom.left p (IsLocalRing.closedPoint k)
  have hsq := Pt_leftHom_baseChange (k := k) (L := L) (X := C.toOver) p
  -- `Spec k` has a single point, so `specMap k L` sends the closed point of `Spec L` to
  -- the closed point of `Spec k`
  have hpt : Work.CurveBasics.Curve.specMap k L (IsLocalRing.closedPoint L) =
      IsLocalRing.closedPoint k := Subsingleton.elim _ _
  calc Work.CurveBasics.Curve.baseChangeFst C L
        (Over.Hom.left (Work.KeyLemma.Curve.Pt.baseChange (k := k) L p)
          (IsLocalRing.closedPoint L))
      = (Over.Hom.left (Work.KeyLemma.Curve.Pt.baseChange (k := k) L p) ≫
            pullback.fst C.toOver.hom (Work.CurveBasics.Curve.specMap k L))
          (IsLocalRing.closedPoint L) := (Scheme.Hom.comp_apply _ _ _).symm
    _ = (Work.CurveBasics.Curve.specMap k L ≫ Over.Hom.left p)
          (IsLocalRing.closedPoint L) :=
          congrArg (fun f : Spec (CommRingCat.of L) ⟶ C.left =>
            f (IsLocalRing.closedPoint L)) hsq
    _ = Over.Hom.left p (Work.CurveBasics.Curve.specMap k L
          (IsLocalRing.closedPoint L)) := Scheme.Hom.comp_apply _ _ _
    _ = Over.Hom.left p (IsLocalRing.closedPoint k) := by rw [hpt]

end Work.KeyLemma.BaseChange
