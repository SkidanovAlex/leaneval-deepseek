import Mathlib
import Submission.Work.GCBasics.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


namespace Work.GCBasics

/-- For a field extension `e : F →ₐ[K] F'`, the induced morphism of spectra
`Spec F' ⟶ Spec F` sends the (unique) closed point of `Spec F'` to the closed point of
`Spec F`.  Both spectra have a single point, so this is the instance
`IsLocalRing.comap_closedPoint` for the (local) ring homomorphism `e`. -/
theorem specOfMap_closedPoint {K : Type _} [Field K] {F F' : Type _} [Field F] [Field F']
    [Algebra K F] [Algebra K F'] (e : F →ₐ[K] F') :
    (specOfMap (K := K) e).left (IsLocalRing.closedPoint F') = IsLocalRing.closedPoint F :=
  IsLocalRing.comap_closedPoint e.toRingHom

open CategoryTheory in
theorem map_landsIn {K : Type _} [Field K] {X : Work.GCBasics.Sch K} {F F' : Type _}
    [Field F] [Field F'] [Algebra K F] [Algebra K F'] (e : F →ₐ[K] F')
    (p : Work.GCBasics.FPt X F) (U : X.left.Opens) :
    Work.GCBasics.RPt.LandsIn (Work.GCBasics.RPt.map e p) U ↔
      Work.GCBasics.RPt.LandsIn p U := by
  have hpt : (specOfMap (K := K) e).left (IsLocalRing.closedPoint F') =
      IsLocalRing.closedPoint F :=
    specOfMap_closedPoint e
  have key : (RPt.map e p).left (IsLocalRing.closedPoint F') =
      p.left (IsLocalRing.closedPoint F) := by
    calc (RPt.map e p).left (IsLocalRing.closedPoint F')
        = (Over.Hom.left (specOfMap (K := K) e) ≫ Over.Hom.left p)
            (IsLocalRing.closedPoint F') := rfl
      _ = Over.Hom.left p (Over.Hom.left (specOfMap (K := K) e)
            (IsLocalRing.closedPoint F')) := AlgebraicGeometry.Scheme.Hom.comp_apply _ _ _
      _ = Over.Hom.left p (IsLocalRing.closedPoint F) := congrArg _ hpt
  rw [RPt.landsIn_iff, RPt.landsIn_iff, key]

end Work.GCBasics
