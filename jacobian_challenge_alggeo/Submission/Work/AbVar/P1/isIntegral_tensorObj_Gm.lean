import Mathlib
import Submission.Work.AbVar.Basic
import Submission.Work.AbVar.TestObjects
import Submission.Work.AbVar.TestObjects.gm_geometricallyIntegral

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Integrality of `X ⊗ 𝔾_m`

If `X` is a scheme over a field `k` which is geometrically integral over `k`, then
`X ×_k 𝔾_m` is integral.

The reason is entirely structural:

* `𝔾_m = Spec k[T;T⁻¹]` is geometrically integral over `k`
  (`Work.AbVar.TestObjects.gm_geometricallyIntegral`), and the target `Spec k` is a
  one-point integral scheme, so `𝔾_m` itself is integral and locally noetherian
  (being locally of finite type over `k`).
* `X ×_k 𝔾_m` is the fibre product of `X.hom` and `(𝔾_m).hom`; the projection to the
  second factor is geometrically integral (base change of `X.hom`), flat and universally
  open (every morphism onto a one-point integral scheme is) and the target `𝔾_m` is
  integral and locally noetherian. Hence `X ×_k 𝔾_m` is integral.
-/

set_option linter.style.haveILetI false

namespace Work.AbVar.P1

open CategoryTheory in
theorem isIntegral_tensorObj_Gm {k : Type*} [Field k] {X : Work.AbVar.Sch k}
    [AlgebraicGeometry.IsProper X.hom] [AlgebraicGeometry.GeometricallyIntegral X.hom] :
    AlgebraicGeometry.IsIntegral (MonoidalCategoryStruct.tensorObj X (Work.AbVar.Gm k)).left := by
  -- `𝔾_m` is geometrically integral over `k`.
  haveI : AlgebraicGeometry.GeometricallyIntegral (Work.AbVar.Gm k).hom :=
    Work.AbVar.TestObjects.gm_geometricallyIntegral
  -- Over the one-point integral scheme `Spec k`, geometric integrality is integrality.
  haveI : AlgebraicGeometry.IsIntegral (Work.AbVar.Gm k).left :=
    AlgebraicGeometry.GeometricallyIntegral.isIntegral_of_subsingleton (Work.AbVar.Gm k).hom
  -- `𝔾_m = Spec k[T;T⁻¹]` is locally of finite type over `k`, hence locally noetherian.
  haveI : AlgebraicGeometry.LocallyOfFiniteType (Work.AbVar.Gm k).hom :=
    Work.AbVar.gm_locallyOfFiniteType k
  haveI : AlgebraicGeometry.IsLocallyNoetherian (Work.AbVar.Gm k).left :=
    AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian (Work.AbVar.Gm k).hom
  -- `(X ⊗ 𝔾_m).left` is by definition the fibre product `X ×_k 𝔾_m`.
  change AlgebraicGeometry.IsIntegral (Limits.pullback X.hom (Work.AbVar.Gm k).hom)
  -- Everything over the one-point integral scheme `Spec k` is flat and universally open,
  -- so `X ×_k 𝔾_m` is integral as the source of the geometrically integral, flat,
  -- universally open projection to the integral, locally noetherian scheme `𝔾_m`.
  exact inferInstance

end Work.AbVar.P1
