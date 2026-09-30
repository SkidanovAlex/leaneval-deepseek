import Mathlib
import Submission.Work.SymQuot.Chart
import Submission.Work.SymQuot.Invariants.fixedPoints_isIntegral
import Submission.Work.SymQuot.Invariants.surjective_specMap_fixedPoints

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option linter.style.haveILetI false

open scoped AlgebraicGeometry

namespace Work.SymQuot.Chart

theorem chartMap_isIntegralHom {G : Type*} [Group G] [Finite G] {X : AlgebraicGeometry.Scheme}
    (A : Work.SymQuot.GAction G X) {U : X.Opens} (hU : AlgebraicGeometry.IsAffineOpen U)
    (hUi : A.IsInvariantOpen U) :
    AlgebraicGeometry.IsIntegralHom (A.chartMap U hUi) := by
  rw [Work.SymQuot.GAction.chartMap]
  -- `chartMap U = U.toSpecΓ ≫ Spec.map (Subring.subtype Γ(X,U)^G ↪ Γ(X,U))`.
  letI : MulSemiringAction G Γ(X, U) := A.sectionMulSemiringAction U hUi
  -- `Γ(X,U)` is integral over its invariants, since `G` is finite.
  haveI hInt : Algebra.IsIntegral (A.invariants U hUi) Γ(X, U) :=
    Work.SymQuot.Invariants.fixedPoints_isIntegral
  -- Hence `Spec.map` of the inclusion of the invariants is an integral morphism.
  haveI hspec : AlgebraicGeometry.IsIntegralHom
      (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (A.invariants U hUi).subtype)) := by
    rw [AlgebraicGeometry.IsIntegralHom.SpecMap_iff]
    rw [show (A.invariants U hUi).subtype = algebraMap (A.invariants U hUi) Γ(X, U) from rfl]
    exact algebraMap_isIntegral_iff.mpr hInt
  -- `U.toSpecΓ` is an isomorphism because `U` is affine, hence integral as well.
  haveI : CategoryTheory.IsIso U.toSpecΓ := by rw [← hU.isoSpec_hom]; infer_instance
  infer_instance

end Work.SymQuot.Chart
