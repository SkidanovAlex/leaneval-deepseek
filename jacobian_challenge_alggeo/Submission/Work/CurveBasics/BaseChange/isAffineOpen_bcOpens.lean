import Mathlib
import Submission.Work.CurveBasics.BaseChangeFunctionField

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option linter.style.haveILetI false

open CategoryTheory Limits AlgebraicGeometry

namespace Work.CurveBasics.BaseChange

/-!
# The preimage of an affine open is affine under base change of a curve

For a curve `C` over `k` and a field extension `F/k`, the projection `C_F ⟶ C` is affine
(it is the base change of the affine morphism `Spec F ⟶ Spec k`), hence the preimage of an
affine open subset of `C` is affine in `C_F`.
-/

universe u in
/-- The structure morphism `Spec F ⟶ Spec k` of a field extension is affine. -/
theorem isAffineHom_specMap {k : Type u} [Field k] (F : Type u) [Field F] [Algebra k F] :
    IsAffineHom (Curve.specMap k F) :=
  isAffineHom_of_isAffine (Curve.specMap k F)

universe u in
/-- The projection `C_F ⟶ C` of a base change is an affine morphism: it is the base change
of the affine morphism `Spec F ⟶ Spec k` along `C ⟶ Spec k`. -/
instance isAffineHom_baseChangeFst {k : Type u} [Field k] (C : Curve k) (F : Type u) [Field F]
    [Algebra k F] : IsAffineHom (C.baseChangeFst F) := by
  haveI : MorphismProperty.IsStableUnderBaseChangeAlong (@IsAffineHom) C.hom :=
    @MorphismProperty.instIsStableUnderBaseChangeAlongOfIsStableUnderBaseChange Scheme.{u} _
      (@IsAffineHom) inferInstance C.left (Spec (CommRingCat.of k)) C.hom
  exact MorphismProperty.pullback_fst C.hom (Curve.specMap k F) (isAffineHom_specMap F)

universe u in
open Work.CurveBasics in
theorem isAffineOpen_bcOpens {k : Type u} [Field k] {C : Curve k} (F : Type u) [Field F]
    [Algebra k F] (W : C.left.Opens) (hW : AlgebraicGeometry.IsAffineOpen W) :
    AlgebraicGeometry.IsAffineOpen (C.bcOpens F W) := by
  show AlgebraicGeometry.IsAffineOpen ((C.baseChangeFst F) ⁻¹ᵁ W)
  exact hW.preimage (C.baseChangeFst F)

end Work.CurveBasics.BaseChange
