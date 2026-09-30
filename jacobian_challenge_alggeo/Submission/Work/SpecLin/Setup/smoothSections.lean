import Mathlib
import Submission.Work.CurveBasics.Basic
import Submission.Work.CurveBasics.BaseChange.krullDim_le_one

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Sections over an affine open of a curve are smooth over the base field

Let `C` be a smooth, proper, geometrically irreducible curve over a field `K` and let
`W ⊆ C` be an affine open subset.  Then the ring of sections `Γ(C, W)` is a smooth
`K`-algebra.

Indeed `C` is smooth of relative dimension `1` over `Spec K`, hence in particular smooth,
and a morphism of schemes is smooth precisely when all the induced maps on rings of sections
over affine open subschemes are smooth ring homomorphisms (`AlgebraicGeometry.Smooth`).
The `K`-algebra structure on `Γ(C, W)` used here is the canonical one coming from the
structure morphism `C ⟶ Spec K` (see `Work.CurveBasics.BaseChange.instAlgebraSections`),
whose structure map is exactly the composite `K ⟶ Γ(Spec K, ⊤) ⟶ Γ(C, W)`; the first map is
an isomorphism (hence smooth) and the second is smooth by the defining property of `C ⟶ Spec K`.
-/

set_option autoImplicit false

universe u

namespace Work.SpecLin.Setup

open CategoryTheory Limits AlgebraicGeometry

/-- Sections of a curve over an affine open subset form a smooth algebra over the base field. -/
theorem smoothSections {K : Type u} [Field K] (C : Work.CurveBasics.Curve K)
    (W : C.left.Opens) (hW : AlgebraicGeometry.IsAffineOpen W) :
    Algebra.Smooth K (C.left.presheaf.obj (Opposite.op W)) := by
  -- `C` is smooth over `Spec K`
  have hSm : Smooth C.hom := SmoothOfRelativeDimension.smooth (n := 1) C.hom
  -- the induced map on sections `Γ(Spec K, ⊤) ⟶ Γ(C, W)` is smooth
  have h1 : RingHom.Smooth
      (C.hom.appLE (⊤ : (Spec (CommRingCat.of K)).Opens) W le_top).hom :=
    hSm.smooth_appLE (isAffineOpen_top _) hW le_top
  -- `K ⟶ Γ(Spec K, ⊤)` is an isomorphism, hence smooth
  have h2 : RingHom.Smooth ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom) :=
    RingHom.Smooth.of_bijective (ConcreteCategory.bijective_of_isIso _)
  -- composing gives smoothness of the structure map `K ⟶ Γ(C, W)`
  have h3 : RingHom.Smooth
      ((C.hom.appLE (⊤ : (Spec (CommRingCat.of K)).Opens) W le_top).hom.comp
        (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom) :=
    RingHom.Smooth.comp h2 h1
  exact (RingHom.smooth_algebraMap).mp h3

end Work.SpecLin.Setup
