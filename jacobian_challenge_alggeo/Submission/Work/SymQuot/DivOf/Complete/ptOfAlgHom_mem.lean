import Mathlib
import Submission.Work.SymQuot.DivOf.Complete.Setup

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


universe u

namespace Work.SymQuot.DivOf.Complete

open CategoryTheory Limits AlgebraicGeometry in
theorem ptOfAlgHom_mem {K : Type u} [Field K] {C : Work.CurveBasics.Curve K} {V : C.left.Opens}
    (hV : IsAffineOpen V) {S : Type u} [CommRing S] [Algebra K S]
    (κ : Γ(C.left, V) →ₐ[K] S) :
    ⊤ ≤ (ptOfAlgHom C hV κ).left ⁻¹ᵁ V := by
  -- On the level of schemes, `ptOfAlgHom C hV κ` is `Spec.map κ ≫ hV.fromSpec`, and
  -- `hV.fromSpec ⁻¹ᵁ V = ⊤` because the range of `hV.fromSpec` is exactly `V`.
  rw [show Over.Hom.left (ptOfAlgHom C hV κ) =
    (Work.SpecLin.specOfMap (K := K) κ).left ≫ hV.fromSpec from rfl]
  rw [Scheme.Hom.comp_preimage, IsAffineOpen.fromSpec_preimage_self, Scheme.Hom.preimage_top]

end Work.SymQuot.DivOf.Complete
