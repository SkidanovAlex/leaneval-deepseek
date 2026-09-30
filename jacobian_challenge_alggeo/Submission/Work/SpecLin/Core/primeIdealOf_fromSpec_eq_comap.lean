import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open AlgebraicGeometry CategoryTheory

universe u

namespace Work.SpecLin.Core

/-- **(D1c-geom)** The prime of a point of an affine chart given by a ring map to a field. -/
theorem primeIdealOf_fromSpec_eq_comap {X : AlgebraicGeometry.Scheme}
    (U : X.Opens) (hU : AlgebraicGeometry.IsAffineOpen U) {k : Type u} [Field k]
    (ψ : X.presheaf.obj (Opposite.op U) →+* k)
    (z : AlgebraicGeometry.Spec (CommRingCat.of k)) :
    hU.primeIdealOf ⟨hU.fromSpec (AlgebraicGeometry.Spec.map (CommRingCat.ofHom ψ) z),
        by simpa [AlgebraicGeometry.IsAffineOpen.range_fromSpec] using
          Set.mem_range_self (f := hU.fromSpec)
            (AlgebraicGeometry.Spec.map (CommRingCat.ofHom ψ) z)⟩
      = PrimeSpectrum.comap ψ z := by
  simp only [AlgebraicGeometry.IsAffineOpen.primeIdealOf]
  have h : (⟨hU.fromSpec (AlgebraicGeometry.Spec.map (CommRingCat.ofHom ψ) z),
        by simpa [AlgebraicGeometry.IsAffineOpen.range_fromSpec] using
          Set.mem_range_self (f := hU.fromSpec)
            (AlgebraicGeometry.Spec.map (CommRingCat.ofHom ψ) z)⟩ : ↑U)
      = hU.isoSpec.inv (AlgebraicGeometry.Spec.map (CommRingCat.ofHom ψ) z) := by
    apply Subtype.ext
    rfl
  rw [h, ← Scheme.Hom.comp_apply, hU.isoSpec.inv_hom_id]
  rfl

end Work.SpecLin.Core
