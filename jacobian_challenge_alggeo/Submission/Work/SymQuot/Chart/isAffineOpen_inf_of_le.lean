import Mathlib
import Submission.Work.SymQuot.Chart

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open CategoryTheory Limits AlgebraicGeometry

namespace Work.SymQuot.Chart

/-- If `W₁` and `W₂` are affine open subschemes of a scheme `X` which are both contained in an
affine open `U`, then `W₁ ⊓ W₂` is again affine open.

Indeed, `W₁` and `W₂` are affine open subschemes of the affine scheme `U`, and in a scheme with
affine diagonal (here `U`, being affine, has affine diagonal) the intersection of two affine opens
is affine. -/
theorem isAffineOpen_inf_of_le {X : AlgebraicGeometry.Scheme} {W₁ W₂ U : X.Opens}
    (h₁ : W₁ ≤ U) (h₂ : W₂ ≤ U) (hU : AlgebraicGeometry.IsAffineOpen U)
    (hW₁a : AlgebraicGeometry.IsAffineOpen W₁) (hW₂a : AlgebraicGeometry.IsAffineOpen W₂) :
    AlgebraicGeometry.IsAffineOpen (W₁ ⊓ W₂) := by
  -- Work inside the affine open subscheme `U.toScheme`, which has affine diagonal.
  have : IsAffine U.toScheme := hU
  -- The preimages of `W₁` and `W₂` under the open immersion `U.ι` are affine opens of `U.toScheme`.
  have hW₁a' : IsAffineOpen (U.ι ⁻¹ᵁ W₁) :=
    hW₁a.preimage_of_isOpenImmersion U.ι (by rw [Scheme.Opens.opensRange_ι]; exact h₁)
  have hW₂a' : IsAffineOpen (U.ι ⁻¹ᵁ W₂) :=
    hW₂a.preimage_of_isOpenImmersion U.ι (by rw [Scheme.Opens.opensRange_ι]; exact h₂)
  -- Their intersection is affine because `U.toScheme` has affine diagonal.
  have hinf' : IsAffineOpen (U.ι ⁻¹ᵁ (W₁ ⊓ W₂)) := by
    rw [Scheme.Hom.preimage_inf]
    exact hW₁a'.inf hW₂a'
  -- The image of this preimage in `X` is exactly `W₁ ⊓ W₂`, since `W₁ ⊓ W₂ ≤ U`.
  have heq : U.ι ''ᵁ (U.ι ⁻¹ᵁ (W₁ ⊓ W₂)) = W₁ ⊓ W₂ := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
      inf_eq_right.mpr (inf_le_left.trans h₁)]
  rw [← heq]
  exact (Scheme.Hom.isAffineOpen_iff_of_isOpenImmersion U.ι).mpr hinf'

end Work.SymQuot.Chart
