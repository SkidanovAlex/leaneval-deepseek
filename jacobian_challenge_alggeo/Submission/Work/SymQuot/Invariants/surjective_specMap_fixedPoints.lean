/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Surjectivity of `Spec B → Spec (B^G)` for a finite group action

For a finite group `G` acting on a commutative ring `B`, the ring of invariants `B^G` sits inside
`B` and the induced morphism of spectra `Spec B ⟶ Spec (B^G)` is surjective.  Equivalently, every
prime ideal of `B^G` is the contraction of a prime ideal of `B` (lying over).

This is the ring-theoretic shadow of the fact that the quotient map `X → X/G` is surjective, and
it is used in the construction of the quotient of a scheme by a finite group.

The proof is short but rests on two facts about invariant rings:

* `B` is integral over `B^G` (each `b : B` is a root of the monic polynomial `∏_{g : G} (X - g • b)`,
  whose coefficients lie in `B^G`); this is `Algebra.IsInvariant.isIntegral`.
* `B^G ↪ B` is injective, so `B` is a faithful `B^G`-module.

Together these give the lying-over theorem `Algebra.IsIntegral.comap_surjective`, which is precisely
the statement that `PrimeSpectrum.comap (B^G ↪ B)` is surjective.
-/
import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.SymQuot.Invariants

/-- Every element of `B` fixed by `G` lies in the subring `B^G`; that is, `B` is an invariant
extension of `B^G`. -/
instance instIsInvariantFixedPoints {G : Type*} [Group G] {B : Type*} [CommRing B]
    [MulSemiringAction G B] : Algebra.IsInvariant (FixedPoints.subring B G) B G where
  isInvariant b hb := ⟨⟨b, hb⟩, rfl⟩

/-- For a finite group `G`, the ring `B` is integral over its subring of invariants `B^G`. -/
instance instIsIntegralFixedPoints {G : Type*} [Group G] [Finite G] {B : Type*} [CommRing B]
    [MulSemiringAction G B] : Algebra.IsIntegral (FixedPoints.subring B G) B :=
  Algebra.IsInvariant.isIntegral (FixedPoints.subring B G) B G

/-- The structure map `B^G → B` is the injective inclusion `Subring.subtype`, so `B` is a faithful
`B^G`-module. -/
instance instFaithfulSMulFixedPoints {G : Type*} [Group G] {B : Type*} [CommRing B]
    [MulSemiringAction G B] : FaithfulSMul (FixedPoints.subring B G) B := by
  rw [faithfulSMul_iff_algebraMap_injective]
  exact Subtype.val_injective

/-- For a finite group `G` acting on a commutative ring `B`, the map
`Spec.map (B^G ↪ B) : Spec B ⟶ Spec (B^G)` induced by the inclusion of the invariants is
surjective on the underlying points.  Equivalently, every prime ideal of `B^G` admits a prime
ideal of `B` lying over it. -/
theorem surjective_specMap_fixedPoints {G : Type*} [Group G] [Finite G] {B : Type*} [CommRing B]
    [MulSemiringAction G B] :
    Function.Surjective
      (AlgebraicGeometry.Spec.map
        (CommRingCat.ofHom (Subring.subtype (FixedPoints.subring B G)))) := by
  change Function.Surjective (PrimeSpectrum.comap (Subring.subtype (FixedPoints.subring B G)))
  intro x
  obtain ⟨y, hy⟩ := Algebra.IsIntegral.comap_surjective (FixedPoints.subring B G) B x
  exact ⟨y, hy⟩

end Work.SymQuot.Invariants
