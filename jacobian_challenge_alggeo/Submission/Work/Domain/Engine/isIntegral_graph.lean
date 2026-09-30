/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The graph closure of a partial `S`-map over an integral base is integral

Let `X` be an integral, locally Noetherian `S`-scheme, `Y` an `S`-scheme proper over `S`, and
`g : X ⇢ Y` a partial `S`-map.  This file proves that the closure of the graph of `g`
(`Work.Domain.PartialMap.graph S g`, the scheme-theoretic image of the graph morphism
`graphMap S g` into `X ×_S Y`) is an integral scheme.

The graph closure `Γ = (graphMap S g).image` is the scheme-theoretic image of the morphism
`f := graphMap S g : g.domain ⟶ X ×_S Y`, whose source is an open subscheme of the integral
scheme `X` (so reduced and irreducible), and which is an immersion (see `Work.Domain.Graph`).

* Reducedness.  For an open immersion `U ⊆ X` the graph map is an immersion; being an immersion it
  is quasi-compact, and the scheme-theoretic image of a *reduced* scheme under a quasi-compact
  morphism is reduced: over an affine open `Spec A ⊆ X ×_S Y` the sections of `Γ` embed in the
  reduced ring `Γ(f ⁻¹ᵁ Spec A)`.  This is the general lemma `isReduced_image` below.
* Irreducibility.  `toGraph : U ⟶ Γ` has dense image and `U` is irreducible, so `Γ` — which is the
  closure of the image — is irreducible.

Both are local/formal facts about the graph morphism; the properness of `Y ⟶ S` enters only through
the instance `QuasiCompact (graphMap S g)` established in `Work.Domain.Graph`.
-/
import Mathlib
import Submission.Work.Domain.Graph
import Submission.Work.Domain.Theta

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option linter.style.haveILetI false

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

universe u

namespace Work.Domain.Engine

/-! ## The scheme-theoretic image of a reduced scheme is reduced -/

/-- The quotient of a ring by the kernel of a ring homomorphism into a reduced ring is reduced:
it is (isomorphic to) the range of the homomorphism, a subring of a reduced ring. -/
lemma isReduced_quotient_ker {R S : Type*} [CommRing R] [CommRing S] [_root_.IsReduced S]
    (φ : R →+* S) : _root_.IsReduced (R ⧸ RingHom.ker φ) := by
  haveI : _root_.IsReduced ↥(RingHom.range φ) :=
    isReduced_of_injective (RingHom.range φ).subtype Subtype.val_injective
  exact isReduced_of_injective (RingHom.quotientKerEquivRange φ).toRingHom
    (RingHom.quotientKerEquivRange φ).injective

/-- For a quasi-compact morphism `f : X ⟶ Y` and an affine open `U ⊆ Y`, the scheme
`Spec (Γ(Y, U) / f.ker.ideal U)` — the piece of the scheme-theoretic image of `f` over `U` — is
reduced as soon as `X` is reduced. -/
lemma isReduced_glueDataObj_ker {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [IsReduced X]
    (U : Y.affineOpens) : IsReduced (f.ker.glueDataObj U) := by
  rw [Scheme.IdealSheafData.glueDataObj]
  rw [affine_isReduced_iff]
  rw [Scheme.Hom.ker_apply]
  exact isReduced_quotient_ker (f.app U).hom

/-- **The scheme-theoretic image of a reduced scheme is reduced.**

For a quasi-compact morphism `f : X ⟶ Y` with `X` reduced, the scheme-theoretic image `f.image` is
reduced.  Indeed `f.image` is covered by the affines `Spec (Γ(Y, U) / f.ker.ideal U)` for
`U ⊆ Y` affine open (`IdealSheafData.subschemeCover`); since `f` is quasi-compact,
`f.ker.ideal U` is the kernel of the restriction map on sections, so these rings are subrings of
the reduced ring `Γ(X, f ⁻¹ᵁ U)`, hence reduced. -/
lemma isReduced_image {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [IsReduced X] :
    IsReduced f.image := by
  haveI : ∀ i : f.ker.subschemeCover.openCover.I₀,
      IsReduced (f.ker.subschemeCover.openCover.X i) := fun i => by
    show IsReduced (f.ker.glueDataObj i)
    exact isReduced_glueDataObj_ker f i
  exact IsReduced.of_openCover f.image f.ker.subschemeCover.openCover

/-! ## The graph closure -/

/-- **The closure of the graph of an `S`-partial map out of an integral scheme is integral.** -/
theorem isIntegral_graph {S X Y : AlgebraicGeometry.Scheme} [X.Over S] [Y.Over S]
    [AlgebraicGeometry.IsIntegral X] [AlgebraicGeometry.IsLocallyNoetherian X]
    [AlgebraicGeometry.IsProper (Work.Domain.overHom S Y)]
    (g : AlgebraicGeometry.Scheme.PartialMap X Y)
    [hg : AlgebraicGeometry.Scheme.PartialMap.IsOver S g] :
    AlgebraicGeometry.IsIntegral (Work.Domain.PartialMap.graph S g) := by
  -- the graph map is quasi-compact, so `IsDominant (toGraph S g)` is available
  haveI hred : IsReduced (Work.Domain.PartialMap.graph S g) :=
    isReduced_image (Work.Domain.PartialMap.graphMap S g)
  haveI hirr : IrreducibleSpace (Work.Domain.PartialMap.graph S g) := by
    rw [irreducibleSpace_def]
    -- the domain of `g` is an open subscheme of the integral scheme `X`, hence irreducible
    haveI : IsIntegral g.domain.toScheme := isIntegral_of_isOpenImmersion g.domain.ι
    have hU : IsIrreducible (⊤ : Set g.domain.toScheme) := (irreducibleSpace_def _).mp inferInstance
    -- the image of the irreducible domain under `toGraph` is irreducible ...
    have hrange : IsIrreducible (Set.range ⇑(Work.Domain.PartialMap.toGraph S g)) := by
      have := IsIrreducible.image hU (⇑(Work.Domain.PartialMap.toGraph S g))
        (Work.Domain.PartialMap.toGraph S g).continuous.continuousOn
      simpa [Set.image_univ] using this
    -- ... and dense, and the graph closure is its closure
    have hdense : closure (Set.range ⇑(Work.Domain.PartialMap.toGraph S g)) = Set.univ := by
      rw [← denseRange_iff_closure_range]
      exact IsDominant.denseRange
    show IsIrreducible (Set.univ : Set (Work.Domain.PartialMap.graph S g))
    rw [← hdense]
    exact hrange.closure
  exact isIntegral_of_irreducibleSpace_of_isReduced _

end Work.Domain.Engine
