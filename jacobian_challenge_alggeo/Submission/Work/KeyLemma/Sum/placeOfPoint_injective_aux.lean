/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Injectivity of `placeOfPoint`

A `k`-point of a curve `C` is a section `p : Spec k ⟶ C` of the structure morphism, and
`Curve.placeOfPoint C p` is the closed point of `C` which is the image of `p`.  This file
proves that a `k`-point of `C` is *determined* by its image point:

> `Function.Injective (Curve.placeOfPoint C)`.

The mathematical content is that a `k`-point gives a `k`-algebra retraction
`κ(x) ⟶ k` of the residue field extension `k ⟶ κ(x)` at its image point `x`, and such a
retraction is unique (it is an isomorphism with inverse the structure map, hence
"the" inverse).  The proof below implements this with the `Spec ⊣ Γ` technology:

* if `π : X ⟶ Spec k` and `p : Spec k ⟶ X` with `p ≫ π = 𝟙`, then `p` factors through
  `Spec (κ(p ⋆))`, and the induced map `ρ_p = (Spec κ(p⋆) ⟶ X ≫ π)` is a morphism of affine
  schemes, hence `ρ_p = Spec.map γ_p` for `γ_p = Spec.preimage ρ_p : k ⟶ κ(p ⋆)`;
* from `Spec.map (α_p) ≫ ρ_p = 𝟙` (where `α_p` is the residue field map of `p`, the second
  component of `Scheme.SpecToEquivOfField`) we get `γ_p ≫ α_p = 𝟙`, i.e. `α_p ∘ γ_p = id`;
* for two points with the same image, the two `γ`'s differ by `Scheme.residueFieldCongr`, so
  the uniqueness of a left inverse of a fixed `γ : k ⟶ K` (a ring hom from a field) gives
  `α_p = α_q` up to `residueFieldCongr`, and `Scheme.SpecToEquivOfField_eq_iff` concludes.
-/
import Mathlib
import Submission.Work.KeyLemma.Sum

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


namespace Work.KeyLemma.Sum

open CategoryTheory AlgebraicGeometry

universe u

/-- Two ring homomorphisms `K ⟶ k` out of a field `K` which both invert the same
`γ : k ⟶ K` on the left are equal.  Indeed, `α : K ⟶ k` with `α ∘ γ = id` is bijective
(being injective as a map of fields and surjective because `α ∘ γ` is onto), with inverse
`γ`; so both `α₁` and `α₂` equal the inverse of `γ`. -/
lemma field_ringHom_ext {k K : Type*} [Field k] [Field K] (γ : k →+* K)
    (α₁ α₂ : K →+* k) (h₁ : α₁.comp γ = RingHom.id k) (h₂ : α₂.comp γ = RingHom.id k) :
    α₁ = α₂ := by
  ext x
  have hx : γ (α₁ x) = x := by
    apply α₁.injective
    rw [← RingHom.comp_apply, h₁]
    simp
  calc α₁ x = α₂ (γ (α₁ x)) := by rw [← RingHom.comp_apply, h₂]; simp
    _ = α₂ x := by rw [hx]

/-- **A section of `π : X ⟶ Spec k` over a field `k` is determined by its image point.**

If `f, g : Spec k ⟶ X` satisfy `f ≫ π = 𝟙 = g ≫ π` and `f` and `g` have the same value at
the closed point of `Spec k`, then `f = g`. -/
lemma eq_of_comp_eq_id {k : Type u} [Field k] {X : Scheme}
    (π : X ⟶ Spec (CommRingCat.of k))
    {f g : Spec (CommRingCat.of k) ⟶ X}
    (hf : f ≫ π = 𝟙 (Spec (CommRingCat.of k)))
    (hg : g ≫ π = 𝟙 (Spec (CommRingCat.of k)))
    (hpt : f (IsLocalRing.closedPoint k) = g (IsLocalRing.closedPoint k)) : f = g := by
  -- `p ≫ π = 𝟙` for the sections; the `Spec`-level statement of the section property.
  have hstep : ∀ (p : Spec (CommRingCat.of k) ⟶ X), p ≫ π = 𝟙 (Spec (CommRingCat.of k)) →
      Spec.map (Scheme.descResidueField (Scheme.stalkClosedPointTo p))
        ≫ (X.fromSpecResidueField (p (IsLocalRing.closedPoint k)) ≫ π) =
        𝟙 (Spec (CommRingCat.of k)) := by
    intro p hp
    rw [← Category.assoc, Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField k X p, hp]
  -- `γ_f` is the ring map of `Spec κ(f ⋆) ⟶ Spec k`; it is a left inverse of `α_f`.
  have hγf : Spec.preimage (X.fromSpecResidueField (f (IsLocalRing.closedPoint k)) ≫ π)
      ≫ Scheme.descResidueField (Scheme.stalkClosedPointTo f) = 𝟙 (CommRingCat.of k) := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_id, Spec.map_preimage]
    exact hstep f hf
  have hγg : Spec.preimage (X.fromSpecResidueField (g (IsLocalRing.closedPoint k)) ≫ π)
      ≫ Scheme.descResidueField (Scheme.stalkClosedPointTo g) = 𝟙 (CommRingCat.of k) := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_id, Spec.map_preimage]
    exact hstep g hg
  -- The two `Spec κ(⋆) ⟶ Spec k` morphisms differ by `residueFieldCongr`.
  have hρgf : X.fromSpecResidueField (g (IsLocalRing.closedPoint k)) ≫ π
      = Spec.map ((X.residueFieldCongr hpt).hom)
        ≫ (X.fromSpecResidueField (f (IsLocalRing.closedPoint k)) ≫ π) := by
    rw [← Category.assoc, Scheme.residueFieldCongr_fromSpecResidueField (X := X) hpt]
  have hγgf : Spec.preimage (X.fromSpecResidueField (g (IsLocalRing.closedPoint k)) ≫ π)
      = Spec.preimage (X.fromSpecResidueField (f (IsLocalRing.closedPoint k)) ≫ π)
        ≫ (X.residueFieldCongr hpt).hom := by
    apply Spec.map_injective
    rw [Spec.map_preimage, Spec.map_comp, Spec.map_preimage, hρgf]
  -- Convert the `γ`-relations to ring hom statements.
  have h₁ : (Scheme.descResidueField (Scheme.stalkClosedPointTo f)).hom.comp
      (Spec.preimage (X.fromSpecResidueField (f (IsLocalRing.closedPoint k)) ≫ π)).hom
      = RingHom.id k := by
    have h := congrArg CommRingCat.Hom.hom hγf
    rw [CommRingCat.hom_comp, CommRingCat.hom_id] at h
    exact h
  have h₂ : ((X.residueFieldCongr hpt).hom ≫
        Scheme.descResidueField (Scheme.stalkClosedPointTo g)).hom.comp
      (Spec.preimage (X.fromSpecResidueField (f (IsLocalRing.closedPoint k)) ≫ π)).hom
      = RingHom.id k := by
    have hg' := congrArg CommRingCat.Hom.hom hγg
    rw [CommRingCat.hom_comp, CommRingCat.hom_id] at hg'
    have hγ' := congrArg CommRingCat.Hom.hom hγgf
    rw [CommRingCat.hom_comp] at hγ'
    rw [hγ'] at hg'
    rw [← RingHom.comp_assoc] at hg'
    rw [CommRingCat.hom_comp]
    exact hg'
  -- Uniqueness of the left inverse of `γ_f` gives the comparison of residue field maps.
  have hαhom : (Scheme.descResidueField (Scheme.stalkClosedPointTo f)).hom
      = ((X.residueFieldCongr hpt).hom ≫
          Scheme.descResidueField (Scheme.stalkClosedPointTo g)).hom :=
    field_ringHom_ext _ _ _ h₁ h₂
  have hα : Scheme.descResidueField (Scheme.stalkClosedPointTo f)
      = (X.residueFieldCongr hpt).hom ≫ Scheme.descResidueField (Scheme.stalkClosedPointTo g) :=
    CommRingCat.hom_ext hαhom
  -- Finally identify the two `Spec k`-points.
  apply (Scheme.SpecToEquivOfField k X).injective
  rw [Scheme.SpecToEquivOfField_eq_iff]
  exact ⟨hpt, hα⟩

theorem placeOfPoint_injective_aux {k : Type u} [Field k] (C : Work.CurveBasics.Curve k) :
    Function.Injective (Work.KeyLemma.Curve.placeOfPoint C) := by
  intro p q hpq
  have hpt : Work.KeyLemma.Curve.Pt.leftHom p (IsLocalRing.closedPoint k)
      = Work.KeyLemma.Curve.Pt.leftHom q (IsLocalRing.closedPoint k) := by
    have h := congrArg Subtype.val hpq
    simpa using h
  have hleft : Work.KeyLemma.Curve.Pt.leftHom p = Work.KeyLemma.Curve.Pt.leftHom q :=
    eq_of_comp_eq_id C.hom (Work.KeyLemma.Curve.Pt.leftHom_comp p)
      (Work.KeyLemma.Curve.Pt.leftHom_comp q) hpt
  exact Over.OverMorphism.ext hleft

end Work.KeyLemma.Sum
