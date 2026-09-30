import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false



universe u

open CategoryTheory
namespace Work.Charts

/-- **A section of `X ⟶ Spec F` is determined by its value at the closed point.**

Two sections `g h : Spec F ⟶ X` of the structure morphism `p : X ⟶ Spec F` which agree on
the (unique) point `closedPoint F` of `Spec F` are equal.

The point is that for a section the point `x = g (closedPoint F)` is an `F`-rational point: the
structure morphism induces `F ≅ κ(x)` and the section induces the inverse isomorphism, so the
data `x ↦ (κ(x) ⟶ F)` classifying `Spec F ⟶ X` is completely forced.  Formally we use
`Scheme.SpecToEquivOfField` (morphisms `Spec F ⟶ X` correspond to points `x` together with field
maps `κ(x) → F`) and the identity `Scheme.descResidueField (Scheme.stalkClosedPointTo g)` as the
residue field map of `g`. -/
theorem section_eq_of_closedPoint_eq {F : Type u} [Field F] {X : AlgebraicGeometry.Scheme.{u}}
    (p : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of F))
    (g h : AlgebraicGeometry.Spec (CommRingCat.of F) ⟶ X)
    (hg : CategoryTheory.CategoryStruct.comp g p =
      CategoryTheory.CategoryStruct.id (AlgebraicGeometry.Spec (CommRingCat.of F)))
    (hh : CategoryTheory.CategoryStruct.comp h p =
      CategoryTheory.CategoryStruct.id (AlgebraicGeometry.Spec (CommRingCat.of F)))
    (hpt : g (IsLocalRing.closedPoint F) = h (IsLocalRing.closedPoint F)) : g = h := by
  set Dg := AlgebraicGeometry.Scheme.descResidueField
    (AlgebraicGeometry.Scheme.stalkClosedPointTo g) with hDg
  set Dh := AlgebraicGeometry.Scheme.descResidueField
    (AlgebraicGeometry.Scheme.stalkClosedPointTo h) with hDh
  set I := X.fromSpecResidueField (g (IsLocalRing.closedPoint F)) ≫ p with hI
  set I' := X.fromSpecResidueField (h (IsLocalRing.closedPoint F)) ≫ p with hI'
  set c := AlgebraicGeometry.Scheme.residueFieldCongr hpt with hc
  -- `g` (resp. `h`) is the composite `Spec.map Dg ≫ fromSpecResidueField`, which is a
  -- section of `I` (resp. `I'`).
  have hA : AlgebraicGeometry.Spec.map Dg ≫ I =
      𝟙 (AlgebraicGeometry.Spec (CommRingCat.of F)) := by
    rw [hI, ← CategoryTheory.Category.assoc, hDg,
      AlgebraicGeometry.Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField, hg]
  have hB : AlgebraicGeometry.Spec.map Dh ≫ I' =
      𝟙 (AlgebraicGeometry.Spec (CommRingCat.of F)) := by
    rw [hI', ← CategoryTheory.Category.assoc, hDh,
      AlgebraicGeometry.Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField, hh]
  -- and `I` and `I'` differ by the residue field comparison `c`.
  have hC : AlgebraicGeometry.Spec.map c.hom ≫ I = I' := by
    rw [hI, hI', hc, ← CategoryTheory.Category.assoc,
      AlgebraicGeometry.Scheme.residueFieldCongr_fromSpecResidueField]
  -- Extract the induced ring maps `ι : F ⟶ κ(x)`, `ι' : F ⟶ κ(x')`.
  set ι := AlgebraicGeometry.Spec.preimage I with hιdef
  set ι' := AlgebraicGeometry.Spec.preimage I' with hι'def
  have hι : AlgebraicGeometry.Spec.map ι = I := AlgebraicGeometry.Spec.map_preimage I
  have hι' : AlgebraicGeometry.Spec.map ι' = I' := AlgebraicGeometry.Spec.map_preimage I'
  have hAring : ι ≫ Dg = 𝟙 (CommRingCat.of F) := by
    rw [← AlgebraicGeometry.Spec.map_inj, AlgebraicGeometry.Spec.map_comp, hι, hA,
      AlgebraicGeometry.Spec.map_id]
  have hBring : ι' ≫ Dh = 𝟙 (CommRingCat.of F) := by
    rw [← AlgebraicGeometry.Spec.map_inj, AlgebraicGeometry.Spec.map_comp, hι', hB,
      AlgebraicGeometry.Spec.map_id]
  have hCring : ι ≫ c.hom = ι' := by
    rw [← AlgebraicGeometry.Spec.map_inj, AlgebraicGeometry.Spec.map_comp, hι, hC, hι']
  -- Hence `ι ≫ (c.hom ≫ Dh) = 𝟙` too.
  have hIA : ι ≫ (c.hom ≫ Dh) = 𝟙 (CommRingCat.of F) := by
    rw [← CategoryTheory.Category.assoc, hCring, hBring]
  -- The two retractions `Dg` and `c.hom ≫ Dh` of the monomorphism `ι` (a map of fields)
  -- therefore agree.
  have h1 : ∀ w : ↥(CommRingCat.of F), (c.hom ≫ Dh).hom (ι.hom w) = w := by
    intro w
    have hz := DFunLike.congr_fun (CommRingCat.hom_ext_iff.mp hIA) w
    simpa [CommRingCat.comp_apply] using hz
  have h2 : ∀ w : ↥(CommRingCat.of F), Dg.hom (ι.hom w) = w := by
    intro w
    have hz := DFunLike.congr_fun (CommRingCat.hom_ext_iff.mp hAring) w
    simpa [CommRingCat.comp_apply] using hz
  have hAi : (c.hom ≫ Dh) ≫ ι =
      𝟙 (X.residueField (g (IsLocalRing.closedPoint F))) := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro z
    have hinj : Function.Injective (c.hom ≫ Dh).hom := RingHom.injective _
    apply hinj
    rw [CommRingCat.comp_apply]
    exact h1 ((c.hom ≫ Dh).hom z)
  have hDi : Dg ≫ ι = 𝟙 (X.residueField (g (IsLocalRing.closedPoint F))) := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro z
    have hinj : Function.Injective Dg.hom := RingHom.injective _
    apply hinj
    rw [CommRingCat.comp_apply]
    exact h2 (Dg.hom z)
  have key : Dg = c.hom ≫ Dh := by
    calc Dg = Dg ≫ 𝟙 (CommRingCat.of F) := (CategoryTheory.Category.comp_id _).symm
      _ = Dg ≫ (ι ≫ (c.hom ≫ Dh)) := by rw [hIA]
      _ = (Dg ≫ ι) ≫ (c.hom ≫ Dh) := by rw [CategoryTheory.Category.assoc]
      _ = 𝟙 _ ≫ (c.hom ≫ Dh) := by rw [hDi]
      _ = c.hom ≫ Dh := CategoryTheory.Category.id_comp _
  calc g = AlgebraicGeometry.Spec.map Dg ≫
        X.fromSpecResidueField (g (IsLocalRing.closedPoint F)) :=
        (AlgebraicGeometry.Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField
          F X g).symm
    _ = AlgebraicGeometry.Spec.map (c.hom ≫ Dh) ≫
        X.fromSpecResidueField (g (IsLocalRing.closedPoint F)) := by rw [key]
    _ = AlgebraicGeometry.Spec.map Dh ≫ AlgebraicGeometry.Spec.map c.hom ≫
        X.fromSpecResidueField (g (IsLocalRing.closedPoint F)) := by
        rw [AlgebraicGeometry.Spec.map_comp, CategoryTheory.Category.assoc]
    _ = AlgebraicGeometry.Spec.map Dh ≫
        X.fromSpecResidueField (h (IsLocalRing.closedPoint F)) := by
        rw [hc, AlgebraicGeometry.Scheme.residueFieldCongr_fromSpecResidueField]
    _ = h := AlgebraicGeometry.Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField
        F X h

end Work.Charts
