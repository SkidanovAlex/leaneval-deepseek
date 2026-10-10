import Mathlib
import Submission.Work.Motivic.Defs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option linter.style.haveILetI false

namespace Work.Motivic

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme MotivicInvariants

/-
# Every birational map has a partial-isomorphism representative

`PartialIso.toBirationalMap` (in `ChallengeDeps.lean`) sends a partial isomorphism
`i : X.PartialIso Y` (an iso between dense opens) to the `BirationalMap` with `hom := i.toRationalMap`
and `inv := i.symm.toRationalMap`. The requested result is the converse: every `BirationalMap`
`φ : X ⇢ Y` between irreducible schemes is *represented* by a partial isomorphism.

## Proof route
Work with representatives:
 * take `a : X.PartialMap Y` with `a.toRationalMap = φ.hom` and `b : Y.PartialMap X` with
   `b.toRationalMap = φ.inv`;
 * `a.comp b ≃ id_X` and `b.comp a ≃ id_Y`, giving dense opens `W₁ ⊆ X`, `W₂ ⊆ Y` on which the
   composites are the respective identity *morphisms*;
 * shrink to a pair of dense opens `U ⊆ X`, `V ⊆ Y` on which `a` and `b` restrict to mutually
   inverse isomorphisms, and assemble the `PartialIso`.
-/

theorem exists_partialIso_toBirationalMap {X Y : Scheme.{0}} [IrreducibleSpace X]
    [IrreducibleSpace Y] (φ : X.BirationalMap Y) : ∃ i : X.PartialIso Y, i.toBirationalMap = φ := by
  classical
  let a : X.PartialMap Y := φ.hom.representative
  let b : Y.PartialMap X := φ.inv.representative
  have ha : a.toRationalMap = φ.hom := RationalMap.toRationalMap_representative φ.hom
  have hb : b.toRationalMap = φ.inv := RationalMap.toRationalMap_representative φ.inv
  haveI hda : IsDominant a.hom :=
    (PartialMap.isDominant_toRationalMap_iff a).mp (by rw [ha]; infer_instance)
  haveI hdb : IsDominant b.hom :=
    (PartialMap.isDominant_toRationalMap_iff b).mp (by rw [hb]; infer_instance)
  -- Step 1: the composites of the two representatives are equivalent to the identities.
  have hcomp₁ : a.toRationalMap.comp b.toRationalMap = φ.hom.comp φ.inv := by simp only [ha, hb]
  have hcomp₂ : b.toRationalMap.comp a.toRationalMap = φ.inv.comp φ.hom := by simp only [hb, ha]
  have h1 : (a.comp b).equiv (PartialMap.id X) := by
    rw [← PartialMap.toRationalMap_eq_iff, ← RationalMap.toRationalMap_comp (f := a) (g := b),
      hcomp₁, BirationalMap.hom_comp_inv_id]
  have h2 : (b.comp a).equiv (PartialMap.id Y) := by
    rw [← PartialMap.toRationalMap_eq_iff, ← RationalMap.toRationalMap_comp (f := b) (g := a),
      hcomp₂, BirationalMap.inv_comp_hom_id]
  -- Step 2: unpack the two equivalences into morphism identities on dense opens.
  obtain ⟨W₁, hW₁d, hW₁l, hW₁r, he₁⟩ := h1
  obtain ⟨W₂, hW₂d, hW₂l, hW₂r, he₂⟩ := h2
  -- the two opens are the comp-domains, made explicit
  let hW₁l' : W₁ ≤ a.domain.ι ''ᵁ (a.hom ⁻¹ᵁ b.domain) := hW₁l
  let hW₂l' : W₂ ≤ b.domain.ι ''ᵁ (b.hom ⁻¹ᵁ a.domain) := hW₂l
  -- the two factorisations of `a.hom` (resp. `b.hom`) through the other's domain
  let p : (a.domain.ι ''ᵁ (a.hom ⁻¹ᵁ b.domain)).toScheme ⟶ (b.domain).toScheme :=
    (a.domain.ι.isoImage (a.hom ⁻¹ᵁ b.domain)).inv ≫ (a.hom ∣_ b.domain)
  let q : (b.domain.ι ''ᵁ (b.hom ⁻¹ᵁ a.domain)).toScheme ⟶ (a.domain).toScheme :=
    (b.domain.ι.isoImage (b.hom ⁻¹ᵁ a.domain)).inv ≫ (b.hom ∣_ a.domain)
  have MX : X.homOfLE hW₁l' ≫ p ≫ b.hom = W₁.ι := by
    have h := he₁
    rw [PartialMap.restrict_hom, PartialMap.restrict_hom, PartialMap.id_hom,
      Scheme.topIso_hom] at h
    rw [show X.homOfLE hW₁r ≫ (⊤ : X.Opens).ι = W₁.ι from Scheme.homOfLE_ι X hW₁r] at h
    rw [show X.homOfLE hW₁l = X.homOfLE hW₁l' from congrArg _ (Subsingleton.elim _ _),
      show (a.comp b).hom = p ≫ b.hom from rfl] at h
    exact h
  have MY : Y.homOfLE hW₂l' ≫ q ≫ a.hom = W₂.ι := by
    have h := he₂
    rw [PartialMap.restrict_hom, PartialMap.restrict_hom, PartialMap.id_hom,
      Scheme.topIso_hom] at h
    rw [show Y.homOfLE hW₂r ≫ (⊤ : Y.Opens).ι = W₂.ι from Scheme.homOfLE_ι Y hW₂r] at h
    rw [show Y.homOfLE hW₂l = Y.homOfLE hW₂l' from congrArg _ (Subsingleton.elim _ _),
      show (b.comp a).hom = q ≫ a.hom from rfl] at h
    exact h
  -- Step 3: the two dense opens
  let V : Y.Opens := W₂ ⊓ (b.domain.ι ''ᵁ (b.hom ⁻¹ᵁ W₁))
  have hVd : Dense (V : Set Y) := by
    have hd₂ : Dense ((b.domain.ι ''ᵁ (b.hom ⁻¹ᵁ W₁)) : Set Y) :=
      (b.domain.ι ''ᵁ (b.hom ⁻¹ᵁ W₁)).2.dense (by
        obtain ⟨x, hxW, hxr⟩ :=
          b.hom.denseRange.inter_open_nonempty (W₁ : Set X) W₁.2 hW₁d.nonempty
        obtain ⟨e, rfl⟩ := hxr
        exact ⟨b.domain.ι e, ⟨e, hxW, rfl⟩⟩)
    simpa only [TopologicalSpace.Opens.coe_inf, V] using
      hW₂d.inter_of_isOpen_left hd₂ W₂.2
  let U : X.Opens := W₁ ⊓ (a.domain.ι ''ᵁ (a.hom ⁻¹ᵁ V))
  have hUd : Dense (U : Set X) := by
    have hd₂ : Dense ((a.domain.ι ''ᵁ (a.hom ⁻¹ᵁ V)) : Set X) :=
      (a.domain.ι ''ᵁ (a.hom ⁻¹ᵁ V)).2.dense (by
        obtain ⟨x, hxA, hxr⟩ :=
          a.hom.denseRange.inter_open_nonempty (V : Set Y) V.2 hVd.nonempty
        obtain ⟨d, rfl⟩ := hxr
        exact ⟨a.domain.ι d, ⟨d, hxA, rfl⟩⟩)
    simpa only [TopologicalSpace.Opens.coe_inf, U] using
      hW₁d.inter_of_isOpen_left hd₂ W₁.2
  -- Step 4: the relevant containments
  have hVleE : V ≤ b.domain :=
    ((inf_le_left : V ≤ W₂).trans hW₂l').trans (b.domain.ι_image_le (b.hom ⁻¹ᵁ a.domain))
  have hUleD : U ≤ a.domain :=
    ((inf_le_left : U ≤ W₁).trans hW₁l').trans (a.domain.ι_image_le (a.hom ⁻¹ᵁ b.domain))
  -- Step 5: the morphism α₀ (the restriction of `a` to `U`) and its range
  let α₀ : U.toScheme ⟶ Y := X.homOfLE hUleD ≫ a.hom
  have hαrange : Set.range (⇑α₀) ⊆ Set.range (⇑V.ι) := by
    rw [Scheme.Opens.range_ι]
    rintro y ⟨x, rfl⟩
    have hx : ⇑(X.homOfLE hUleD) x ∈ (a.hom ⁻¹ᵁ V : Set ↑(a.domain)) := by
      refine (Scheme.Hom.apply_mem_image_iff a.domain.ι).mp ?_
      have hmem : ⇑U.ι x ∈ (a.domain.ι ''ᵁ (a.hom ⁻¹ᵁ V) : Set X) :=
        (inf_le_right : U ≤ a.domain.ι ''ᵁ (a.hom ⁻¹ᵁ V)) x.2
      rw [← Scheme.homOfLE_ι (X := X) hUleD] at hmem
      exact hmem
    exact hx
  -- Step 6: the factorisation `g` of α₀ through `b.domain`
  let g : U.toScheme ⟶ (b.domain).toScheme :=
    X.homOfLE ((inf_le_left : U ≤ W₁).trans hW₁l') ≫ p
  have hg₁ : g ≫ b.hom = U.ι := by
    rw [Category.assoc, ← Scheme.homOfLE_homOfLE X ((inf_le_left : U ≤ W₁)) hW₁l', Category.assoc,
      MX, Scheme.homOfLE_ι]
  have hpι : p ≫ b.domain.ι = X.homOfLE (a.domain.ι_image_le (a.hom ⁻¹ᵁ b.domain)) ≫ a.hom := by
    rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, Scheme.Opens.isoImage_ι_inv_ι]
  have hg₂ : g ≫ b.domain.ι = α₀ := by
    rw [Category.assoc, hpι, ← Category.assoc,
      Scheme.homOfLE_homOfLE X ((inf_le_left : U ≤ W₁).trans hW₁l')
        (a.domain.ι_image_le (a.hom ⁻¹ᵁ b.domain))]
  -- Step 7: α is the lift of α₀ through V
  let α : U.toScheme ⟶ V.toScheme := IsOpenImmersion.lift V.ι α₀ hαrange
  have hαfac : α ≫ V.ι = α₀ := IsOpenImmersion.lift_fac V.ι α₀ hαrange
  -- Step 8: the morphism h₀ (the restriction of `b` to `V`) and β₀
  let h₀ : V.toScheme ⟶ (a.domain).toScheme :=
    Y.homOfLE ((inf_le_left : V ≤ W₂).trans hW₂l') ≫ q
  have hh₀₁ : h₀ ≫ a.hom = V.ι := by
    rw [Category.assoc, ← Scheme.homOfLE_homOfLE Y ((inf_le_left : V ≤ W₂)) hW₂l', Category.assoc,
      MY, Scheme.homOfLE_ι]
  have hqι : q ≫ a.domain.ι = Y.homOfLE (b.domain.ι_image_le (b.hom ⁻¹ᵁ a.domain)) ≫ b.hom := by
    rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, Scheme.Opens.isoImage_ι_inv_ι]
  have hh₀₂ : h₀ ≫ a.domain.ι = Y.homOfLE hVleE ≫ b.hom := by
    rw [Category.assoc, hqι, ← Category.assoc,
      Scheme.homOfLE_homOfLE Y ((inf_le_left : V ≤ W₂).trans hW₂l')
        (b.domain.ι_image_le (b.hom ⁻¹ᵁ a.domain))]
  let β₀ : V.toScheme ⟶ X := h₀ ≫ a.domain.ι
  -- Step 9: the range condition for β₀
  have hβrange : Set.range (⇑β₀) ⊆ Set.range (⇑U.ι) := by
    rw [Scheme.Opens.range_ι]
    have hW : Set.range (⇑β₀) ⊆ (W₁ : Set X) := by
      rintro x ⟨y, rfl⟩
      have hy : ⇑(Y.homOfLE hVleE) y ∈ (b.hom ⁻¹ᵁ W₁ : Set ↑(b.domain)) := by
        refine (Scheme.Hom.apply_mem_image_iff b.domain.ι).mp ?_
        have hmem : ⇑V.ι y ∈ (b.domain.ι ''ᵁ (b.hom ⁻¹ᵁ W₁) : Set Y) :=
          (inf_le_right : V ≤ b.domain.ι ''ᵁ (b.hom ⁻¹ᵁ W₁)) y.2
        rw [← Scheme.homOfLE_ι (X := Y) hVleE] at hmem
        exact hmem
      rw [show β₀ = Y.homOfLE hVleE ≫ b.hom from hh₀₂]
      simpa using hy
    have himg : Set.range (⇑β₀) ⊆ (a.domain.ι ''ᵁ (a.hom ⁻¹ᵁ V) : Set X) := by
      have hh : Set.range (⇑h₀) ⊆ (a.hom ⁻¹ᵁ V : Set ↑(a.domain)) := by
        intro d hd
        have h2 : ⇑a.hom d ∈ ⇑a.hom '' Set.range (⇑h₀) := ⟨d, hd, rfl⟩
        have h3 : ⇑a.hom '' Set.range (⇑h₀) = (V : Set Y) := by
          rw [← Set.range_comp]
          rw [show (⇑a.hom ∘ ⇑h₀) = ⇑(h₀ ≫ a.hom) from rfl, hh₀₁, Scheme.Opens.range_ι]
        rwa [h3] at h2
      rintro x ⟨y, rfl⟩
      rw [Scheme.Hom.coe_image]
      exact ⟨⇑h₀ y, hh ⟨y, rfl⟩, rfl⟩
    intro x hx
    rw [TopologicalSpace.Opens.coe_inf]
    exact ⟨hW hx, himg hx⟩
  -- Step 10: β
  let β : V.toScheme ⟶ U.toScheme := IsOpenImmersion.lift U.ι β₀ hβrange
  have hβfac : β ≫ U.ι = β₀ := IsOpenImmersion.lift_fac U.ι β₀ hβrange
  -- Step 11: auxiliary cancellation identities
  have h_g : α ≫ Y.homOfLE hVleE = g := by
    rw [← cancel_mono b.domain.ι]
    rw [Category.assoc, Scheme.homOfLE_ι, hαfac]
    exact hg₂.symm
  have h_h₀ : β ≫ X.homOfLE hUleD = h₀ := by
    rw [← cancel_mono a.domain.ι]
    rw [Category.assoc, Scheme.homOfLE_ι, hβfac]
  -- Step 12: the two inverse identities
  have hβα : β ≫ α = 𝟙 V.toScheme := by
    rw [← cancel_mono V.ι]
    show (β ≫ α) ≫ V.ι = 𝟙 V.toScheme ≫ V.ι
    rw [Category.assoc, hαfac]
    show β ≫ (X.homOfLE hUleD ≫ a.hom) = 𝟙 V.toScheme ≫ V.ι
    rw [← Category.assoc, h_h₀, hh₀₁, Category.id_comp]
  have hαβ : α ≫ β = 𝟙 U.toScheme := by
    rw [← cancel_mono U.ι]
    show (α ≫ β) ≫ U.ι = 𝟙 U.toScheme ≫ U.ι
    rw [Category.assoc, hβfac]
    show α ≫ (h₀ ≫ a.domain.ι) = 𝟙 U.toScheme ≫ U.ι
    rw [hh₀₂]
    rw [← Category.assoc, h_g, hg₁, Category.id_comp]
  -- Step 13: assemble the partial isomorphism
  let iso : U.toScheme ≅ V.toScheme := ⟨α, β, hαβ, hβα⟩
  let i : X.PartialIso Y := ⟨U, hUd, V, hVd, iso⟩
  have hptm : i.toPartialMap.equiv a := by
    have hdom : Dense (↑i.toPartialMap.domain : Set X) := hUd
    have hle : i.toPartialMap.domain ≤ a.domain := hUleD
    refine ⟨i.toPartialMap.domain, hdom,
      (le_rfl : i.toPartialMap.domain ≤ i.toPartialMap.domain), hle, ?_⟩
    rw [PartialMap.restrict_hom, PartialMap.restrict_hom,
      show X.homOfLE (le_rfl : i.toPartialMap.domain ≤ i.toPartialMap.domain) =
        𝟙 (i.toPartialMap.domain).toScheme from Scheme.homOfLE_rfl X i.toPartialMap.domain,
      Category.id_comp, PartialIso.toPartialMap_hom]
    show α ≫ V.ι = X.homOfLE hUleD ≫ a.hom
    exact hαfac
  have hφ : i.toRationalMap = φ.hom := (PartialMap.toRationalMap_eq_iff.mpr hptm).trans ha
  exact ⟨i, BirationalMap.ext _ _ (by rw [PartialIso.toBirationalMap_hom]; exact hφ)⟩

end Work.Motivic
