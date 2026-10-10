import Mathlib
import Submission.Work.Motivic.CompMorph

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option linter.style.haveILetI false

namespace Work.Motivic

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme

/-!
# A birational map is represented by a partial isomorphism

`ChallengeDeps.lean` defines `Scheme.BirationalMap X Y` as a pair of mutually inverse dominant
rational maps `hom : X ⤏ Y`, `inv : Y ⤏ X` (with `hom.comp inv = .id X` and `inv.comp hom = .id Y`).
Mathlib has `Scheme.PartialIso X Y` (an isomorphism between dense open subschemes) and
`PartialIso.toBirationalMap`, but *not* the converse: every such pair of mutually inverse
rational maps is represented by a partial isomorphism, i.e. `φ.hom` is, over a dense open, an
isomorphism of schemes.

## Proof route

Work with representatives: `a : X.PartialMap Y` with `a.toRationalMap = φ.hom` and
`b : Y.PartialMap X` with `b.toRationalMap = φ.inv`.

* From `φ.hom_comp_inv_id` we get `a.comp b ≃ id_X`, and from `φ.inv_comp_hom_id`
  `b.comp a ≃ id_Y`.  Unpacking these equivalences gives dense opens `W₁ ⊆ X`, `W₂ ⊆ Y` on which
  the composites `a.comp b` resp. `b.comp a` are the identity *morphisms* (`MX`, `MY`).
* Set `V := W₂ ⊓ (b.domain.ι ''ᵁ (b.hom ⁻¹ᵁ W₁))` and `U := W₁ ⊓ (a.domain.ι ''ᵁ (a.hom ⁻¹ᵁ V))`,
  both dense.  The morphism `α₀ : ↑U ⟶ Y`, `α₀ = X.homOfLE hUleD ≫ a.hom`, has image in `V`, so
  it lifts to `α : ↑U ⟶ ↑V`.  Symmetrically `β₀ : ↑V ⟶ X` (obtained as `h₀ ≫ a.domain.ι` for a
  suitable factorisation `h₀` of the composite) has image in `U` and lifts to `β : ↑V ⟶ ↑U`.
* Using `MX`/`MY` one shows `β ≫ α = 𝟙 V` and `α ≫ β = 𝟙 U`, hence `↑U ≅ ↑V` by `α`.
* The resulting partial isomorphism has `toRationalMap = a.toRationalMap = φ.hom` because its
  underlying partial map restricts to the restriction of `a` on the dense open `U`.
-/

/-- If `f : X.PartialMap Y` is dominant and `W : Y.Opens` is dense, then the open subscheme
`f.domain.ι ''ᵁ (f.hom ⁻¹ᵁ W)` of `X` (the domain of the composite of `f` with the restriction of
the identity to `W`) is dense in `X`. -/
theorem aux_dense_image_preimage {X Y : Scheme.{0}} [PreirreducibleSpace X] [Nonempty Y]
    (f : X.PartialMap Y) [IsDominant f.hom] {W : Y.Opens} (hW : Dense (W : Set Y)) :
    Dense (↑(f.domain.ι ''ᵁ (f.hom ⁻¹ᵁ W)) : Set X) :=
  (f.domain.ι ''ᵁ (f.hom ⁻¹ᵁ W)).2.dense <| by
    simpa [← Set.nonempty_preimage_iff] using
      f.hom.denseRange.inter_open_nonempty _ W.2 hW.nonempty

/-- Restricting the identity `MX : X.homOfLE hWl ≫ compMorph f g = W.ι` to `U ≤ W`. -/
theorem aux_homOfLE_comp_compMorph_eq_ι {X Y : Scheme.{0}} (f : X.PartialMap Y)
    (g : Y.PartialMap X) {W : X.Opens} (hWl : W ≤ f.domain.ι ''ᵁ (f.hom ⁻¹ᵁ g.domain))
    (MX : X.homOfLE hWl ≫ compMorph f g = W.ι) {U : X.Opens} (hU : U ≤ W) :
    X.homOfLE (hU.trans hWl) ≫ compMorph f g = U.ι := by
  rw [← Scheme.homOfLE_homOfLE X hU hWl, Category.assoc, MX, Scheme.homOfLE_ι]

/-- The first half of the composite `a ∘ b`, composed with `b.hom`, is the inclusion of `U`. -/
theorem aux_compMorphInv_comp_hom {X Y : Scheme.{0}} [PreirreducibleSpace X] [Nonempty Y]
    (f : X.PartialMap Y) [IsDominant f.hom] (g : Y.PartialMap X) {W : X.Opens}
    (hWl : W ≤ f.domain.ι ''ᵁ (f.hom ⁻¹ᵁ g.domain))
    (hW : X.homOfLE hWl ≫ compMorph f g = W.ι) {U : X.Opens} (hUX : U ≤ W) :
    compMorphInv f g (hUX.trans hWl) ≫ g.hom = U.ι := by
  have h1 : X.homOfLE (hUX.trans hWl) ≫ compMorph f g = U.ι :=
    aux_homOfLE_comp_compMorph_eq_ι f g hWl hW hUX
  rw [← h1]
  simp only [compMorph, compMorphInv, Category.assoc]

/-- The first half of the composite `a ∘ b`, composed with `b.domain.ι`, is the restriction of
`a.hom` to `U`. -/
theorem aux_compMorphInv_comp_domain_iota {X Y : Scheme.{0}} (f : X.PartialMap Y)
    (g : Y.PartialMap X) {U : X.Opens}
    (hUE : U ≤ f.domain.ι ''ᵁ (f.hom ⁻¹ᵁ g.domain)) (hUD : U ≤ f.domain) :
    compMorphInv f g hUE ≫ g.domain.ι = X.homOfLE hUD ≫ f.hom := by
  simp only [compMorphInv, Category.assoc]
  rw [AlgebraicGeometry.morphismRestrict_ι,
    ← Category.assoc (Hom.isoImage f.domain.ι (f.hom ⁻¹ᵁ g.domain)).inv,
    Scheme.Opens.isoImage_ι_inv_ι,
    ← Scheme.homOfLE_homOfLE X hUE (Scheme.Opens.ι_image_le f.domain (f.hom ⁻¹ᵁ g.domain))]
  rw [Category.assoc]

/-- Every birational map between irreducible schemes is represented by a partial isomorphism:
there is a partial isomorphism `i` whose rational map is `φ.hom`. -/
theorem exists_partialIso_toRationalMap_eq {X Y : Scheme.{0}} [IrreducibleSpace X]
    [IrreducibleSpace Y] (φ : X.BirationalMap Y) :
    ∃ i : X.PartialIso Y, i.toRationalMap = φ.hom := by
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
  have h₁ : (a.comp b).equiv (PartialMap.id X) := by
    rw [← PartialMap.toRationalMap_eq_iff, ← RationalMap.toRationalMap_comp (f := a) (g := b),
      hcomp₁, BirationalMap.hom_comp_inv_id]
  have h₂ : (b.comp a).equiv (PartialMap.id Y) := by
    rw [← PartialMap.toRationalMap_eq_iff, ← RationalMap.toRationalMap_comp (f := b) (g := a),
      hcomp₂, BirationalMap.inv_comp_hom_id]
  -- Step 2: unpack the two equivalences into morphism identities on dense opens.
  obtain ⟨W₁, hW₁d, hW₁l, hW₁r, he₁⟩ := h₁
  obtain ⟨W₂, hW₂d, hW₂l, hW₂r, he₂⟩ := h₂
  have MX : X.homOfLE hW₁l ≫ (a.comp b).hom = W₁.ι := by
    have h2 : ((PartialMap.id X).restrict W₁ hW₁d hW₁r).hom = W₁.ι := by
      simp only [PartialMap.restrict_hom, PartialMap.id_hom, Scheme.topIso_hom]
      exact Scheme.homOfLE_ι X hW₁r
    exact he₁.trans h2
  have MY : Y.homOfLE hW₂l ≫ (b.comp a).hom = W₂.ι := by
    have h2 : ((PartialMap.id Y).restrict W₂ hW₂d hW₂r).hom = W₂.ι := by
      simp only [PartialMap.restrict_hom, PartialMap.id_hom, Scheme.topIso_hom]
      exact Scheme.homOfLE_ι Y hW₂r
    exact he₂.trans h2
  -- The same identities with the composite written out on its explicit domain.
  have hW₁l' : W₁ ≤ a.domain.ι ''ᵁ (a.hom ⁻¹ᵁ b.domain) := hW₁l
  have MX' : X.homOfLE hW₁l' ≫ compMorph a b = W₁.ι := by
    rw [compMorph_eq]; exact MX
  have hW₂l' : W₂ ≤ b.domain.ι ''ᵁ (b.hom ⁻¹ᵁ a.domain) := hW₂l
  have MY' : Y.homOfLE hW₂l' ≫ compMorph b a = W₂.ι := by
    rw [compMorph_eq]; exact MY
  -- Step 3: the two dense opens `U ⊆ X` and `V ⊆ Y`.
  let V : Y.Opens := W₂ ⊓ (b.domain.ι ''ᵁ (b.hom ⁻¹ᵁ W₁))
  have hVd : Dense (V : Set Y) := by
    have hd₂ : Dense ((b.domain.ι ''ᵁ (b.hom ⁻¹ᵁ W₁)) : Set Y) :=
      aux_dense_image_preimage b hW₁d
    simpa only [TopologicalSpace.Opens.coe_inf, V] using hW₂d.inter_of_isOpen_left hd₂ W₂.2
  let U : X.Opens := W₁ ⊓ (a.domain.ι ''ᵁ (a.hom ⁻¹ᵁ V))
  have hUd : Dense (U : Set X) := by
    have hd₂ : Dense ((a.domain.ι ''ᵁ (a.hom ⁻¹ᵁ V)) : Set X) :=
      aux_dense_image_preimage a hVd
    simpa only [TopologicalSpace.Opens.coe_inf, U] using hW₁d.inter_of_isOpen_left hd₂ W₁.2
  -- Step 4: containments of the opens.
  have hVleBA : V ≤ b.domain.ι ''ᵁ (b.hom ⁻¹ᵁ a.domain) :=
    (inf_le_left : V ≤ W₂).trans hW₂l'
  have hVleE : V ≤ b.domain := hVleBA.trans (b.domain.ι_image_le (b.hom ⁻¹ᵁ a.domain))
  have hUleD : U ≤ a.domain :=
    (inf_le_right : U ≤ a.domain.ι ''ᵁ (a.hom ⁻¹ᵁ V)).trans
      ((a.domain.ι.image_mono (a.hom.preimage_mono hVleE)).trans
        (a.domain.ι_image_le (a.hom ⁻¹ᵁ b.domain)))
  -- Step 5: `α₀`, the restriction of `a` to `U`, and its range condition.
  let α₀ : U.toScheme ⟶ Y := X.homOfLE hUleD ≫ a.hom
  have hαrange : Set.range (⇑α₀) ⊆ Set.range (⇑V.ι) := by
    rw [Scheme.Opens.range_ι]
    rintro y ⟨x, rfl⟩
    have hx : ⇑(X.homOfLE hUleD) x ∈ (a.hom ⁻¹ᵁ V : Set (a.domain).toScheme) := by
      refine (Scheme.Hom.apply_mem_image_iff a.domain.ι).mp ?_
      have hmem : ⇑U.ι x ∈ (a.domain.ι ''ᵁ (a.hom ⁻¹ᵁ V) : Set X) :=
        (inf_le_right : U ≤ a.domain.ι ''ᵁ (a.hom ⁻¹ᵁ V)) x.2
      rw [← Scheme.homOfLE_ι (X := X) hUleD] at hmem
      exact hmem
    exact hx
  -- Step 6: the factorisation `g` of `α₀` through `b.domain`.
  let g : U.toScheme ⟶ (b.domain).toScheme :=
    compMorphInv a b ((inf_le_left : U ≤ W₁).trans hW₁l')
  have hg₁ : g ≫ b.hom = U.ι :=
    aux_compMorphInv_comp_hom a b hW₁l' MX' (hUX := inf_le_left)
  have hg₂ : g ≫ b.domain.ι = α₀ :=
    aux_compMorphInv_comp_domain_iota a b ((inf_le_left : U ≤ W₁).trans hW₁l') hUleD
  -- Step 7: `α` is the lift of `α₀` through the open immersion `V.ι`.
  let α : U.toScheme ⟶ V.toScheme := IsOpenImmersion.lift V.ι α₀ hαrange
  have hαfac : α ≫ V.ι = α₀ := IsOpenImmersion.lift_fac V.ι α₀ hαrange
  -- Step 8: the factorisation `h₀` of `β₀` through `a.domain`.
  let h₀ : V.toScheme ⟶ (a.domain).toScheme :=
    compMorphInv b a ((inf_le_left : V ≤ W₂).trans hW₂l')
  have hh₀₁ : h₀ ≫ a.hom = V.ι :=
    aux_compMorphInv_comp_hom b a hW₂l' MY' (hUX := inf_le_left)
  let β₀ : V.toScheme ⟶ X := h₀ ≫ a.domain.ι
  have hβ₀iff : β₀ = Y.homOfLE hVleE ≫ b.hom :=
    aux_compMorphInv_comp_domain_iota b a ((inf_le_left : V ≤ W₂).trans hW₂l') hVleE
  -- Step 9: the range condition for `β₀`.
  have hβrange : Set.range (⇑β₀) ⊆ Set.range (⇑U.ι) := by
    rw [Scheme.Opens.range_ι]
    have hW : Set.range (⇑β₀) ⊆ (W₁ : Set X) := by
      rintro x ⟨y, rfl⟩
      have hy : ⇑(Y.homOfLE hVleE) y ∈ (b.hom ⁻¹ᵁ W₁ : Set (b.domain).toScheme) := by
        refine (Scheme.Hom.apply_mem_image_iff b.domain.ι).mp ?_
        have hmem : ⇑V.ι y ∈ (b.domain.ι ''ᵁ (b.hom ⁻¹ᵁ W₁) : Set Y) :=
          (inf_le_right : V ≤ b.domain.ι ''ᵁ (b.hom ⁻¹ᵁ W₁)) y.2
        rw [← Scheme.homOfLE_ι (X := Y) hVleE] at hmem
        exact hmem
      rw [hβ₀iff]
      exact hy
    have himg : Set.range (⇑β₀) ⊆ (a.domain.ι ''ᵁ (a.hom ⁻¹ᵁ V) : Set X) := by
      have hh : Set.range (⇑h₀) ⊆ (a.hom ⁻¹ᵁ V : Set (a.domain).toScheme) := by
        intro d hd
        have h2 : ⇑a.hom d ∈ ⇑a.hom '' Set.range (⇑h₀) := ⟨d, hd, rfl⟩
        have h3 : ⇑a.hom '' Set.range (⇑h₀) = (V : Set Y) := by
          rw [← Set.range_comp]
          have : (⇑a.hom ∘ ⇑h₀) = ⇑(h₀ ≫ a.hom) := rfl
          rw [this, hh₀₁, Scheme.Opens.range_ι]
        rwa [h3] at h2
      rintro x ⟨y, rfl⟩
      rw [Scheme.Hom.coe_image]
      exact ⟨⇑h₀ y, hh ⟨y, rfl⟩, rfl⟩
    intro x hx
    rw [TopologicalSpace.Opens.coe_inf]
    exact ⟨hW hx, himg hx⟩
  -- Step 10: `β` is the lift of `β₀` through the open immersion `U.ι`.
  let β : V.toScheme ⟶ U.toScheme := IsOpenImmersion.lift U.ι β₀ hβrange
  have hβfac : β ≫ U.ι = β₀ := IsOpenImmersion.lift_fac U.ι β₀ hβrange
  -- Step 11: auxiliary cancellation identities.
  have h_g : α ≫ Y.homOfLE hVleE = g := by
    rw [← cancel_mono b.domain.ι]
    rw [Category.assoc, Scheme.homOfLE_ι, hαfac]
    exact hg₂.symm
  have h_h₀ : β ≫ X.homOfLE hUleD = h₀ := by
    rw [← cancel_mono a.domain.ι]
    rw [Category.assoc, Scheme.homOfLE_ι, hβfac, hβ₀iff]
    exact (aux_compMorphInv_comp_domain_iota b a
      ((inf_le_left : V ≤ W₂).trans hW₂l') hVleE).symm
  -- Step 12: the two inverse identities.
  have hβα : β ≫ α = 𝟙 V.toScheme := by
    rw [← cancel_mono V.ι]
    show (β ≫ α) ≫ V.ι = 𝟙 V.toScheme ≫ V.ι
    rw [Category.assoc, hαfac]
    show β ≫ (X.homOfLE hUleD ≫ a.hom) = 𝟙 V.toScheme ≫ V.ι
    rw [← Category.assoc, h_h₀, hh₀₁, Category.id_comp]
  have hαβ : α ≫ β = 𝟙 U.toScheme := by
    rw [← cancel_mono U.ι]
    show (α ≫ β) ≫ U.ι = 𝟙 U.toScheme ≫ U.ι
    rw [Category.assoc, hβfac, hβ₀iff]
    show α ≫ (Y.homOfLE hVleE ≫ b.hom) = 𝟙 U.toScheme ≫ U.ι
    rw [← Category.assoc, h_g, hg₁, Category.id_comp]
  -- Step 13: assemble the partial isomorphism.
  let iso : U.toScheme ≅ V.toScheme := ⟨α, β, hαβ, hβα⟩
  let i : X.PartialIso Y := ⟨U, hUd, V, hVd, iso⟩
  have hptm : i.toPartialMap.equiv a := by
    refine ⟨U, hUd, le_rfl, hUleD, ?_⟩
    show X.homOfLE (le_rfl : U ≤ U) ≫ i.toPartialMap.hom = X.homOfLE hUleD ≫ a.hom
    rw [Scheme.homOfLE_rfl]
    show α ≫ V.ι = X.homOfLE hUleD ≫ a.hom
    exact hαfac
  exact ⟨i, (PartialMap.toRationalMap_eq_iff.mpr hptm).trans ha⟩

end Work.Motivic
