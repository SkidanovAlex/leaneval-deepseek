import Mathlib
import Submission.Work.CY3Stab.Defs
import Submission.Work.CY3Stab.Prod.AlgMapResidue
import Submission.Work.CY3Stab.Prod.isIso_algMapResidue_id

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The `𝔸ᵏ`-leg compatibility of the tensor of a cylinder

For a `𝕜`-scheme `Y`, a point `y : Y` and `k : ℕ`, the tensor of the cylinder triplet is
`(cylTriplet Y y k).tensor = κ(𝔸ᵏ) ⊗_{κ(s)} κ(y)` and its coprojection
`(cylTriplet Y y k).tensorInl : κ(𝔸ᵏ) ⟶ (cylTriplet Y y k).tensor` is the `𝔸ᵏ`-leg.

This module proves `Work.CY3Stab.Prod.tensor_iso_tensorInl`: if two base points `x : X`, `z : Z`
have `𝕜`-isomorphic residue fields (`ResEquiv 𝕜 x z`), then the tensors of the two cylinder
triplets are isomorphic by an isomorphism which is *the identity on the shared `𝔸ᵏ`-leg*:

`(cylTriplet X x k).tensorInl ≫ Φ.hom = (cylTriplet Z z k).tensorInl`.

This is the `tensorInl` companion of `Work.CY3Stab.Prod.tensor_iso_of_resEquiv` (which pins the
`tensorInr` leg against a specific `κ(x) ≅ κ(z)`); it is the transport used to compare the
`𝕜`-structures of the two tensors via the `𝔸ᵏ`-leg in
`Submission/Work/CY3Stab/Prod/resEquiv_prodPt_of_resEquiv.lean`.

The mathematical content is the standard functoriality of the pushout: the two tensors are
pushouts of spans with a common left leg `algMapResidue (𝔸ᵏ ↘ Spec 𝕜) (genericPoint 𝔸ᵏ)`
(the `𝕜`-structure of the residue field of the generic point of `𝔸ᵏ`) and right legs
`algMapResidue (X ↘ Spec 𝕜) x` resp. `algMapResidue (Z ↘ Spec 𝕜) z`, which are intertwined by
the `𝕜`-algebra isomorphism `κ(x) ≅ κ(z)` supplied by `ResEquiv`.  Passing from the "raw" legs
of `Triplet.tensor` (based at `κ(s)`) to these `𝕜`-based legs is a pushout base change along the
isomorphism `algMapResidue (𝟙 (Spec 𝕜)) s : 𝕜 ≅ κ(s)`.

The proof is assembled from three ingredients:

* `pushout_iso_base_change` — pushing out along a composite `φ ≫ f` with `φ` an isomorphism is
  the same as pushing out along `f`, with the corresponding `pushout.inl` compatibilities;
* `pushout_iso_right` — replacing the right leg of a pushout span by an isomorphic one (over a
  fixed left leg) produces an isomorphism of pushouts with the corresponding leg compatibilities;
* `cylTriplet_tensor_iso_inl_leg` — the identification of `(cylTriplet Y y k).tensor` with the
  pushout of `l` (a chosen left leg, equal to `algMapResidue (𝔸ᵏ ↘ Spec 𝕜) (genericPoint 𝔸ᵏ)`)
  and `algMapResidue (Y ↘ Spec 𝕜) y`, together with the two `tensorInl` compatibilities.  The
  left leg is kept as a *variable* so that the isomorphisms obtained for `X` and for `Z` are
  literally pushouts of the same span, which is what makes the final assembly syntactically
  transparent.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Work.CY3Stab.Prod

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

noncomputable section

variable {𝕜 : Type} [Field 𝕜]

/-! ## 1. Two general pushout compatibilities -/

/-- **Base change of a pushout along an isomorphism.**  If `φ : A ⟶ A'` is an isomorphism then
the pushout of the span `A --φ ≫ f--> B`, `A --φ ≫ g--> C` is canonically isomorphic to the
pushout of `f : A' ⟶ B`, `g : A' ⟶ C`, and the isomorphism intertwines the two coprojections. -/
theorem pushout_iso_base_change {A A' B C : CommRingCat.{0}} (φ : A ⟶ A') [IsIso φ]
    (F : A' ⟶ B) (G : A' ⟶ C) (f : A ⟶ B) (g : A ⟶ C) (hf : f = φ ≫ F) (hg : g = φ ≫ G) :
    ∃ i : pushout f g ≅ pushout F G,
      pushout.inl f g ≫ i.hom = pushout.inl F G ∧
      pushout.inl F G ≫ i.inv = pushout.inl f g := by
  subst hf; subst hg
  refine ⟨Iso.mk
      (pushout.desc (f := φ ≫ F) (g := φ ≫ G) (pushout.inl F G) (pushout.inr F G)
        (by simp only [Category.assoc, pushout.condition]))
      (pushout.desc (f := F) (g := G) (pushout.inl (φ ≫ F) (φ ≫ G))
        (pushout.inr (φ ≫ F) (φ ≫ G))
        (by
          refine (cancel_epi φ).mp ?_
          rw [← Category.assoc, ← Category.assoc, pushout.condition]))
      ?_ ?_, ?_, ?_⟩
  · refine pushout.hom_ext (f := φ ≫ F) (g := φ ≫ G) ?_ ?_
    · simp only [← Category.assoc, pushout.inl_desc, Category.comp_id]
    · simp only [← Category.assoc, pushout.inr_desc, Category.comp_id]
  · refine pushout.hom_ext (f := F) (g := G) ?_ ?_
    · simp only [← Category.assoc, pushout.inl_desc, Category.comp_id]
    · simp only [← Category.assoc, pushout.inr_desc, Category.comp_id]
  · exact pushout.inl_desc _ _ _
  · exact pushout.inl_desc _ _ _

/-- **Pushout of a span with a replaced right leg.**  If `e : C₁ ≅ C₂` satisfies
`g₁ ≫ e.hom = g₂`, then pushing out `f, g₁` is the same as pushing out `f, g₂`, and the
isomorphism intertwines the coprojections. -/
theorem pushout_iso_right {A B C₁ C₂ : CommRingCat.{0}} (f : A ⟶ B) (g₁ : A ⟶ C₁)
    (g₂ : A ⟶ C₂) (e : C₁ ≅ C₂) (w : g₁ ≫ e.hom = g₂) :
    ∃ i : pushout f g₁ ≅ pushout f g₂,
      pushout.inl f g₁ ≫ i.hom = pushout.inl f g₂ ∧
      pushout.inr f g₁ ≫ i.hom = e.hom ≫ pushout.inr f g₂ ∧
      pushout.inl f g₂ ≫ i.inv = pushout.inl f g₁ := by
  have hw : g₂ ≫ e.inv = g₁ := by rw [← w, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  refine ⟨Iso.mk
      (pushout.desc (f := f) (g := g₁) (pushout.inl f g₂) (e.hom ≫ pushout.inr f g₂)
        (by rw [← Category.assoc, w, pushout.condition]))
      (pushout.desc (f := f) (g := g₂) (pushout.inl f g₁) (e.inv ≫ pushout.inr f g₁)
        (by rw [← Category.assoc, hw, pushout.condition]))
      ?_ ?_, ?_, ?_, ?_⟩
  · refine pushout.hom_ext (f := f) (g := g₁) ?_ ?_
    · simp only [← Category.assoc, pushout.inl_desc, Category.comp_id]
    · rw [← Category.assoc, pushout.inr_desc, Category.assoc, pushout.inr_desc,
        Iso.hom_inv_id_assoc, Category.comp_id]
  · refine pushout.hom_ext (f := f) (g := g₂) ?_ ?_
    · simp only [← Category.assoc, pushout.inl_desc, Category.comp_id]
    · rw [← Category.assoc, pushout.inr_desc, Category.assoc, pushout.inr_desc,
        Iso.inv_hom_id_assoc, Category.comp_id]
  · exact pushout.inl_desc _ _ _
  · exact pushout.inr_desc _ _ _
  · exact pushout.inl_desc _ _ _

/-! ## 2. The tensor of a cylinder triplet, in terms of the structure maps -/

/-- **The tensor of a cylinder triplet, with a prescribed `𝔸ᵏ`-leg.**  For a `𝕜`-scheme `Y`, a
point `y : Y` and a morphism `l : 𝕜 ⟶ κ(genericPoint 𝔸ᵏ)` equal to the structure map
`algMapResidue (𝔸ᵏ ↘ Spec 𝕜) (genericPoint 𝔸ᵏ)`, the tensor of `cylTriplet Y y k` is the pushout
of `l` and `algMapResidue (Y ↘ Spec 𝕜) y`, by an isomorphism intertwining the two `𝔸ᵏ`-legs.

The left leg is kept as a variable so that the isomorphism produced for two different schemes `Y`
(the same `l` being used for both) has a target which is *syntactically* the pushout of the same
span. -/
theorem cylTriplet_tensor_iso_inl_leg (Y : Scheme.{0}) [Y.Over (Spec (CommRingCat.of 𝕜))] (y : Y)
    (k : ℕ)
    (l : CommRingCat.of 𝕜 ⟶ (AffineK (𝕜 := 𝕜) k).residueField
          (cylTriplet (𝕜 := 𝕜) Y y k).x)
    (hl : l = algMapResidue
        (AffineK (𝕜 := 𝕜) k ↘ Spec (CommRingCat.of 𝕜))
        (cylTriplet (𝕜 := 𝕜) Y y k).x) :
    ∃ β : (cylTriplet (𝕜 := 𝕜) Y y k).tensor ≅
        pushout l (algMapResidue (Y ↘ Spec (CommRingCat.of 𝕜)) y),
      (cylTriplet (𝕜 := 𝕜) Y y k).tensorInl ≫ β.hom
        = pushout.inl l (algMapResidue (Y ↘ Spec (CommRingCat.of 𝕜)) y) ∧
      pushout.inl l (algMapResidue (Y ↘ Spec (CommRingCat.of 𝕜)) y) ≫ β.inv
        = (cylTriplet (𝕜 := 𝕜) Y y k).tensorInl := by
  haveI : IsIso (algMapResidue (𝟙 (Spec (CommRingCat.of 𝕜)))
      (cylTriplet (𝕜 := 𝕜) Y y k).s) :=
    isIso_algMapResidue_id 𝕜 _
  -- The raw first leg of `Triplet.tensor` is `algMapResidue (𝔸ᵏ ↘ Spec 𝕜) (gen 𝔸ᵏ)`, read
  -- through the isomorphism `algMapResidue (𝟙 (Spec 𝕜)) s : 𝕜 ≅ κ(s)`.
  have hF : algMapResidue
        (AffineK (𝕜 := 𝕜) k ↘ Spec (CommRingCat.of 𝕜))
        (cylTriplet (𝕜 := 𝕜) Y y k).x =
      algMapResidue (𝟙 (Spec (CommRingCat.of 𝕜)))
          (cylTriplet (𝕜 := 𝕜) Y y k).s
        ≫ ((Spec (CommRingCat.of 𝕜)).residueFieldCongr
              (cylTriplet (𝕜 := 𝕜) Y y k).hx).inv
          ≫ (AffineK (𝕜 := 𝕜) k ↘ Spec (CommRingCat.of 𝕜)).residueFieldMap
              (cylTriplet (𝕜 := 𝕜) Y y k).x := by
    rw [← Category.assoc, residueFieldCongr_inv,
      algMapResidue_residueFieldCongr
        (cylTriplet (𝕜 := 𝕜) Y y k).hx.symm]
    exact (algMapResidue_id _ _).symm
  have hG : algMapResidue (Y ↘ Spec (CommRingCat.of 𝕜)) y =
      algMapResidue (𝟙 (Spec (CommRingCat.of 𝕜)))
          (cylTriplet (𝕜 := 𝕜) Y y k).s
        ≫ ((Spec (CommRingCat.of 𝕜)).residueFieldCongr
              (cylTriplet (𝕜 := 𝕜) Y y k).hy).inv
          ≫ (Y ↘ Spec (CommRingCat.of 𝕜)).residueFieldMap
              (cylTriplet (𝕜 := 𝕜) Y y k).y := by
    rw [← Category.assoc, residueFieldCongr_inv,
      algMapResidue_residueFieldCongr
        (cylTriplet (𝕜 := 𝕜) Y y k).hy.symm]
    exact (algMapResidue_id _ _).symm
  obtain ⟨i, h1, h2⟩ := pushout_iso_base_change
    (φ := algMapResidue (𝟙 (Spec (CommRingCat.of 𝕜)))
      (cylTriplet (𝕜 := 𝕜) Y y k).s)
    (F := ((Spec (CommRingCat.of 𝕜)).residueFieldCongr
              (cylTriplet (𝕜 := 𝕜) Y y k).hx).inv
          ≫ (AffineK (𝕜 := 𝕜) k ↘ Spec (CommRingCat.of 𝕜)).residueFieldMap
              (cylTriplet (𝕜 := 𝕜) Y y k).x)
    (G := ((Spec (CommRingCat.of 𝕜)).residueFieldCongr
              (cylTriplet (𝕜 := 𝕜) Y y k).hy).inv
          ≫ (Y ↘ Spec (CommRingCat.of 𝕜)).residueFieldMap
              (cylTriplet (𝕜 := 𝕜) Y y k).y)
    (f := l) (g := algMapResidue (Y ↘ Spec (CommRingCat.of 𝕜)) y) (hl.trans hF) hG
  exact ⟨i.symm, h2, h1⟩

/-- **The `ResEquiv` hypothesis, as an equation of structure maps.**  If `e : κ(x) ≅ κ(z)` is a
`𝕜`-algebra isomorphism of residue fields (`e.toRingHom.comp (resMap 𝕜 X x) = resMap 𝕜 Z z`), then
`algMapResidue (X ↘ Spec 𝕜) x ≫ e = algMapResidue (Z ↘ Spec 𝕜) z`. -/
theorem algMapResidue_comp_toCommRingCatIso {X Z : Scheme.{0}}
    [X.Over (Spec (CommRingCat.of 𝕜))] [Z.Over (Spec (CommRingCat.of 𝕜))]
    {x : X} {z : Z} (e : X.residueField x ≃+* Z.residueField z)
    (he : e.toRingHom.comp (resMap 𝕜 X x) = resMap 𝕜 Z z) :
    algMapResidue (X ↘ Spec (CommRingCat.of 𝕜)) x
      ≫ (RingEquiv.toCommRingCatIso e).hom
      = algMapResidue (Z ↘ Spec (CommRingCat.of 𝕜)) z := by
  apply CommRingCat.hom_ext
  rw [CommRingCat.hom_comp, RingEquiv.toCommRingCatIso_hom, CommRingCat.hom_ofHom]
  rw [show (algMapResidue (X ↘ Spec (CommRingCat.of 𝕜)) x).hom = resMap 𝕜 X x from rfl]
  rw [show (algMapResidue (Z ↘ Spec (CommRingCat.of 𝕜)) z).hom = resMap 𝕜 Z z from rfl]
  exact he

/-! ## 3. The `𝔸ᵏ`-leg compatibility -/

theorem tensor_iso_tensorInl (𝕜 : Type) [Field 𝕜] (k : ℕ) {X Z : AlgebraicGeometry.Scheme.{0}}
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of 𝕜))]
    [Z.Over (AlgebraicGeometry.Spec (CommRingCat.of 𝕜))] (x : X) (z : Z)
    (h : ResEquiv 𝕜 x z) :
    ∃ Φ : (Work.CY3Stab.cylTriplet (𝕜 := 𝕜) X x k).tensor ≅
        (Work.CY3Stab.cylTriplet (𝕜 := 𝕜) Z z k).tensor,
      CategoryTheory.CategoryStruct.comp (Work.CY3Stab.cylTriplet (𝕜 := 𝕜) X x k).tensorInl Φ.hom
        = (Work.CY3Stab.cylTriplet (𝕜 := 𝕜) Z z k).tensorInl := by
  obtain ⟨e, he⟩ := h
  -- The common `𝔸ᵏ`-leg, as a variable, so that both tensors are pushouts of the *same* span.
  let LegX : CommRingCat.of 𝕜 ⟶ (Work.CY3Stab.AffineK (𝕜 := 𝕜) k).residueField
      (Work.CY3Stab.cylTriplet (𝕜 := 𝕜) X x k).x :=
    Work.CY3Stab.Prod.algMapResidue (Work.CY3Stab.AffineK (𝕜 := 𝕜) k ↘ Spec (CommRingCat.of 𝕜))
      (genericPoint (Work.CY3Stab.AffineK (𝕜 := 𝕜) k))
  obtain ⟨βX, hβX1, hβX2⟩ := cylTriplet_tensor_iso_inl_leg (𝕜 := 𝕜) X x k LegX rfl
  obtain ⟨βZ, hβZ1, hβZ2⟩ := cylTriplet_tensor_iso_inl_leg (𝕜 := 𝕜) Z z k LegX rfl
  -- the comparison of the two pushouts over the common left leg
  obtain ⟨Ψ, hΨ1, hΨ2, hΨ3⟩ := pushout_iso_right
    (f := LegX)
    (g₁ := Work.CY3Stab.Prod.algMapResidue (X ↘ Spec (CommRingCat.of 𝕜)) x)
    (g₂ := Work.CY3Stab.Prod.algMapResidue (Z ↘ Spec (CommRingCat.of 𝕜)) z)
    (RingEquiv.toCommRingCatIso e) (algMapResidue_comp_toCommRingCatIso e he)
  refine ⟨βX ≪≫ Ψ ≪≫ βZ.symm, ?_⟩
  show CategoryTheory.CategoryStruct.comp (Work.CY3Stab.cylTriplet (𝕜 := 𝕜) X x k).tensorInl
      (βX.hom ≫ Ψ.hom ≫ βZ.inv) = (Work.CY3Stab.cylTriplet (𝕜 := 𝕜) Z z k).tensorInl
  have hfinal : CategoryTheory.CategoryStruct.comp (Work.CY3Stab.cylTriplet (𝕜 := 𝕜) X x k).tensorInl
        (βX.hom ≫ Ψ.hom ≫ βZ.inv)
      = pushout.inl LegX (Work.CY3Stab.Prod.algMapResidue (Z ↘ Spec (CommRingCat.of 𝕜)) z)
        ≫ βZ.inv := by
    calc CategoryTheory.CategoryStruct.comp (Work.CY3Stab.cylTriplet (𝕜 := 𝕜) X x k).tensorInl
          (βX.hom ≫ Ψ.hom ≫ βZ.inv)
        = ((Work.CY3Stab.cylTriplet (𝕜 := 𝕜) X x k).tensorInl ≫ βX.hom) ≫ (Ψ.hom ≫ βZ.inv) :=
            (Category.assoc _ _ _).symm
      _ = pushout.inl LegX (Work.CY3Stab.Prod.algMapResidue (X ↘ Spec (CommRingCat.of 𝕜)) x)
          ≫ (Ψ.hom ≫ βZ.inv) := by rw [hβX1]
      _ = (pushout.inl LegX (Work.CY3Stab.Prod.algMapResidue (X ↘ Spec (CommRingCat.of 𝕜)) x)
            ≫ Ψ.hom) ≫ βZ.inv := (Category.assoc _ _ _).symm
      _ = pushout.inl LegX (Work.CY3Stab.Prod.algMapResidue (Z ↘ Spec (CommRingCat.of 𝕜)) z)
          ≫ βZ.inv := by rw [hΨ1]
  exact hfinal.trans hβZ2

end

end Work.CY3Stab.Prod
