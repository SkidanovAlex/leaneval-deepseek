import Mathlib

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.CY3Stab.Prod

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits TensorProduct

set_option linter.style.haveILetI false

/-- **The affine chart of the fibre product attached to a pair of affine models.**

Let `f : W ⟶ Spec 𝕜`, `g : X' ⟶ Spec 𝕜` be a cospan, `eW : W ≅ Spec 𝕜[X_σ]` over `Spec 𝕜`, and
`eU : U ≅ Spec A` an affine open of `X'`, also over `Spec 𝕜`.  Then there is a morphism
`Φ : Spec (𝕜[X_σ] ⊗[𝕜] A) ⟶ W ×_{Spec 𝕜} X'` which is an open immersion with image the preimage of
`U` under the second projection, and whose two components are the `Spec` of the canonical ring maps
composed with the inverses of the two affine identifications.

Suggested route: build `Φ` with `pullback.lift`, using that both composites to `Spec 𝕜` are
`Spec.map (algebraMap 𝕜 (𝕜[X_σ] ⊗[𝕜] A))` (rewrite `eW.inv ≫ f` and `eU.inv ≫ U.ι ≫ g` using
`heW`/`heU` and `Iso.inv_hom_id`); then `Φ` is the composite of the iso
`pullbackSpecIso 𝕜 (MvPolynomial σ 𝕜) A` (suitably transported along `eW`, `eU`) with the base
change of the open immersion `U.ι`, so `IsOpenImmersion` follows from
`AlgebraicGeometry.Scheme.pullback_map_isOpenImmersion` (or directly by `pullback.hom_ext` plus
`IsOpenImmersion.comp`), and `opensRange` from `pullback.snd`'s preimage of `U`. -/
theorem chart_of_isos {𝕜 : Type} [Field 𝕜] (σ : Type) (A : Type) [CommRing A] [Algebra 𝕜 A]
    {W X' : Scheme.{0}} (f : W ⟶ Spec (CommRingCat.of 𝕜)) (g : X' ⟶ Spec (CommRingCat.of 𝕜))
    (U : X'.Opens)
    (eW : W ≅ Spec (CommRingCat.of (MvPolynomial σ 𝕜)))
    (heW : eW.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap 𝕜 (MvPolynomial σ 𝕜))) = f)
    (eU : ↑U ≅ Spec (CommRingCat.of A))
    (heU : eU.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap 𝕜 A)) = U.ι ≫ g) :
    ∃ (Φ : Spec (CommRingCat.of (MvPolynomial σ 𝕜 ⊗[𝕜] A)) ⟶ pullback f g)
      (_ : IsOpenImmersion Φ),
      (Φ.opensRange = pullback.snd f g ⁻¹ᵁ U ∧
      Φ ≫ pullback.fst f g = Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
        (R := 𝕜) (A := MvPolynomial σ 𝕜) (B := A))) ≫ eW.inv ∧
      Φ ≫ pullback.snd f g = Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
        (R := 𝕜) (A := MvPolynomial σ 𝕜) (B := A)).toRingHom) ≫ eU.inv ≫ U.ι) := by
  -- The two structure morphisms of the two affine models.
  let s : Spec (CommRingCat.of (MvPolynomial σ 𝕜)) ⟶ Spec (CommRingCat.of 𝕜) :=
    Spec.map (CommRingCat.ofHom (algebraMap 𝕜 (MvPolynomial σ 𝕜)))
  let t : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of 𝕜) :=
    Spec.map (CommRingCat.ofHom (algebraMap 𝕜 A))
  have heW' : eW.hom ≫ s = f := heW
  have heU' : eU.hom ≫ t = U.ι ≫ g := heU
  have hW : eW.inv ≫ f = s := by rw [← heW', Iso.inv_hom_id_assoc]
  have hU : eU.inv ≫ U.ι ≫ g = t := by rw [← heU', Iso.inv_hom_id_assoc]
  -- The comparison morphism from the pullback of the two models to the fibre product.
  let L : pullback s t ⟶ pullback f g :=
    pullback.lift (pullback.fst s t ≫ eW.inv) (pullback.snd s t ≫ eU.inv ≫ U.ι)
      (by simp only [Category.assoc, hW, hU, pullback.condition])
  have hLfst : L ≫ pullback.fst f g = pullback.fst s t ≫ eW.inv := by
    dsimp only [L]; exact pullback.lift_fst _ _ _
  have hLsnd : L ≫ pullback.snd f g = pullback.snd s t ≫ eU.inv ≫ U.ι := by
    dsimp only [L]; exact pullback.lift_snd _ _ _
  -- `L` is the base change of the open immersion `eU.inv ≫ U.ι` along `pullback.snd f g`;
  -- this is witnessed by an explicit isomorphism `θ` between `pullback s t` and
  -- `pullback (pullback.snd f g) (eU.inv ≫ U.ι)`.
  have hcondθinv :
      (pullback.fst (pullback.snd f g) (eU.inv ≫ U.ι) ≫ pullback.fst f g ≫ eW.hom) ≫ s
        = pullback.snd (pullback.snd f g) (eU.inv ≫ U.ι) ≫ t := by
    rw [Category.assoc, Category.assoc, heW', pullback.condition, pullback.condition_assoc,
      Category.assoc, hU]
  let θhom : pullback s t ⟶ pullback (pullback.snd f g) (eU.inv ≫ U.ι) :=
    pullback.lift L (pullback.snd s t) hLsnd
  let θinv : pullback (pullback.snd f g) (eU.inv ≫ U.ι) ⟶ pullback s t :=
    pullback.lift (pullback.fst (pullback.snd f g) (eU.inv ≫ U.ι) ≫ pullback.fst f g ≫ eW.hom)
      (pullback.snd (pullback.snd f g) (eU.inv ≫ U.ι)) hcondθinv
  have hθhom_fst : θhom ≫ pullback.fst (pullback.snd f g) (eU.inv ≫ U.ι) = L := by
    dsimp only [θhom]; exact pullback.lift_fst _ _ _
  have hθhom_snd : θhom ≫ pullback.snd (pullback.snd f g) (eU.inv ≫ U.ι) = pullback.snd s t := by
    dsimp only [θhom]; exact pullback.lift_snd _ _ _
  have hθinv_fst : θinv ≫ pullback.fst s t
      = pullback.fst (pullback.snd f g) (eU.inv ≫ U.ι) ≫ pullback.fst f g ≫ eW.hom := by
    dsimp only [θinv]; exact pullback.lift_fst _ _ _
  have hθinv_snd : θinv ≫ pullback.snd s t = pullback.snd (pullback.snd f g) (eU.inv ≫ U.ι) := by
    dsimp only [θinv]; exact pullback.lift_snd _ _ _
  have hθinv_L : θinv ≫ L = pullback.fst (pullback.snd f g) (eU.inv ≫ U.ι) := by
    apply pullback.hom_ext
    · rw [Category.assoc, hLfst]
      dsimp only [θinv]
      rw [pullback.lift_fst_assoc, Category.assoc, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    · rw [Category.assoc, hLsnd]
      dsimp only [θinv]
      rw [pullback.lift_snd_assoc, pullback.condition]
  have hhom_inv : θhom ≫ θinv = 𝟙 (pullback s t) := by
    apply pullback.hom_ext
    · rw [Category.assoc, hθinv_fst, Category.id_comp]
      dsimp only [θhom]
      rw [pullback.lift_fst_assoc]
      dsimp only [L]
      rw [pullback.lift_fst_assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    · rw [Category.assoc, hθinv_snd, Category.id_comp]
      dsimp only [θhom]
      rw [pullback.lift_snd]
  have hinv_hom : θinv ≫ θhom = 𝟙 (pullback (pullback.snd f g) (eU.inv ≫ U.ι)) := by
    apply pullback.hom_ext
    · rw [Category.assoc, hθhom_fst, Category.id_comp]
      exact hθinv_L
    · rw [Category.assoc, hθhom_snd, Category.id_comp]
      dsimp only [θinv]
      rw [pullback.lift_snd]
  -- The chart map: the tensor product identification composed with `L`.
  haveI hIsoθhom : IsIso θhom := ⟨θinv, hhom_inv, hinv_hom⟩
  let Φ : Spec (CommRingCat.of (MvPolynomial σ 𝕜 ⊗[𝕜] A)) ⟶ pullback f g :=
    ((pullbackSpecIso 𝕜 (MvPolynomial σ 𝕜) A).inv ≫ θhom) ≫
      pullback.fst (pullback.snd f g) (eU.inv ≫ U.ι)
  have hΦ_eq : Φ = (pullbackSpecIso 𝕜 (MvPolynomial σ 𝕜) A).inv ≫ L := by
    dsimp only [Φ]
    rw [Category.assoc, hθhom_fst]
  have hΦopen : IsOpenImmersion Φ := by
    dsimp only [Φ]; infer_instance
  haveI hΦopenI : IsOpenImmersion Φ := hΦopen
  have hUι : (eU.inv ≫ U.ι).opensRange = U := by
    rw [Scheme.Hom.opensRange_comp_of_isIso, Scheme.Opens.opensRange_ι]
  have hρ : (pullback.fst (pullback.snd f g) (eU.inv ≫ U.ι)).opensRange
      = pullback.snd f g ⁻¹ᵁ U := by
    rw [Scheme.Hom.opensRange_pullbackFst, hUι]
  have hrange : Φ.opensRange = pullback.snd f g ⁻¹ᵁ U := by
    dsimp only [Φ]
    rw [Scheme.Hom.opensRange_comp_of_isIso, hρ]
  have hfst : Φ ≫ pullback.fst f g =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
        (R := 𝕜) (A := MvPolynomial σ 𝕜) (B := A))) ≫ eW.inv := by
    rw [hΦ_eq, Category.assoc, hLfst, ← Category.assoc, pullbackSpecIso_inv_fst]
  have hsnd : Φ ≫ pullback.snd f g =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
        (R := 𝕜) (A := MvPolynomial σ 𝕜) (B := A)).toRingHom) ≫ eU.inv ≫ U.ι := by
    rw [hΦ_eq, Category.assoc, hLsnd, ← Category.assoc, pullbackSpecIso_inv_snd]
    simp only [AlgHom.toRingHom_eq_coe]
  exact ⟨Φ, hΦopen, hrange, hfst, hsnd⟩

end Work.CY3Stab.Prod
