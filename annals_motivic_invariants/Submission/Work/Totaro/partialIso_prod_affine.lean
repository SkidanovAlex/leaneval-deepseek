import Mathlib
import Submission.Work.Totaro.Defs
import Submission.Work.K3.BaseChangeBirational
import Submission.Work.K3.partialIso_baseChangeAlong

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Birationality is preserved by multiplication by affine space

`Work.Totaro.partialIso_prod_affine`: a partial isomorphism `i : X ⤏ Y` between two `𝕜`-varieties
induces one between `X × 𝔸ⁿ` and `Y × 𝔸ⁿ`.

Mathlib's `PartialIso` API has no product, so this is done through the *functoriality of the
fibre product in the base*: the projection `X ×_𝕜 𝔸ⁿ ⟶ X` exhibits `X ×_𝕜 𝔸ⁿ` as the base change
of `X` (a `Spec ℤ`-scheme, `Spec ℤ` being the terminal object of the category of schemes) along the
morphism `𝔸ⁿ_ℤ ⟶ Spec ℤ`, and the base change of a partial isomorphism along a surjective
universally open morphism is a partial isomorphism
(`Work.K3.partialIso_baseChangeAlong`).

The two ingredients are `Work.Totaro.prodOver_affineN_iso`, the (canonical) identification of
`X ×_𝕜 𝔸ⁿ` with that base change — proved here by pasting pullback squares, using Mathlib's
`AlgebraicGeometry.AffineSpace.isPullback_map` (which says that the affine space over `Spec 𝕜` *is*
the base change of the affine space over `Spec ℤ`) — and the fact that `Spec ℤ` is terminal, so
that the structure morphisms of `X` and `Y` can be composed with `Spec 𝕜 ⟶ Spec ℤ` and every
morphism of schemes is automatically a `Spec ℤ`-morphism.

This is the missing step which makes stable birationality (`Work.Totaro.StablyBirational`) an
equivalence relation — see `Work.Totaro.stablyBirational_trans`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
attribute [instance] MotivicInvariants.Variety.over MotivicInvariants.Variety.isIntegral

namespace Work.Totaro

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
  MotivicInvariants

noncomputable section

variable {𝕜 : Type} [Field 𝕜]

/-! ## The `ℤ`-model of the situation -/

/-- The structure morphism `Spec 𝕜 ⟶ Spec ℤ`. -/
abbrev specZMap : Spec (CommRingCat.of 𝕜) ⟶ Spec (CommRingCat.of ℤ) :=
  Spec.map (CommRingCat.ofHom (Int.castRingHom 𝕜))

/-- `Spec ℤ`, the terminal scheme. -/
abbrev SpecZ : Scheme.{0} := Spec (CommRingCat.of ℤ)

/-- **`Spec ℤ` is the terminal scheme**, so any two morphisms into it are equal.  This is what
makes every partial map between schemes automatically a `Spec ℤ`-map: both sides of the equation
`f.iso.hom ≫ f.target.ι ≫ Y ↘ Spec ℤ = f.source.ι ≫ X ↘ Spec ℤ` are morphisms into `Spec ℤ`. -/
lemma specZ_hom_ext {X : Scheme.{0}} (f g : X ⟶ Spec (CommRingCat.of ℤ)) : f = g :=
  AlgebraicGeometry.specZIsTerminal.hom_ext f g

/-- Affine `n`-space over `ℤ`, the `ℤ`-model of `𝔸ⁿ`. -/
abbrev AffineNZ (n : ℕ) : Scheme.{0} := 𝔸(Fin n; Spec (CommRingCat.of ℤ))

/-- The structure morphism `𝔸ⁿ_ℤ ⟶ Spec ℤ`, i.e. the base we base-change along. -/
abbrev affineNZMap (n : ℕ) : AffineNZ n ⟶ Spec (CommRingCat.of ℤ) :=
  AffineNZ n ↘ Spec (CommRingCat.of ℤ)

/-- **The base-change model of `X × 𝔸ⁿ`.**  For a `𝕜`-scheme `X`, the product `X ×_𝕜 𝔸ⁿ` with
affine `n`-space is the base change of `X` (regarded as a scheme over `Spec ℤ`, via
`Spec 𝕜 ⟶ Spec ℤ`) along the projection `𝔸ⁿ_ℤ ⟶ Spec ℤ`.

The proof is the pasting of pullback squares: `AffineSpace.isPullback_map` exhibits `𝔸ⁿ_𝕜` as the
fibre product `Spec 𝕜 ×_{Spec ℤ} 𝔸ⁿ_ℤ`, so `pullback s q ≅ 𝔸ⁿ_𝕜` over `Spec 𝕜`; substituting this
into the second leg of the fibre product defining `X ×_𝕜 𝔸ⁿ` and applying the associativity of the
fibre product (`pullbackRightPullbackFstIso`, i.e. `X ×_𝕜 (Spec 𝕜 ×_{Spec ℤ} 𝔸ⁿ_ℤ) ≅
X ×_{Spec ℤ} 𝔸ⁿ_ℤ`) gives the identification. -/
noncomputable def prodOver_affineN_iso (X : Scheme.{0}) [X.Over (Spec (.of 𝕜))] (n : ℕ) :
    Work.K3.prodOver 𝕜 X (AffineN 𝕜 n) ≅
      pullback (affineNZMap n) ((X ↘ Spec (.of 𝕜)) ≫ specZMap (𝕜 := 𝕜)) := by
  show pullback (X ↘ Spec (.of 𝕜)) (AffineN 𝕜 n ↘ Spec (.of 𝕜)) ≅
    pullback (affineNZMap n) ((X ↘ Spec (.of 𝕜)) ≫ specZMap (𝕜 := 𝕜))
  -- `𝔸ⁿ_𝕜` is the base change of `𝔸ⁿ_ℤ` along `Spec 𝕜 ⟶ Spec ℤ`
  have hpb := AffineSpace.isPullback_map (n := Fin n) (f := specZMap (𝕜 := 𝕜))
  let E : AffineN 𝕜 n ≅ pullback (affineNZMap n) (specZMap (𝕜 := 𝕜)) := hpb.isoPullback
  have hE2 : E.hom ≫ pullback.snd (affineNZMap n) (specZMap (𝕜 := 𝕜)) =
      AffineN 𝕜 n ↘ Spec (.of 𝕜) := hpb.isoPullback_hom_snd
  -- the transport of the affine space to the shape in which the pasting applies
  let j : AffineN 𝕜 n ≅ pullback (specZMap (𝕜 := 𝕜)) (affineNZMap n) :=
    E ≪≫ pullbackSymmetry (affineNZMap n) (specZMap (𝕜 := 𝕜))
  have hj : j.hom ≫ pullback.fst (specZMap (𝕜 := 𝕜)) (affineNZMap n) =
      AffineN 𝕜 n ↘ Spec (.of 𝕜) := by
    rw [Iso.trans_hom, Category.assoc, pullbackSymmetry_hom_comp_fst]
    exact hE2
  have hj' : j.inv ≫ (AffineN 𝕜 n ↘ Spec (.of 𝕜)) =
      pullback.fst (specZMap (𝕜 := 𝕜)) (affineNZMap n) :=
    (Iso.inv_comp_eq j).mpr hj.symm
  -- the comparison of the two fibre products over `Spec 𝕜`
  let Φ : pullback (X ↘ Spec (.of 𝕜)) (AffineN 𝕜 n ↘ Spec (.of 𝕜)) ⟶
      pullback (X ↘ Spec (.of 𝕜)) (pullback.fst (specZMap (𝕜 := 𝕜)) (affineNZMap n)) :=
    pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ j.hom) (by
      rw [Category.assoc, hj]
      exact pullback.condition)
  let Ψ : pullback (X ↘ Spec (.of 𝕜)) (pullback.fst (specZMap (𝕜 := 𝕜)) (affineNZMap n)) ⟶
      pullback (X ↘ Spec (.of 𝕜)) (AffineN 𝕜 n ↘ Spec (.of 𝕜)) :=
    pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ j.inv) (by
      rw [Category.assoc, hj']
      exact pullback.condition)
  have hΦf : Φ ≫ pullback.fst _ _ = pullback.fst _ _ := pullback.lift_fst _ _ _
  have hΦs : Φ ≫ pullback.snd _ _ = pullback.snd _ _ ≫ j.hom := pullback.lift_snd _ _ _
  have hΨf : Ψ ≫ pullback.fst _ _ = pullback.fst _ _ := pullback.lift_fst _ _ _
  have hΨs : Ψ ≫ pullback.snd _ _ = pullback.snd _ _ ≫ j.inv := pullback.lift_snd _ _ _
  have hΦΨ : Φ ≫ Ψ = 𝟙 _ := by
    apply pullback.hom_ext
    · calc (Φ ≫ Ψ) ≫ pullback.fst _ _
          = Φ ≫ (Ψ ≫ pullback.fst _ _) := Category.assoc ..
        _ = Φ ≫ pullback.fst _ _ := by rw [hΨf]
        _ = pullback.fst _ _ := hΦf
        _ = 𝟙 _ ≫ pullback.fst _ _ := (Category.id_comp _).symm
    · calc (Φ ≫ Ψ) ≫ pullback.snd _ _
          = Φ ≫ (Ψ ≫ pullback.snd _ _) := Category.assoc ..
        _ = Φ ≫ (pullback.snd _ _ ≫ j.inv) := by rw [hΨs]
        _ = (Φ ≫ pullback.snd _ _) ≫ j.inv := (Category.assoc ..).symm
        _ = (pullback.snd _ _ ≫ j.hom) ≫ j.inv := by rw [hΦs]
        _ = pullback.snd _ _ ≫ (j.hom ≫ j.inv) := Category.assoc ..
        _ = pullback.snd _ _ ≫ 𝟙 _ := by rw [j.hom_inv_id]
        _ = pullback.snd _ _ := Category.comp_id ..
        _ = 𝟙 _ ≫ pullback.snd _ _ := (Category.id_comp _).symm
  have hΨΦ : Ψ ≫ Φ = 𝟙 _ := by
    apply pullback.hom_ext
    · calc (Ψ ≫ Φ) ≫ pullback.fst _ _
          = Ψ ≫ (Φ ≫ pullback.fst _ _) := Category.assoc ..
        _ = Ψ ≫ pullback.fst _ _ := by rw [hΦf]
        _ = pullback.fst _ _ := hΨf
        _ = 𝟙 _ ≫ pullback.fst _ _ := (Category.id_comp _).symm
    · calc (Ψ ≫ Φ) ≫ pullback.snd _ _
          = Ψ ≫ (Φ ≫ pullback.snd _ _) := Category.assoc ..
        _ = Ψ ≫ (pullback.snd _ _ ≫ j.hom) := by rw [hΦs]
        _ = (Ψ ≫ pullback.snd _ _) ≫ j.hom := (Category.assoc ..).symm
        _ = (pullback.snd _ _ ≫ j.inv) ≫ j.hom := by rw [hΨs]
        _ = pullback.snd _ _ ≫ (j.inv ≫ j.hom) := Category.assoc ..
        _ = pullback.snd _ _ ≫ 𝟙 _ := by rw [j.inv_hom_id]
        _ = pullback.snd _ _ := Category.comp_id ..
        _ = 𝟙 _ ≫ pullback.snd _ _ := (Category.id_comp _).symm
  -- the associativity of the fibre product over the two bases
  exact Iso.mk Φ Ψ hΦΨ hΨΦ ≪≫
    pullbackRightPullbackFstIso (specZMap (𝕜 := 𝕜)) (affineNZMap n) (X ↘ Spec (.of 𝕜)) ≪≫
    pullbackSymmetry _ _

/-- **Birationality is preserved by multiplication by affine space.**  A partial isomorphism `i : X ⤏ Y` (an isomorphism of dense open subschemes) induces one between `X × 𝔸ⁿ` and `Y × 𝔸ⁿ`: take the base change of the two open subschemes along the projection to `𝕜`; the source stays dense because the base change is over `Spec 𝕜` (the fibre product of two nonempty opens over a point has points, and `X × 𝔸ⁿ` is irreducible) and the two open subschemes are isomorphic by the base change of `i.iso`.  Mathlib's `PartialIso` API has no product, so this is the missing step which makes stable birationality (`Work.Totaro.StablyBirational`) an equivalence relation — see `Work.Totaro.stablyBirational_trans`. -/
theorem partialIso_prod_affine {𝕜 : Type} [Field 𝕜] {X Y : AlgebraicGeometry.Scheme.{0}}
    [MotivicInvariants.Variety 𝕜 X] [MotivicInvariants.Variety 𝕜 Y] (i : X.PartialIso Y) (n : ℕ) :
    Nonempty ((Work.Totaro.prodOver 𝕜 X (Work.Totaro.AffineN 𝕜 n)).PartialIso
      (Work.Totaro.prodOver 𝕜 Y (Work.Totaro.AffineN 𝕜 n))) := by
  -- Regard `X` and `Y` as schemes over `Spec ℤ`.
  letI hXz : X.Over SpecZ := ⟨(X ↘ Spec (.of 𝕜)) ≫ specZMap (𝕜 := 𝕜)⟩
  letI hYz : Y.Over SpecZ := ⟨(Y ↘ Spec (.of 𝕜)) ≫ specZMap (𝕜 := 𝕜)⟩
  -- The base change morphism `𝔸ⁿ_ℤ ⟶ Spec ℤ` is surjective and universally open, and every
  -- partial map of schemes is a `Spec ℤ`-map since `Spec ℤ` is terminal.
  haveI hSurj : Surjective (affineNZMap n) := inferInstance
  haveI hOpen : UniversallyOpen (affineNZMap n) := inferInstance
  haveI hIsOver : i.toPartialMap.IsOver SpecZ := ⟨specZ_hom_ext _ _⟩
  -- Base change of the partial isomorphism along `𝔸ⁿ_ℤ ⟶ Spec ℤ`.
  obtain ⟨h, -, -, -⟩ := Work.K3.partialIso_baseChangeAlong (f := affineNZMap n) i hIsOver
  -- Identify the two base changes with the products.
  have eX : Work.K3.prodOver 𝕜 X (AffineN 𝕜 n) ≅
      Work.K3.baseChangeAlong (affineNZMap n) X := by
    show Work.K3.prodOver 𝕜 X (AffineN 𝕜 n) ≅ pullback (affineNZMap n) (X ↘ SpecZ)
    exact prodOver_affineN_iso (𝕜 := 𝕜) X n
  have eY : Work.K3.prodOver 𝕜 Y (AffineN 𝕜 n) ≅
      Work.K3.baseChangeAlong (affineNZMap n) Y := by
    show Work.K3.prodOver 𝕜 Y (AffineN 𝕜 n) ≅ pullback (affineNZMap n) (Y ↘ SpecZ)
    exact prodOver_affineN_iso (𝕜 := 𝕜) Y n
  exact ⟨(PartialIso.ofIso eX).trans (h.trans (PartialIso.ofIso eY.symm))⟩

end

end Work.Totaro
