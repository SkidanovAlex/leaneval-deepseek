import Mathlib
import Submission.Work.K3Inputs.Defs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.K3Inputs

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

set_option autoImplicit false

noncomputable section

/-! ## Generic transport of a fibre product along an isomorphism of the second leg -/

/-- Given `f : X ⟶ S` and two morphisms `g₁ : Y₁ ⟶ S`, `g₂ : Y₂ ⟶ S` whose domains are
isomorphic by `τ` compatibly with `g₁`, `g₂`, the fibre products `X ×_S Y₁` and `X ×_S Y₂` are
isomorphic, and the isomorphism is compatible with the first projections. -/
theorem pullback_iso_of_iso_snd {C : Type*} [Category C] {S X Y₁ Y₂ : C}
    (f : X ⟶ S) (g₁ : Y₁ ⟶ S) (g₂ : Y₂ ⟶ S) [HasPullback f g₁] [HasPullback f g₂]
    (τ : Y₁ ≅ Y₂) (h : τ.hom ≫ g₂ = g₁) :
    ∃ e : pullback f g₁ ≅ pullback f g₂, e.hom ≫ pullback.fst f g₂ = pullback.fst f g₁ := by
  have h' : τ.inv ≫ g₁ = g₂ := by
    rw [← h, ← Category.assoc, τ.inv_hom_id, Category.id_comp]
  have w₁ : pullback.fst f g₁ ≫ f = (pullback.snd f g₁ ≫ τ.hom) ≫ g₂ := by
    rw [pullback.condition, Category.assoc, h]
  have w₂ : pullback.fst f g₂ ≫ f = (pullback.snd f g₂ ≫ τ.inv) ≫ g₁ := by
    rw [pullback.condition, Category.assoc, h']
  let φ : pullback f g₁ ⟶ pullback f g₂ :=
    pullback.lift (pullback.fst f g₁) (pullback.snd f g₁ ≫ τ.hom) w₁
  let ψ : pullback f g₂ ⟶ pullback f g₁ :=
    pullback.lift (pullback.fst f g₂) (pullback.snd f g₂ ≫ τ.inv) w₂
  have hφf : φ ≫ pullback.fst f g₂ = pullback.fst f g₁ := pullback.lift_fst _ _ _
  have hφs : φ ≫ pullback.snd f g₂ = pullback.snd f g₁ ≫ τ.hom := pullback.lift_snd _ _ _
  have hψf : ψ ≫ pullback.fst f g₁ = pullback.fst f g₂ := pullback.lift_fst _ _ _
  have hψs : ψ ≫ pullback.snd f g₁ = pullback.snd f g₂ ≫ τ.inv := pullback.lift_snd _ _ _
  have hφψ : φ ≫ ψ = 𝟙 (pullback f g₁) := by
    apply pullback.hom_ext
    · rw [Category.assoc, hψf, hφf, Category.id_comp]
    · calc (φ ≫ ψ) ≫ pullback.snd f g₁
          = φ ≫ (ψ ≫ pullback.snd f g₁) := Category.assoc _ _ _
        _ = φ ≫ (pullback.snd f g₂ ≫ τ.inv) := by rw [hψs]
        _ = (φ ≫ pullback.snd f g₂) ≫ τ.inv := (Category.assoc _ _ _).symm
        _ = (pullback.snd f g₁ ≫ τ.hom) ≫ τ.inv := by rw [hφs]
        _ = pullback.snd f g₁ ≫ (τ.hom ≫ τ.inv) := Category.assoc _ _ _
        _ = pullback.snd f g₁ ≫ 𝟙 Y₁ := by rw [τ.hom_inv_id]
        _ = pullback.snd f g₁ := Category.comp_id _
        _ = 𝟙 (pullback f g₁) ≫ pullback.snd f g₁ := (Category.id_comp _).symm
  have hψφ : ψ ≫ φ = 𝟙 (pullback f g₂) := by
    apply pullback.hom_ext
    · rw [Category.assoc, hφf, hψf, Category.id_comp]
    · calc (ψ ≫ φ) ≫ pullback.snd f g₂
          = ψ ≫ (φ ≫ pullback.snd f g₂) := Category.assoc _ _ _
        _ = ψ ≫ (pullback.snd f g₁ ≫ τ.hom) := by rw [hφs]
        _ = (ψ ≫ pullback.snd f g₁) ≫ τ.hom := (Category.assoc _ _ _).symm
        _ = (pullback.snd f g₂ ≫ τ.inv) ≫ τ.hom := by rw [hψs]
        _ = pullback.snd f g₂ ≫ (τ.inv ≫ τ.hom) := Category.assoc _ _ _
        _ = pullback.snd f g₂ ≫ 𝟙 Y₂ := by rw [τ.inv_hom_id]
        _ = pullback.snd f g₂ := Category.comp_id _
        _ = 𝟙 (pullback f g₂) ≫ pullback.snd f g₂ := (Category.id_comp _).symm
  exact ⟨Iso.mk φ ψ hφψ hψφ, hφf⟩

/-! ## `Spec 𝕜[t]` and `Spec (MvPolynomial (Fin 1) 𝕜)` -/

/-- The `𝕜`-algebra equivalence `MvPolynomial (Fin 1) 𝕜 ≃ₐ[𝕜] Polynomial 𝕜`, sending the
variable to the variable. -/
def mvPolynomialFinOneAlgEquiv (𝕜 : Type) [Field 𝕜] :
    MvPolynomial (Fin 1) 𝕜 ≃ₐ[𝕜] Polynomial 𝕜 :=
  (MvPolynomial.finSuccEquiv 𝕜 0).trans
    (Polynomial.mapAlgEquiv (MvPolynomial.isEmptyAlgEquiv 𝕜 (Fin 0)))

/-- `Spec (MvPolynomial (Fin 1) 𝕜) ≅ Spec 𝕜[t]`, compatible with the structure maps
`↘ Spec 𝕜`. -/
theorem specMvPolynomialIsoPolynomial_over (𝕜 : Type) [Field 𝕜] :
    ∃ ψ : Spec (CommRingCat.of (MvPolynomial (Fin 1) 𝕜)) ≅
        Spec (CommRingCat.of (Polynomial 𝕜)),
      ψ.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap 𝕜 (Polynomial 𝕜))) =
        Spec.map (CommRingCat.ofHom (MvPolynomial.C : 𝕜 →+* MvPolynomial (Fin 1) 𝕜)) := by
  let φ := mvPolynomialFinOneAlgEquiv 𝕜
  have hcomp₁ : CommRingCat.ofHom (φ.toRingEquiv : MvPolynomial (Fin 1) 𝕜 →+* Polynomial 𝕜) ≫
      CommRingCat.ofHom (φ.symm.toRingEquiv : Polynomial 𝕜 →+* MvPolynomial (Fin 1) 𝕜) =
      𝟙 (CommRingCat.of (MvPolynomial (Fin 1) 𝕜)) := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    simp
  have hcomp₂ : CommRingCat.ofHom (φ.symm.toRingEquiv : Polynomial 𝕜 →+* MvPolynomial (Fin 1) 𝕜) ≫
      CommRingCat.ofHom (φ.toRingEquiv : MvPolynomial (Fin 1) 𝕜 →+* Polynomial 𝕜) =
      𝟙 (CommRingCat.of (Polynomial 𝕜)) := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    simp
  have h₁ : Spec.map (CommRingCat.ofHom (φ.symm.toRingEquiv : Polynomial 𝕜 →+* MvPolynomial (Fin 1) 𝕜)) ≫
      Spec.map (CommRingCat.ofHom (φ.toRingEquiv : MvPolynomial (Fin 1) 𝕜 →+* Polynomial 𝕜)) =
      𝟙 (Spec (CommRingCat.of (MvPolynomial (Fin 1) 𝕜))) := by
    rw [← Spec.map_comp, hcomp₁, Spec.map_id]
  have h₂ : Spec.map (CommRingCat.ofHom (φ.toRingEquiv : MvPolynomial (Fin 1) 𝕜 →+* Polynomial 𝕜)) ≫
      Spec.map (CommRingCat.ofHom (φ.symm.toRingEquiv : Polynomial 𝕜 →+* MvPolynomial (Fin 1) 𝕜)) =
      𝟙 (Spec (CommRingCat.of (Polynomial 𝕜))) := by
    rw [← Spec.map_comp, hcomp₂, Spec.map_id]
  refine ⟨Iso.mk _ _ h₁ h₂, ?_⟩
  rw [← Spec.map_comp]
  have hring : CommRingCat.ofHom (algebraMap 𝕜 (Polynomial 𝕜)) ≫
      CommRingCat.ofHom (φ.symm.toRingEquiv : Polynomial 𝕜 →+* MvPolynomial (Fin 1) 𝕜) =
      CommRingCat.ofHom (MvPolynomial.C : 𝕜 →+* MvPolynomial (Fin 1) 𝕜) := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro c
    change φ.symm (algebraMap 𝕜 (Polynomial 𝕜) c) = MvPolynomial.C c
    rw [AlgEquiv.commutes, MvPolynomial.algebraMap_eq]
  rw [hring]

/-- The affine line `𝔸¹_𝕜 = 𝔸(Fin 1; Spec 𝕜)` is `Spec 𝕜[t]`, compatibly with `↘ Spec 𝕜`. -/
theorem affine1_iso_specPolynomial (𝕜 : Type) [Field 𝕜] :
    ∃ τ : Affine1 𝕜 ≅ Spec (CommRingCat.of (Polynomial 𝕜)),
      τ.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap 𝕜 (Polynomial 𝕜))) =
        CategoryTheory.over (Affine1 𝕜) (Spec (CommRingCat.of 𝕜)) := by
  obtain ⟨ψ, hψ⟩ := specMvPolynomialIsoPolynomial_over 𝕜
  let σ : Affine1 𝕜 ≅ Spec (CommRingCat.of (MvPolynomial (Fin 1) 𝕜)) :=
    AffineSpace.SpecIso (Fin 1) (CommRingCat.of 𝕜)
  have hσ : σ.inv ≫ CategoryTheory.over (Affine1 𝕜) (Spec (CommRingCat.of 𝕜)) =
      Spec.map (CommRingCat.ofHom (MvPolynomial.C : 𝕜 →+* MvPolynomial (Fin 1) 𝕜)) :=
    AffineSpace.SpecIso_inv_over (CommRingCat.of 𝕜)
  refine ⟨σ.trans ψ, ?_⟩
  rw [Iso.trans_hom, Category.assoc, hψ]
  rw [← hσ, ← Category.assoc, σ.hom_inv_id, Category.id_comp]

/-- **The cylinder `Cyl 𝕜 X = X ×_𝕜 𝔸¹` is the fibre product of `X` with `Spec 𝕜[t]`.**

`Work.K3Inputs.Cyl 𝕜 X` is defined as `Work.K3.prodOver 𝕜 X (Work.K3Inputs.Affine1 𝕜)`, i.e. the
pullback of `X ↘ Spec 𝕜` with `𝔸(Fin 1; Spec 𝕜) ↘ Spec 𝕜`; here `𝔸(Fin 1; Spec 𝕜)` is replaced by
the standard affine line `Spec 𝕜[t]`.  The second component of the conclusion is the compatibility
with the first projections, i.e. the isomorphism is over `Spec 𝕜` for the canonical `Over`
structures (`Work.K3Inputs.cylOver` on the left).

Suggested route: `AlgebraicGeometry.AffineSpace.SpecIso (Fin 1) 𝕜` gives
`𝔸(Fin 1; Spec 𝕜) ≅ Spec (MvPolynomial (Fin 1) 𝕜)`, and
`MvPolynomial.finSuccEquiv 𝕜 0` composed with `MvPolynomial.isEmptyAlgEquiv` (or
`MvPolynomial.uniqueAlgEquiv` at `Fin 0`) identifies `MvPolynomial (Fin 1) 𝕜` with `Polynomial 𝕜`;
`AlgebraicGeometry.AffineSpace.SpecIso_inv_over` (or `_over`/`map_over`) records that this
isomorphism is compatible with the structure maps `↘ Spec 𝕜`.  Then transport the second factor
along that isomorphism using the pullback-congruence of `CategoryTheory.Limits.pullback`
(`CategoryTheory.Limits.pullback.congrHom`/`pullback.map` with `𝟙` on the first factor), and use
`CategoryTheory.Limits.pullback.lift_fst`/`pullback.hom_ext` for the compatibility. -/
theorem cylIsoPullbackAffineLine (𝕜 : Type) [Field 𝕜] (X : AlgebraicGeometry.Scheme)
    [AlgebraicGeometry.Scheme.Over X (AlgebraicGeometry.Spec (CommRingCat.of 𝕜))] :
    ∃ e : CategoryTheory.Iso (Work.K3Inputs.Cyl 𝕜 X) (CategoryTheory.Limits.pullback
        (CategoryTheory.over X (AlgebraicGeometry.Spec (CommRingCat.of 𝕜)))
        (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap 𝕜 (Polynomial 𝕜))))),
      CategoryTheory.CategoryStruct.comp e.hom (CategoryTheory.CategoryStruct.comp
        (CategoryTheory.Limits.pullback.fst
          (CategoryTheory.over X (AlgebraicGeometry.Spec (CommRingCat.of 𝕜)))
          (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap 𝕜 (Polynomial 𝕜)))))
        (CategoryTheory.over X (AlgebraicGeometry.Spec (CommRingCat.of 𝕜)))) =
      CategoryTheory.over (Work.K3Inputs.Cyl 𝕜 X) (AlgebraicGeometry.Spec (CommRingCat.of 𝕜)) := by
  obtain ⟨τ, hτ⟩ := affine1_iso_specPolynomial 𝕜
  obtain ⟨e, he⟩ := pullback_iso_of_iso_snd
    (CategoryTheory.over X (AlgebraicGeometry.Spec (CommRingCat.of 𝕜)))
    (CategoryTheory.over (Work.K3Inputs.Affine1 𝕜) (AlgebraicGeometry.Spec (CommRingCat.of 𝕜)))
    (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap 𝕜 (Polynomial 𝕜)))) τ hτ
  have hfin : e.hom ≫ CategoryTheory.Limits.pullback.fst
        (CategoryTheory.over X (AlgebraicGeometry.Spec (CommRingCat.of 𝕜)))
        (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap 𝕜 (Polynomial 𝕜)))) ≫
        CategoryTheory.over X (AlgebraicGeometry.Spec (CommRingCat.of 𝕜)) =
      CategoryTheory.over (Work.K3Inputs.Cyl 𝕜 X) (AlgebraicGeometry.Spec (CommRingCat.of 𝕜)) := by
    rw [← Category.assoc, he]
    rfl
  exact ⟨e, hfin⟩

end

end Work.K3Inputs
