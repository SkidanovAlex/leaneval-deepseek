import Mathlib
import Submission.Work.ATOM.Defs

namespace Work.ATOM

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed
open _root_.LightCondensed
open Opposite

noncomputable section

/-!
# `P = ℤ[ℕ∪∞]/ℤ[∞]` is projective in `LightCondAb`

This is fact F4 of REFS/01: `Hom(P, -) ≅ Γ ∘ ihom P`, where `Γ = (-)(*)` is evaluation at the
point and `ihom P` preserves epimorphisms because `P` is internally projective.  `Γ` preserves
epimorphisms because every surjection of light profinite sets onto the point splits (F2).

We do not package the isomorphism `Hom(P, -) ≅ Γ ∘ ihom P` abstractly: we use the adjunction
`tensorLeft P ⊣ ihom P` together with the identification of the monoidal unit with `ℤ[*]`.
-/

/-- The point, as a light profinite set. -/
abbrev Point : LightProfinite.{0} := LightProfinite.of PUnit.{1}

/-- **F2.** Evaluation at the point preserves epimorphisms of light condensed abelian groups:
if `e : E ⟶ X` is an epimorphism, then `E(*) ⟶ X(*)` is surjective.

Indeed, epimorphisms of light condensed abelian groups are the locally surjective maps, so a
section `y` of `X` at the point is lifted after a surjection `S' ↠ *`, and every such surjection
splits (pick a point of `S'`). -/
theorem epi_pointSections_surjective {E X : LightCondAb} (e : E ⟶ X) [Epi e] :
    Function.Surjective (ConcreteCategory.hom (e.hom.app (op Point))) := by
  intro y
  obtain ⟨S', φ, hφ, x, hx⟩ :=
    (LightCondMod.epi_iff_locallySurjective_on_lightProfinite ℤ e).mp (inferInstance) Point y
  obtain ⟨s, _⟩ := hφ PUnit.unit
  let p : Point ⟶ S' := ConcreteCategory.ofHom ⟨fun _ => s, continuous_const⟩
  refine ⟨E.obj.map (op p) x, ?_⟩
  have hnat := NatTrans.naturality_apply e.hom (op p) x
  rw [hnat, hx]
  have hcomp : p ≫ φ = 𝟙 Point := LightProfinite.isTerminalPUnit.hom_ext _ _
  have hop : (op φ ≫ op p : op Point ⟶ op Point) = 𝟙 (op Point) :=
    (op_comp (f := p) (g := φ)).symm.trans (by rw [hcomp]; exact op_id)
  rw [← ModuleCat.comp_apply, ← Functor.map_comp, hop]
  simp

/-- The monoidal unit of `LightCondAb` is `ℤ[*] = ℤ[pt]`: the monoidal functor `free ℤ` sends the
unit of `LightCondSet` (the point, by compatibility of `lightProfiniteToLightCondSet`) to the free
object on the point. -/
noncomputable def unitIso : 𝟙_ LightCondAb ≅ (free ℤ).obj Point.toCondensed :=
  (Functor.Monoidal.εIso (free ℤ)) ≪≫
    (free ℤ).mapIso (Functor.Monoidal.εIso lightProfiniteToLightCondSet)

/-- Naturality of `Hom(ℤ[S], -) ≅ (-)(S)` in the target: a morphism into `Z` is sent to the
composite with `Y ⟶ Z`, which on sections is the application of the map on sections. -/
theorem homFreeEquiv_naturality_target (S : LightProfinite.{0}) {Y Z : LightCondAb} (h : Y ⟶ Z)
    (g : zfree S ⟶ Y) :
    homFreeEquiv S Z (g ≫ h) = h.hom.app (op S) (homFreeEquiv S Y g) := by
  show (coherentTopology LightProfinite).yonedaEquiv
      ((freeForgetAdjunction ℤ).homEquiv S.toCondensed Z (g ≫ h)) =
    (ConcreteCategory.hom (h.hom.app (op S)))
      ((coherentTopology LightProfinite).yonedaEquiv
        ((freeForgetAdjunction ℤ).homEquiv S.toCondensed Y g))
  rw [Adjunction.homEquiv_naturality_right]
  exact GrothendieckTopology.yonedaEquiv_comp (coherentTopology LightProfinite)
    (((freeForgetAdjunction ℤ).homEquiv S.toCondensed Y) g) ((LightCondensed.forget ℤ).map h)

/-- `Hom(𝟙, Y) ≃ Y(*)`: since `𝟙 ≅ ℤ[pt]`, this is `Hom(ℤ[pt], Y) ≃ Y(pt)`. -/
noncomputable def toPointEquiv (Y : LightCondAb) :
    (𝟙_ LightCondAb ⟶ Y) ≃ ↥(Y.obj.obj (op Point)) where
  toFun u := homFreeEquiv Point Y (unitIso.inv ≫ u)
  invFun z := unitIso.hom ≫ (homFreeEquiv Point Y).symm z
  left_inv u := by simp
  right_inv z := by simp

@[simp]
theorem toPointEquiv_apply (Y : LightCondAb) (u : 𝟙_ LightCondAb ⟶ Y) :
    toPointEquiv Y u = homFreeEquiv Point Y (unitIso.inv ≫ u) := rfl

/-- Naturality of `Hom(𝟙, -) ≃ (-)(*)`. -/
theorem toPointEquiv_naturality {Y Z : LightCondAb} (h : Y ⟶ Z) (u : 𝟙_ LightCondAb ⟶ Y) :
    toPointEquiv Z (u ≫ h) = h.hom.app (op Point) (toPointEquiv Y u) := by
  rw [toPointEquiv_apply, toPointEquiv_apply, ← Category.assoc, homFreeEquiv_naturality_target]

/-- `Hom(𝟙, -)` preserves epimorphisms, i.e. the monoidal unit `ℤ[*]` is projective. -/
theorem epi_unit_hom_surjective {E X : LightCondAb} (e : E ⟶ X) [Epi e] :
    Function.Surjective (fun (u : 𝟙_ LightCondAb ⟶ E) => u ≫ e) := by
  intro v
  obtain ⟨w, hw⟩ := epi_pointSections_surjective e (toPointEquiv X v)
  refine ⟨(toPointEquiv E).symm w, (toPointEquiv X).injective ?_⟩
  rw [toPointEquiv_naturality, Equiv.apply_symm_apply, hw]

/-- `Hom(P, X) ≃ Hom(𝟙, ihom P X)`, from the right unitor `P ⊗ 𝟙 ≅ P` and the adjunction
`tensorLeft P ⊣ ihom P`. -/
noncomputable def homEquivTensorUnit (X : LightCondAb) :
    (P ⟶ X) ≃ (𝟙_ LightCondAb ⟶ (ihom P).obj X) where
  toFun g := (ihom.adjunction P).homEquiv (𝟙_ LightCondAb) X ((rightUnitor P).hom ≫ g)
  invFun v := (rightUnitor P).inv ≫ ((ihom.adjunction P).homEquiv (𝟙_ LightCondAb) X).symm v
  left_inv g := by simp
  right_inv v := by simp

@[simp]
theorem homEquivTensorUnit_apply (X : LightCondAb) (g : P ⟶ X) :
    homEquivTensorUnit X g =
      (ihom.adjunction P).homEquiv (𝟙_ LightCondAb) X ((rightUnitor P).hom ≫ g) := rfl

/-- Naturality of `Hom(P, -) ≃ Hom(𝟙, ihom P -)`. -/
theorem homEquivTensorUnit_naturality {X Z : LightCondAb} (g : P ⟶ X) (h : X ⟶ Z) :
    homEquivTensorUnit Z (g ≫ h) = homEquivTensorUnit X g ≫ (ihom P).map h := by
  rw [homEquivTensorUnit_apply, homEquivTensorUnit_apply, ← Category.assoc]
  rw [Adjunction.homEquiv_naturality_right]

set_option linter.style.haveILetI false in
/-- `P = ℤ[ℕ∪∞]/ℤ[∞]` is a projective object of `LightCondAb`
(REFS/01 F4: `P` is a retract of the internally projective `ℤ[ℕ∪∞]`, and sections at the point
are exact because every surjection onto the point splits). -/
theorem projective_P : CategoryTheory.Projective LightCondensed.P := by
  refine ⟨fun {E X} f e => ?_⟩
  intro he
  haveI : Epi e := he
  obtain ⟨w, hw⟩ :=
    epi_unit_hom_surjective ((ihom P).map e) (homEquivTensorUnit X f)
  exact ⟨(homEquivTensorUnit E).symm w, by
    apply (homEquivTensorUnit X).injective
    rw [homEquivTensorUnit_naturality, Equiv.apply_symm_apply]
    exact hw⟩

end

end Work.ATOM
