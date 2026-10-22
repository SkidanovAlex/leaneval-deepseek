import Mathlib
import Submission.Work.ANALYTIC.CechPt.DdZfAux
import Submission.Work.ANALYTIC.CechPt.PgU_isIso

/-!
# The canonical comparison `(∐_j Z ⟹ Z) ⟶ ∏_j Z` is an isomorphism

Let `Z = 𝟙_ LightCondAb = ℤ` be the monoidal unit of light condensed abelian groups (written
`Work.ANALYTIC.Z`; it is *definitionally* the unit object).  For any index type `J` the morphism

`Pi.lift (fun j => (pre (ι_j)).app Z ≫ (unitIsoSelf Z).hom) : (∐_j Z ⟹ Z) ⟶ ∏_j Z`

is an isomorphism.  Its `j`-th component sends `λ : (∐_j Z) ⟹ Z` to the functional
`λ ∘ ι_j : Z ⟹ Z = 𝟙 ⟹ Z` evaluated on the unit (`unitIsoSelf Z`).

The proof splits the morphism into the two canonical pieces

* `Pi.lift (fun j => (pre (ι_j)).app Z) : (∐_j Z ⟹ Z) ⟶ ∏_j (Z ⟹ Z)`, the comparison morphism
  expressing "the internal hom turns coproducts into products"; it is an isomorphism by
  `isIso_piLift_pre` (from `PgU_isIso.lean`, the image of the coproduct cocone under the right
  adjoint `[-, Z] = internalHom.flip.obj Z` being a limit cone), and
* `Pi.map (fun _ => (unitIsoSelf Z).hom) : ∏_j (Z ⟹ Z) ⟶ ∏_j Z`, a product of isomorphisms,

glued by the formal identity `pi_lift_comp_map`.
-/

namespace Work.ANALYTIC.CechPt

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed

noncomputable section

/-- `Pi.lift` of a family of composites is the composite of the two comparison morphisms
`Pi.lift` and `Pi.map`. -/
theorem pi_lift_comp_map {J : Type} {C : Type*} [Category C] {X : C} {f g : J → C}
    [HasProduct f] [HasProduct g] (p : ∀ j, X ⟶ f j) (q : ∀ j, f j ⟶ g j) :
    Pi.lift (fun j => p j ≫ q j) = Pi.lift p ≫ Limits.Pi.map q := by
  refine Pi.hom_ext _ _ (fun j => ?_)
  rw [Pi.lift_comp_π, Category.assoc, Limits.Pi.map_π, ← Category.assoc, Pi.lift_comp_π]

/-- `Pi.map` of the isomorphisms `(Z ⟹ Z) ≅ Z` is an isomorphism. -/
theorem isIso_piMap_unitIsoSelf (J : Type) :
    IsIso (Limits.Pi.map (fun _ : J => (MonoidalClosed.unitIsoSelf Work.ANALYTIC.Z).hom)) := by
  have h : Limits.Pi.map (fun _ : J => (MonoidalClosed.unitIsoSelf Work.ANALYTIC.Z).hom) =
      (Pi.mapIso (fun _ : J => MonoidalClosed.unitIsoSelf Work.ANALYTIC.Z)).hom := by
    refine Pi.hom_ext _ _ (fun j => ?_)
    rw [Pi.mapIso_hom_π, Limits.Pi.map_π]
  rw [h]
  exact (Pi.mapIso _).isIso_hom

theorem isIso_piLift_pre_sigma_unit (J : Type) :
    CategoryTheory.IsIso (CategoryTheory.Limits.Pi.lift (fun j : J =>
      CategoryTheory.CategoryStruct.comp
        ((CategoryTheory.MonoidalClosed.pre
          (CategoryTheory.Limits.Sigma.ι (fun _ : J => Work.ANALYTIC.Z) j)).app
            Work.ANALYTIC.Z)
        (CategoryTheory.MonoidalClosed.unitIsoSelf Work.ANALYTIC.Z).hom)) := by
  rw [pi_lift_comp_map
    (fun j : J =>
      (MonoidalClosed.pre (Sigma.ι (fun _ : J => Work.ANALYTIC.Z) j)).app Work.ANALYTIC.Z)
    (fun _ : J => (MonoidalClosed.unitIsoSelf Work.ANALYTIC.Z).hom)]
  exact IsIso.comp_isIso'
    (isIso_piLift_pre J (fun _ : J => Work.ANALYTIC.Z) Work.ANALYTIC.Z)
    (isIso_piMap_unitIsoSelf J)

end

end Work.ANALYTIC.CechPt
