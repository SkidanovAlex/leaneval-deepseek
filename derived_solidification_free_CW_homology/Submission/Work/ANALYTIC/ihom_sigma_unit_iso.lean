import Mathlib
import Submission.Work.ANALYTIC.ihom_coprod_iso
import Submission.Work.TOOLKIT.Instances

namespace Work.ANALYTIC

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed

/-- The internal hom out of a finite coproduct of copies of the monoidal unit is that coproduct:
`[∐_ι 𝟙, 𝟙] ≅ ∐_ι 𝟙`.  (`ihom_coprod_iso` gives the product; the finite index and additivity of
`LightCondAb` convert product into coproduct.) -/
theorem ihom_sigma_unit_iso (ι : Type) [Finite ι] :
    Nonempty ((CategoryTheory.ihom (CategoryTheory.Limits.sigmaObj (fun _ : ι => (𝟙_ LightCondAb)))).obj
        (𝟙_ LightCondAb) ≅
      CategoryTheory.Limits.sigmaObj (fun _ : ι => (𝟙_ LightCondAb))) := by
  classical
  -- the product over `ι` of `𝟙_ LightCondAb` exists
  have hprod : HasProduct (fun _ : ι => (𝟙_ LightCondAb)) := inferInstance
  -- hence so do the corresponding biproduct and coproduct (the index is finite)
  have hbiprod : HasBiproduct (fun _ : ι => (𝟙_ LightCondAb)) := HasBiproduct.of_hasProduct _
  have hcoprod : HasCoproduct (fun _ : ι => (𝟙_ LightCondAb)) := inferInstance
  -- and the product of internal homs `[𝟙, 𝟙]`
  have hprod' : HasProduct (fun _ : ι => (ihom (𝟙_ LightCondAb)).obj (𝟙_ LightCondAb)) :=
    inferInstance
  -- the internal hom out of a coproduct is the product of the internal homs
  obtain ⟨e₁⟩ := ihom_coprod_iso ι (fun _ : ι => (𝟙_ LightCondAb)) (𝟙_ LightCondAb)
  -- `[𝟙, 𝟙] ≅ 𝟙`, hence the product of internal homs is the product of units
  have e₂ : (∏ᶜ fun _ : ι => (ihom (𝟙_ LightCondAb)).obj (𝟙_ LightCondAb)) ≅
      (∏ᶜ fun _ : ι => (𝟙_ LightCondAb)) :=
    Pi.mapIso fun _ => MonoidalClosed.unitIsoSelf (C := LightCondAb) (X := 𝟙_ LightCondAb)
  -- in an additive category a finite product is a coproduct
  exact ⟨e₁ ≪≫ e₂ ≪≫ biproductIso (fun _ : ι => (𝟙_ LightCondAb))⟩

end Work.ANALYTIC
