import Mathlib.FieldTheory.KrullTopology
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Valuation.ValuationSubring
import Submission.NK.FrobeniusBridge.Tame
import Submission.NeukirchUchida.Endgame
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The Frobenius bridge: the packaged endgame

This file plugs the deliverable `NK.FrobeniusBridge.frobeniusCorrespondencePlace` into the
endgame `Submission.NeukirchUchida.exists_sigma_of_reconstruction` of the Neukirch–Uchida theorem,
so that a caller who has

* the place correspondence `a` (input (a) of the endgame) and
* the bundle `NK.FrobeniusBridge.PlaceFrobeniusData` (the local–global dictionary at the places
  of the two fields together with the place-level Frobenius correspondence for `ϕ`),

and who produces the realizing field isomorphism `σ` (input (d), the deliverable of
`Submission/Work/ReconstructField/`), obtains the existence half of the theorem with no further
input.
-/

namespace NK.FrobeniusBridge

open scoped Classical Pointwise

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

variable {K₁ K₂ K₁' K₂' : Type*} [Field K₁] [Field K₂] [Field K₁'] [Field K₂']
  [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
  [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']

/-- **The endgame with the Frobenius bridge in place of the place-level Frobenius correspondence**:
inputs (a), the bridge bundle and the reconstruction (d) yield the existence half of
Neukirch–Uchida. -/
theorem exists_sigma_of_placeFrobeniusData (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂))
    (hϕ : IsHomeomorph ϕ) (a : NK.Reconstruct.LocalCorrespondence ϕ)
    (hB : PlaceFrobeniusData ϕ hϕ a)
    (d : ∃ (σ : K₂' ≃+* K₁')
      (_hσ : Submission.NeukirchUchida.MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂') σ),
      ∀ A : NK.Reconstruct.FinitePlaceOf K₁ K₁',
        (a.placeMap A).1.comap (σ.symm : K₁' →+* K₂') = A.1) :
    ∃ σ : K₂' ≃+* K₁', Submission.NeukirchUchida.Conjugates σ ϕ :=
  Submission.NeukirchUchida.exists_sigma_of_reconstruction ϕ hϕ a
    (frobeniusCorrespondencePlace ϕ hϕ a hB) d

/-- **The endgame with the local structure theory in place of the Frobenius correspondence**:
inputs (a), the local–global dictionary at the places of the two fields, the local structure theory
`NK.FrobeniusBridge.TameDataAtImage` and the reconstruction (d) yield the existence half of
Neukirch–Uchida. -/
theorem exists_sigma_of_tameData (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (hϕ : IsHomeomorph ϕ)
    (a : NK.Reconstruct.LocalCorrespondence ϕ)
    (hD₁ : ∀ A : FinitePlaceOf K₁ K₁', PlaceLevelBridge A)
    (hD₂ : ∀ B : FinitePlaceOf K₂ K₂', PlaceLevelBridge B)
    (hTame : TameDataAtImage a)
    (d : ∃ (σ : K₂' ≃+* K₁')
      (_hσ : Submission.NeukirchUchida.MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂') σ),
      ∀ A : NK.Reconstruct.FinitePlaceOf K₁ K₁',
        (a.placeMap A).1.comap (σ.symm : K₁' →+* K₂') = A.1) :
    ∃ σ : K₂' ≃+* K₁', Submission.NeukirchUchida.Conjugates σ ϕ :=
  exists_sigma_of_placeFrobeniusData ϕ hϕ a
    ⟨hD₁, hD₂, localFrobCorrespondencePlace_of_tameData (ϕ := ϕ) hϕ a hTame⟩ d

/-- **The endgame with the local structure theory at every place of `K₂'`** (the natural form of
the hypothesis). -/
theorem exists_sigma_of_tameData_atPlaces (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (hϕ : IsHomeomorph ϕ)
    (a : NK.Reconstruct.LocalCorrespondence ϕ)
    (hD₁ : ∀ A : FinitePlaceOf K₁ K₁', PlaceLevelBridge A)
    (hD₂ : ∀ B : FinitePlaceOf K₂ K₂', PlaceLevelBridge B)
    (hTame : TameDataAtPlaces K₂ K₂')
    (d : ∃ (σ : K₂' ≃+* K₁')
      (_hσ : Submission.NeukirchUchida.MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂') σ),
      ∀ A : NK.Reconstruct.FinitePlaceOf K₁ K₁',
        (a.placeMap A).1.comap (σ.symm : K₁' →+* K₂') = A.1) :
    ∃ σ : K₂' ≃+* K₁', Submission.NeukirchUchida.Conjugates σ ϕ :=
  exists_sigma_of_placeFrobeniusData ϕ hϕ a
    ⟨hD₁, hD₂, localFrobCorrespondencePlace_of_tameData_atPlaces hϕ a hTame⟩ d

/-- **The σ-based Frobenius correspondence** consumed by
`NK.Mine.exists_sigma_of_frobeniusCorrespondence`, from the bridge bundle: this is the interface
fit of the deliverable with the reconstruction
(`NK.Reconstruct.frobeniusCorrespondence_of_place`). -/
theorem frobeniusCorrespondence_of_placeFrobeniusData (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂))
    (hϕ : IsHomeomorph ϕ) (a : NK.Reconstruct.LocalCorrespondence ϕ)
    (hB : PlaceFrobeniusData ϕ hϕ a) (σ : K₂' ≃+* K₁')
    (hσ : Submission.NeukirchUchida.MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂') σ)
    (hreal : ∀ A : NK.Reconstruct.FinitePlaceOf K₁ K₁',
      (a.placeMap A).1.comap (σ.symm : K₁' →+* K₂') = A.1)
    (hlvl : NK.Reconstruct.AgreesOnLevels ϕ hϕ σ hσ) :
    NK.Reconstruct.FrobeniusCorrespondence ϕ σ :=
  NK.Reconstruct.frobeniusCorrespondence_of_place hϕ a σ hσ hreal hlvl
    (frobeniusCorrespondencePlace ϕ hϕ a hB)

end NK.FrobeniusBridge
