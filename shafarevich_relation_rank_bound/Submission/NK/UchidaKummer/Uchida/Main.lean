/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The reconstruction `(d)` from the inputs of §6

Reference: arXiv:2601.01251, §5 (*Full Neukirch–Uchida*) and §6 (*Weak Neukirch–Uchida*).

This file combines

* `NK.UchidaKummer.nonempty_ringEquiv_of_uchidaModuleData_and_perlis_abs` — the weak
  Neukirch–Uchida theorem, from Uchida's module data (§6 Lemma 6.1 + `cor:arith equiv`) and the
  Perlis/Gassmann input;

with the σ-free assembly of `Submission.NK.UchidaKummer.Assembly`, to obtain the reconstruction
`(d)` of `Submission/NeukirchUchida/Endgame.lean` from

* `(A)` the local correspondence `NK.Reconstruct.LocalCorrespondence ϕ`;
* `IsUchidaModuleData ℓ`,
* `PerlisGassmannInput`,
* `μ_ℓ ⊆ K_i` and `ℓ` prime,
* the Jarden–Ritter rigidity `NK.Reconstruct.PlaceRigidity K₂ K₂'`.
-/

import Submission.NK.UchidaKummer.Uchida.Abstract
import Submission.NK.UchidaKummer.Assembly
import Submission.NK.UchidaKummer.WeakUchida.GassmannInput
import Submission.NK.FieldTheory.Galois.nonempty_mulEquiv_algEquiv_of_isSepClosure

noncomputable section

attribute [local instance] Classical.propDecidable

namespace NK.UchidaKummer

/-- **An isomorphism of absolute Galois groups gives `HasIsomorphicAbsGalois`.**  The given
isomorphism is transported to arbitrary choices of separable closure by uniqueness of the separable
closure (`NK.FieldTheory.Galois.nonempty_mulEquiv_algEquiv_of_isSepClosure`). -/
theorem hasIsomorphicAbsGalois_of_galoisEquiv {K₁ K₂ : Type*} [Field K₁] [NumberField K₁]
    [Field K₂] [NumberField K₂]
    {K₁' : Type*} [Field K₁'] [Algebra K₁ K₁'] [IsSepClosure K₁ K₁']
    {K₂' : Type*} [Field K₂'] [Algebra K₂ K₂'] [IsSepClosure K₂ K₂']
    (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) : HasIsomorphicAbsGalois K₁ K₂ := by
  intro A _ _ _ C _ _ _
  refine ⟨(NK.FieldTheory.Galois.nonempty_mulEquiv_algEquiv_of_isSepClosure
        (K := K₁) (L := A) (M := K₁')).some.trans (ϕ.trans ?_)⟩
  exact (NK.FieldTheory.Galois.nonempty_mulEquiv_algEquiv_of_isSepClosure
        (K := K₂) (L := C) (M := K₂')).some.symm

section Main

variable {K₁ K₂ K₁' K₂' : Type*} [Field K₁] [NumberField K₁] [Field K₂] [NumberField K₂]
  [Field K₁'] [Field K₂'] [Algebra K₁ K₁'] [Algebra K₂ K₂']
  [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']

/-- **The reconstruction `(d)` of Neukirch–Uchida from the inputs of §6.**

`(A)` the local correspondence, Uchida's module data, the Perlis/Gassmann input, `μ_ℓ ⊆ K_i` for
`ℓ` prime, and the Jarden–Ritter rigidity of the place system of `K₂'` produce a field isomorphism
`σ : K₂' ≃+* K₁'` which is `MapsBase` and realizes the whole place correspondence, and which induces
`ϕ` by conjugation.  This is exactly the input `d` consumed by
`Submission.NeukirchUchida.exists_sigma_of_reconstruction`. -/
theorem exists_sigma_of_uchidaModuleData_and_perlis {ℓ : ℕ} [Fact ℓ.Prime]
    (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (hϕ : IsHomeomorph ϕ)
    (a : NK.Reconstruct.LocalCorrespondence ϕ)
    (hU : IsUchidaModuleData ℓ) (hP : PerlisGassmannInput)
    (hμ₁ : ∃ ζ : K₁, IsPrimitiveRoot ζ ℓ) (hμ₂ : ∃ ζ : K₂, IsPrimitiveRoot ζ ℓ)
    (hR : NK.Reconstruct.PlaceRigidity K₂ K₂') :
    ∃ (σ : K₂' ≃+* K₁')
      (_hσ : Submission.NeukirchUchida.MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂') σ),
      (∀ A : NK.Reconstruct.FinitePlaceOf K₁ K₁',
        (a.placeMap A).1.comap (σ.symm : K₁' →+* K₂') = A.1) ∧
      Submission.NeukirchUchida.Conjugates σ ϕ :=
  exists_sigma_of_kummerRoute_of_weakIso_and_placeRigidity_realizesPlaceMap ϕ hϕ a
    (nonempty_ringEquiv_of_uchidaModuleData_and_perlis_abs hU hP K₁ K₂ hμ₁ hμ₂
      (hasIsomorphicAbsGalois_of_galoisEquiv ϕ)) hR

/-- The `Conjugates` form of `exists_sigma_of_uchidaModuleData_and_perlis`. -/
theorem exists_conjugates_of_uchidaModuleData_and_perlis {ℓ : ℕ} [Fact ℓ.Prime]
    (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (hϕ : IsHomeomorph ϕ)
    (a : NK.Reconstruct.LocalCorrespondence ϕ)
    (hU : IsUchidaModuleData ℓ) (hP : PerlisGassmannInput)
    (hμ₁ : ∃ ζ : K₁, IsPrimitiveRoot ζ ℓ) (hμ₂ : ∃ ζ : K₂, IsPrimitiveRoot ζ ℓ)
    (hR : NK.Reconstruct.PlaceRigidity K₂ K₂') :
    ∃ σ : K₂' ≃+* K₁', Submission.NeukirchUchida.Conjugates σ ϕ := by
  obtain ⟨σ, -, -, hconj⟩ :=
    exists_sigma_of_uchidaModuleData_and_perlis ϕ hϕ a hU hP hμ₁ hμ₂ hR
  exact ⟨σ, hconj⟩

end Main

end NK.UchidaKummer
