import Submission.NK.Reconstruct.Assembly
import Submission.NK.Reconstruct.comap_placeMap_eq_of_conjugates
import Submission.NK.Reconstruct.exists_sigma_of_weak_and_placeRigidity

/-!
# The remaining input of the reconstruction (Neukirch's CoNF XII §12.2), and its variants

The reconstruction step of Neukirch–Uchida (CoNF XII §12.2; Shimizu, arXiv:2009.10431 §4) reduces
the whole existence half of the Neukirch–Uchida theorem to **one** statement, which does not mention
the field isomorphism that is to be produced, and which this file identifies exactly:

> **(d)** *the place correspondence is realized by a field isomorphism*: there is
> `σ : K₂' ≃+* K₁'` with `MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂') σ` such that
> `(a.placeMap A).1.comap σ.symm = A.1` for every place `A` of `K₁'` over a finite prime of `K₁`,
> where `a : LocalCorrespondence ϕ` is the σ-free good local correspondence (input (a)).

This file proves:

* `NK.Reconstruct.exists_conjugates_iff_exists_realizesPlaceMap` — **the remaining input (d) is
  *equivalent* to the conclusion**: given the σ-free inputs (a), (b) (the Frobenius
  correspondence) and (c) (Čebotarev),
  `(∃ σ, MapsBase σ ∧ σ realizes the place correspondence) ↔ (∃ σ, Conjugates σ ϕ)`.
  So *every* proof of the existence half must produce (d), and (d) *is* the whole gap.  The
  forward direction is the endgame `NK.Reconstruct.exists_sigma_of_localCorrespondence_sigmaFree`;
  the converse is the rigidity of the place correspondence
  `NK.Reconstruct.comap_placeMap_eq_of_conjugates`.
* `NK.Reconstruct.exists_realizesPlaceMap_of_placeRigidity` — the *PlaceRigidity* route
  (`NK.Reconstruct.exists_conjugates_of_placeRigidity`, i.e. the weak half `K₁ ≅ K₂` plus
  Jarden–Ritter rigidity of the place system) *produces* the remaining input (d), hence plugs into
  the endgame.
* `NK.Reconstruct.exists_sigma_of_localCorrespondence_sharp` — the theorem of the shape requested
  by the reconstruction deliverable: hypotheses (a), (b), (c) and the single input (d).

The two ways of *discharging* (d) currently available in the workspace are

1. `Submission/Work/ReconstructField/` (Shimizu's route: the base-field isomorphism from the rank
   computation `r_ℓ(K) = r_ℂ(K) + 1 + δ_ℓ(K) ≤ [K:ℚ]`, CoNF (10.3.20)) and
2. `Submission/Work/UchidaKummer/` (Uchida's Kummer-theoretic differentiation),
3. plus, for the *weak* half alone, `Submission/Work/ReconstructField/`'s Bauer-style argument: with
   the weak half `K₁ ≅ K₂` the rigidity of the place system
   (`NK.Reconstruct.PlaceRigidity`) gives (d) by way 2 above, namely
   `NK.Reconstruct.exists_realizesPlaceMap_of_placeRigidity`.
-/

set_option linter.unusedVariables false

namespace NK.Reconstruct

open scoped Pointwise

variable {K₁ K₂ K₁' K₂' : Type*} [Field K₁] [Field K₂] [Field K₁'] [Field K₂']
  [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
  [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']

/-- **The remaining input (d) of the reconstruction is equivalent to its conclusion.**

Fix the σ-free inputs of the reconstruction: the good local correspondence
`a : LocalCorrespondence ϕ` (input (a)), the σ-free Frobenius correspondence
`b : FrobeniusCorrespondencePlace ϕ hϕ a` (input (b)) and the Čebotarev input
`c : ChebotarevInput K₁ K₁'` (input (c)).  Then the following are equivalent:

* there is a `MapsBase` field isomorphism `σ : K₂' ≃+* K₁'` *realizing the place correspondence*
  (Neukirch's CoNF XII §12.2, this is the remaining input (d));
* `ϕ` is induced by a `MapsBase` field isomorphism (the conclusion of Neukirch–Uchida).

In particular no input *weaker* than (d) can complete the reconstruction from (a), (b), (c), and
any proof of the theorem must produce (d). -/
theorem exists_conjugates_iff_exists_realizesPlaceMap {ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)}
    (hϕ : IsHomeomorph ϕ) (a : LocalCorrespondence ϕ) (b : FrobeniusCorrespondencePlace ϕ hϕ a)
    (c : ChebotarevInput K₁ K₁') :
    (∃ (σ : K₂' ≃+* K₁')
      (_hσ : Submission.NeukirchUchida.MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂') σ),
      ∀ A : FinitePlaceOf K₁ K₁', (a.placeMap A).1.comap (σ.symm : K₁' →+* K₂') = A.1) ↔
      (∃ σ : K₂' ≃+* K₁', Submission.NeukirchUchida.Conjugates σ ϕ) := by
  constructor
  · rintro ⟨σ, hσ, hreal⟩
    exact exists_sigma_of_localCorrespondence_sigmaFree ϕ hϕ a b c ⟨σ, hσ, hreal⟩
  · rintro ⟨σ, hσ⟩
    exact ⟨σ, hσ.1, fun A => comap_placeMap_eq_of_conjugates a hσ A⟩

/-- **The reconstruction theorem in the shape of the deliverable.**  From the σ-free inputs
(a) (the good local correspondence), (b) (the σ-free Frobenius correspondence), (c) (the Čebotarev
input) and the single remaining input (d) (Neukirch's CoNF XII §12.2: the place correspondence is
realized by a `MapsBase` field isomorphism), `ϕ` is induced by a field isomorphism. -/
theorem exists_sigma_of_localCorrespondence_sharp {ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)}
    (hϕ : IsHomeomorph ϕ) (a : LocalCorrespondence ϕ) (b : FrobeniusCorrespondencePlace ϕ hϕ a)
    (c : ChebotarevInput K₁ K₁')
    (d : ∃ (σ : K₂' ≃+* K₁')
      (_hσ : Submission.NeukirchUchida.MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂') σ),
      ∀ A : FinitePlaceOf K₁ K₁', (a.placeMap A).1.comap (σ.symm : K₁' →+* K₂') = A.1) :
    ∃ σ : K₂' ≃+* K₁', Submission.NeukirchUchida.Conjugates σ ϕ :=
  (exists_conjugates_iff_exists_realizesPlaceMap hϕ a b c).mp d

/-- **The PlaceRigidity route produces the remaining input (d).**  Given the σ-free local
correspondence (a), *some* base-field-mapping isomorphism `σ₀` (the weak half `K₁ ≅ K₂` of the
Neukirch–Uchida theorem) and the rigidity of the place system
(`NK.Reconstruct.PlaceRigidity`, Jarden–Ritter), the place correspondence is realized by a
`MapsBase` field isomorphism — i.e. the endgame's input (d) is available. -/
theorem exists_realizesPlaceMap_of_placeRigidity {ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)}
    (a : LocalCorrespondence ϕ) {σ₀ : K₂' ≃+* K₁'}
    (hσ₀ : Submission.NeukirchUchida.MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂') σ₀)
    (hrig : PlaceRigidity K₂ K₂') :
    ∃ (σ : K₂' ≃+* K₁')
      (_hσ : Submission.NeukirchUchida.MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂') σ),
      ∀ A : FinitePlaceOf K₁ K₁', (a.placeMap A).1.comap (σ.symm : K₁' →+* K₂') = A.1 := by
  obtain ⟨σ, hσ⟩ := exists_conjugates_of_placeRigidity a hσ₀ hrig
  exact ⟨σ, hσ.1, fun A => comap_placeMap_eq_of_conjugates a hσ A⟩

/-- **The Neukirch–Uchida theorem in its `∃!` form, from the four named inputs and the (proved)
uniqueness half.**

`huniq` is the *uniqueness half* of CoNF XII Theorem 12.2.1, which is **proved** in the workspace as
`Submission.NeukirchUchida.unique_sigma` (from triviality of the centre of an absolute Galois group
of a number field, CoNF (12.1.6), `Submission.NeukirchUchida.centralizer_trivial`); it is taken as a
hypothesis here only to keep this module free of the import of
`Submission/NeukirchUchida/Core.lean`, whose single unproved step is exactly the existence half
proved here. -/
theorem existsUnique_sigma_of_localCorrespondence_sharp {ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)}
    (hϕ : IsHomeomorph ϕ) (a : LocalCorrespondence ϕ) (b : FrobeniusCorrespondencePlace ϕ hϕ a)
    (c : ChebotarevInput K₁ K₁')
    (d : ∃ (σ : K₂' ≃+* K₁')
      (_hσ : Submission.NeukirchUchida.MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂') σ),
      ∀ A : FinitePlaceOf K₁ K₁', (a.placeMap A).1.comap (σ.symm : K₁' →+* K₂') = A.1)
    (huniq : ∀ σ₁ σ₂ : K₂' ≃+* K₁',
      Submission.NeukirchUchida.Conjugates σ₁ ϕ → Submission.NeukirchUchida.Conjugates σ₂ ϕ →
        σ₁ = σ₂) :
    ∃! σ : K₂' ≃+* K₁', Submission.NeukirchUchida.Conjugates σ ϕ := by
  obtain ⟨σ, hσ⟩ := exists_sigma_of_localCorrespondence_sharp hϕ a b c d
  exact ⟨σ, hσ, fun y hy => huniq y σ hy hσ⟩

end NK.Reconstruct
