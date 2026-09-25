import Submission.NK.ReconstructField.Input
import Submission.NK.ReconstructField.GaloisCase
import Submission.NK.ReconstructField.primeTransport_eq_primeMap_of_realizesPlaceCorrespondence

/-!
# The two classical targets into which the remaining input splits

`NK.ReconstructField.ReconstructionInput` (the reconstruction input (C) of
`NK.ReconstructField.exists_sigma_of_placeMap_and_frobenius`) is, by
`NK.ReconstructField.primeTransport_eq_primeMap_of_realizesPlaceCorrespondence`, the conjunction of
exactly two classical statements about the number fields, the primes, and the place system:

* **(i) the weak Neukirch–Uchida theorem** — there is a base-field isomorphism `τ : K₁ ≃+* K₂` whose
  induced map on primes is the prime correspondence `a.primeMap` of `ϕ`
  (`NK.ReconstructField.WeakNeukirchUchida`);
* **(ii) the place-system rigidity** — *some* Galois twist of the (provably existing) lift of `τ`
  realizes the place map of `ϕ` (`NK.ReconstructField.PlaceRealization`).

Both are stated **without asserting the existence of a field isomorphism of the separable
closures**: (i) is a statement about the finite fields `K₁`, `K₂` alone, and (ii) quantifies over an
element of `Gal(K₂'/K₂)` applied to a *constructed* lift.

In the Galois-over-`ℚ` case, **(i) is a theorem of this chapter** (`galoisBaseIso`), so only (ii)
remains there. -/

set_option linter.unusedVariables false

namespace NK.ReconstructField

variable {K₁ K₂ K₁' K₂' : Type*} [Field K₁] [Field K₂] [Field K₁'] [Field K₂']
  [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
  [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']

/-- **(i) The weak Neukirch–Uchida theorem in the form used by the reconstruction**: a base-field
isomorphism `τ : K₁ ≃+* K₂` inducing the prime correspondence of `ϕ`. -/
def WeakNeukirchUchida {ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)}
    (a : NK.Reconstruct.LocalCorrespondence ϕ) : Prop :=
  ∃ τ : K₁ ≃+* K₂, ∀ 𝔭 : NK.Chebotarev.PrimeIdeal K₁,
    NK.Reconstruct.primeTransport τ 𝔭 = a.primeMap 𝔭

/-- **(ii) The place-system rigidity**: some Galois twist of the lift of `τ` realizes the place
correspondence of `ϕ`.  (The lift itself is *constructed* by
`NK.ReconstructField.liftTwist`; the assertion is only about the Galois element.) -/
def PlaceRealization {ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)}
    (a : NK.Reconstruct.LocalCorrespondence ϕ) (τ : K₁ ≃+* K₂) : Prop :=
  ∃ h : Gal(K₂'/K₂), RealizesPlaceCorrespondence a (liftTwist K₁ K₂ K₁' K₂' τ h)

/-- The two targets together are exactly the reconstruction input. -/
theorem reconstructionInput_iff_weakNeukirchUchida_and_placeRealization
    {ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)} {hϕ : IsHomeomorph ϕ}
    {a : NK.Reconstruct.LocalCorrespondence ϕ} :
    ReconstructionInput hϕ a ↔
      ∃ τ : K₁ ≃+* K₂, WeakNeukirchUchida a ∧ PlaceRealization a τ := by
  constructor
  · rintro ⟨τ, h, hreal⟩
    refine ⟨τ, ⟨τ, fun 𝔭 => ?_⟩, h, hreal⟩
    -- the prime compatibility is automatic from the realization
    exact primeTransport_eq_primeMap_of_realizesPlaceCorrespondence a
      (liftTwist K₁ K₂ K₁' K₂' τ h) (liftTwist_apply_base K₁ K₂ K₁' K₂' τ h) hreal 𝔭
  · rintro ⟨τ, _, h, hreal⟩
    exact ⟨τ, h, hreal⟩

/-- **The reconstruction, with the two targets as separate hypotheses** (the form in which the
remaining work is stated). -/
theorem exists_sigma_of_placeMap_and_frobenius_of_targets
    (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (he : IsHomeomorph ϕ)
    (a : NK.Reconstruct.LocalCorrespondence ϕ)
    (b : NK.Reconstruct.FrobeniusCorrespondencePlace ϕ he a)
    (τ : K₁ ≃+* K₂) (hii : PlaceRealization a τ) :
    ∃ σ : K₂' ≃+* K₁',
      Submission.NeukirchUchida.MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂') σ ∧
        NK.Reconstruct.FrobeniusCorrespondence ϕ σ :=
  exists_sigma_of_placeMap_and_frobenius ϕ he a b ⟨τ, hii⟩

/-- **In the Galois case, the weak Neukirch–Uchida statement (i) follows from the place realization
(ii).**  With `τ := galoisBaseIso a` (constructed by Bauer from the local correspondence alone), a
realization of the place map by some Galois twist of the lift of `τ` forces the prime compatibility
of `τ`, i.e. a witness of `NK.ReconstructField.WeakNeukirchUchida a`. -/
theorem weakNeukirchUchida_galois {ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)}
    (a : NK.Reconstruct.LocalCorrespondence ϕ) [IsGalois ℚ K₁] [IsGalois ℚ K₂]
    (hreal : ∃ h : Gal(K₂'/K₂),
      RealizesPlaceCorrespondence a (liftTwist K₁ K₂ K₁' K₂' (galoisBaseIso a) h)) :
    WeakNeukirchUchida a := by
  obtain ⟨h, hreal⟩ := hreal
  exact ⟨galoisBaseIso a, fun 𝔭 =>
    primeTransport_eq_primeMap_of_realizesPlaceCorrespondence a
      (liftTwist K₁ K₂ K₁' K₂' (galoisBaseIso a) h)
      (liftTwist_apply_base K₁ K₂ K₁' K₂' (galoisBaseIso a) h) hreal 𝔭⟩

end NK.ReconstructField
