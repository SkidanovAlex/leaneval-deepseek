import Submission.NK.Reconstruct.denseChebotarev
import Submission.NK.Reconstruct.frobeniusCorrespondenceWithin_of_place_within
import Submission.NK.Reconstruct.PlaceCorrespondence

/-!
# The reconstruction of Neukirch–Uchida from the density form of Čebotarev

This file assembles the density-relaxed form of the reconstruction step.  The Čebotarev input (c)
and the Frobenius correspondence (b) of the area are relaxed from "at any prime" to "at the primes
of a set `R` of full Dirichlet density" — which is the form in which the density theorem is
available (`NK.Reconstruct.ChebotarevDensityInput`, proved from Artin reciprocity in
`Submission/Work/Reconstruct/denseChebotarev.lean`).

The main result is

`NK.Reconstruct.exists_sigma_of_localCorrespondence_dense`

* **(a)** the σ-free local correspondence `NK.Reconstruct.LocalCorrespondence ϕ` (CoNF (12.1.9));
* **(b)** the σ-free Frobenius correspondence `NK.Reconstruct.FrobeniusCorrespondencePlace ϕ hϕ a`;
* **(c)** the *density* form of Čebotarev, `NK.Reconstruct.ChebotarevDensityInput K₁ K₁'`, together
  with a set `R` of primes of full Dirichlet density;
* **(d)** the *restricted* realization: a field isomorphism `σ : K₂' ≃+* K₁'` mapping the embedded
  `K₂` onto the embedded `K₁`, whose level correspondence agrees with that of `ϕ`, and whose place
  map agrees with `a.placeMap` *at the places over the primes of `R` only*;

conclude `∃ σ, Conjugates σ ϕ`.

So the place identification is only needed on a set of primes of full density, and the Čebotarev
input only at such primes: this is exactly the shape of the classical construction (Neukirch,
CoNF XII §12.2; Uchida; Shimizu §4), where the identification of the place correspondence is made
outside a set of primes of density zero.
-/

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace NK.Reconstruct

open scoped Pointwise

variable {K₁ K₂ K₁' K₂' : Type*} [Field K₁] [Field K₂] [Field K₁'] [Field K₂']
  [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
  [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']

/-- **The reconstruction step from the density form of Čebotarev, with the place identification
only at a set of primes of full density.**

The hypotheses are the σ-free inputs (a) and (b) of the area, the density form (c) of Čebotarev
(proved from Artin reciprocity: `NK.Reconstruct.chebotarevDensityInput_of_artinReciprocity`), a set
`R` of primes of full Dirichlet density, and the restricted realization (d).

Every ingredient except (d) is either proved in this area or the density theorem; only the
*realization* of the place correspondence (up to a set of primes of density zero) is left as
input, exactly as in Neukirch's CoNF XII §12.2. -/
theorem exists_sigma_of_localCorrespondence_dense (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂))
    (hϕ : IsHomeomorph ϕ) (a : LocalCorrespondence ϕ)
    (b : FrobeniusCorrespondencePlace ϕ hϕ a) (hc : ChebotarevDensityInput K₁ K₁')
    {R : Set (NK.Chebotarev.PrimeIdeal K₁)} (hR : HasFullDensity K₁ R)
    (d : ∃ (σ : K₂' ≃+* K₁')
      (_hσ : Submission.NeukirchUchida.MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂') σ),
      AgreesOnLevels ϕ hϕ σ _hσ ∧
        (∀ A : FinitePlaceOf K₁ K₁',
          Submission.NeukirchUchida.primeOf A.1 A.2 ∈ R →
            (a.placeMap A).1.comap (σ.symm : K₁' →+* K₂') = A.1)) :
    ∃ σ : K₂' ≃+* K₁', Submission.NeukirchUchida.Conjugates σ ϕ := by
  obtain ⟨σ, hσ, hlvl, hreal⟩ := d
  exact exists_sigma_of_frobeniusCorrespondence_within_of_within ϕ σ hσ
    (frobeniusCorrespondenceWithin_of_place_within hϕ a σ hσ hlvl hreal b)
    (chebotarevInputWithin_of_hasFullDensity (K := K₁) (K' := K₁') hc hR)

end NK.Reconstruct
