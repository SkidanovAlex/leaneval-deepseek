import Submission.NK.ReconstructField.MainWeakNU
import Submission.NK.ReconstructField.levelPrimeIdentification

/-!
# The reconstruction of `σ` from (A), the weak Neukirch–Uchida theorem and the differentiation

This file composes the two halves of the §12.2 route built in this chapter:

* `NK.ReconstructField.levelPrimeIdentification` — the *arithmetic/pinning* step (Neukirch's
  Lemma `alpha identifies with sigma on primes`): the level-wise prime identification follows from
  the local correspondence `(A)`, the base-level prime compatibility of a fixed base isomorphism
  `τ₀`, the level-wise weak Neukirch–Uchida theorem and the differentiation lemma (for `ℓ` prime and
  `μ_ℓ ⊆ K₁`);
* `NK.ReconstructField.exists_sigma_of_placeMap_and_frobenius_of_levelPrimeIdentification` — the
  *outer shell* (freeness, extension to the separable closures, compactness limit) producing
  `σ : K₂' ≃+* K₁'` with `MapsBase` and the Frobenius correspondence.

The result below is therefore the reconstruction of CoNF XII §12.2 with σ-free, explicitly listed
inputs: the place correspondence, the base-level prime compatibility of `τ₀` (the base-level form of
Neukirch's Lemma 5.2, strictly weaker than the conclusion: `Targets.lean` proves
`ReconstructionInput ⟺ WeakNeukirchUchida ∧ PlaceRealization`), the weak Neukirch–Uchida theorem at
levels (Uchida's theorem, nu2d §6) and the number theory `ℓ` prime, `μ_ℓ ⊆ K₁`.
-/

set_option linter.unusedVariables false

namespace NK.ReconstructField

open NK.Reconstruct
open scoped Pointwise

variable {K₁ K₂ K₁' K₂' : Type*} [Field K₁] [Field K₂] [Field K₁'] [Field K₂']
  [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
  [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']

/-- **The reconstruction of `σ` (CoNF XII §12.2) from the σ-free inputs.**

Given

* **(A)** the place correspondence `a : NK.Reconstruct.LocalCorrespondence ϕ` of CoNF (12.1.9),
* the base-level prime compatibility `a.primeMap = primeTransport τ₀` of a base isomorphism
  `τ₀ : K₁ ≃+* K₂` (the base-level form of Neukirch's Lemma 5.2),
* **(W)** the level-wise weak Neukirch–Uchida input `NK.ReconstructField.LevelIsoInput` (Uchida's
  theorem, nu2d §6), and
* the number-theoretic input `ℓ` prime, `μ_ℓ ⊆ K₁` (for the differentiation lemma),

there is a base-field-mapping isomorphism `σ : K₂' ≃+* K₁'` inducing `ϕ`, and the σ-based Frobenius
correspondence of Shimizu's Lemma 2.1.5 holds.  With
`NK.Mine.exists_sigma_of_frobeniusCorrespondence` this gives
`Submission.NeukirchUchida.Conjugates σ ϕ`. -/
theorem exists_sigma_of_placeMap_and_frobenius_of_weakUchida {ℓ : ℕ}
    (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (hϕ : IsHomeomorph ϕ)
    (a : NK.Reconstruct.LocalCorrespondence ϕ) (τ₀ : K₁ ≃+* K₂)
    (hbase : ∀ 𝔭 : NK.Chebotarev.PrimeIdeal K₁,
      a.primeMap 𝔭 = NK.Reconstruct.primeTransport τ₀ 𝔭)
    (hlev : LevelIsoInput ϕ hϕ) (hℓ : ℓ.Prime)
    (hμ : ∃ ζ : K₁, IsPrimitiveRoot ζ ℓ) :
    ∃ σ : K₂' ≃+* K₁',
      Submission.NeukirchUchida.MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂') σ ∧
        NK.Reconstruct.FrobeniusCorrespondence ϕ σ :=
  exists_sigma_of_placeMap_and_frobenius_of_levelPrimeIdentification ϕ hϕ a τ₀
    (levelPrimeIdentification ϕ hϕ a τ₀ hbase hlev hℓ hμ)

end NK.ReconstructField
