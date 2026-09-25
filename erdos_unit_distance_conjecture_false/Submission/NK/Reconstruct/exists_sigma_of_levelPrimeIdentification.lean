import Submission.NK.Reconstruct.Reconstruction
import Submission.NK.Reconstruct.levelPrimeIdentification
import Submission.NK.ReconstructField.MainWeakNU
import Submission.NK.ReconstructField.LevelCandidate
import Submission.NeukirchUchida.Uniqueness
import Submission.NeukirchUchida.PlaceRigidity
import Submission.Commons.FieldTheory.Galois.eq_one_of_preserves_and_centralizes

/-!
# The σ-producing step of Neukirch–Uchida, with σ-free hypotheses

This module assembles the reconstruction of `σ` (CoNF XII §12.2) *inside* the `NK.Reconstruct`
area: it composes the level prime identification of `levelPrimeIdentification.lean`
(`NK.Reconstruct.levelPrimeIdentification`, the arithmetic/pinning step of Uchida–Shimizu) with
the compactness limit of `Submission/Work/ReconstructField/MainWeakNU.lean` and the Čebotarev
endgame `NK.Reconstruct.exists_sigma_of_frobeniusCorrespondence` of this area.

The result is the core theorem of the area in the form demanded by the deliverable: the hypotheses
mention

* **(a)** `NK.Reconstruct.LocalCorrespondence ϕ` — the σ-free good local correspondence of
  CoNF (12.1.9) (the place bijection with the Galois equivariance, the compatibility with the
  decomposition groups, and the preservation of the residue characteristic and of the local
  degree);
* the *base-level* form of Neukirch's Lemma 5.2: a base-field isomorphism `τ₀ : K₁ ≃+* K₂` whose
  induced prime map is the prime correspondence `a.primeMap` of `a`;
* **(W)** `NK.ReconstructField.LevelIsoInput ϕ hϕ` — the level-wise weak Neukirch–Uchida theorem
  (Uchida, nu2d §6): every finite level `L ⊆ K₁'` is isomorphic to its image `levelMap ϕ L`.  This
  is *strictly weaker* than the conclusion (`Submission/Work/ReconstructField/Targets.lean`);
* the Kummer input `ℓ` prime, `μ_ℓ ⊆ K₁` of the differentiation lemma;
* **(c)** `NK.Reconstruct.ChebotarevInput K₁ K₁'` — the Čebotarev density theorem.

The Frobenius correspondence **(b)** is *not* assumed: it is a consequence of the level prime
identification (a field isomorphism of levels transports Frobenius elements), so this theorem has
strictly weaker hypotheses than `NK.Reconstruct.exists_sigma_of_localCorrespondence`.

No homeomorphism hypothesis on `ϕ` is needed for the existence statement.
-/

namespace NK.Reconstruct

set_option linter.unusedVariables false

open scoped Pointwise

variable {K₁ K₂ K₁' K₂' : Type*} [Field K₁] [Field K₂] [Field K₁'] [Field K₂']
  [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
  [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']

/-- **The reconstruction from the level prime identification and Čebotarev.**

Given the σ-free local correspondence `a`, a base-field isomorphism `τ₀` inducing its prime map, the
level prime identification `LevelPrimeIdentification ϕ hϕ a τ₀` (Neukirch's Lemma *`alpha
identifies with sigma on primes`*) and the Čebotarev input, there is a field isomorphism
`σ : K₂' ≃+* K₁'` with `Conjugates σ ϕ`.

The proof is the compactness limit producing `σ` together with the σ-based Frobenius correspondence
(`NK.ReconstructField.exists_sigma_of_placeMap_and_frobenius_of_levelPrimeIdentification`), which
the Čebotarev endgame of this area converts into the conjugacy
(`NK.Reconstruct.exists_sigma_of_frobeniusCorrespondence`). -/
theorem exists_sigma_of_levelPrimeIdentification (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂))
    (hϕ : IsHomeomorph ϕ) (a : LocalCorrespondence ϕ) (τ₀ : K₁ ≃+* K₂)
    (hident : NK.ReconstructField.LevelPrimeIdentification ϕ hϕ a τ₀)
    (hc : ChebotarevInput K₁ K₁') :
    ∃ σ : K₂' ≃+* K₁', Submission.NeukirchUchida.Conjugates σ ϕ := by
  obtain ⟨σ, hσ, hfrob⟩ :=
    NK.ReconstructField.exists_sigma_of_placeMap_and_frobenius_of_levelPrimeIdentification
      ϕ hϕ a τ₀ hident
  exact exists_sigma_of_frobeniusCorrespondence ϕ σ hσ hfrob hc

/-- **The core theorem of the area with σ-free hypotheses (the σ-producing step of CoNF §12.2).**

From

* **(a)** the local correspondence `NK.Reconstruct.LocalCorrespondence ϕ`,
* a base-field isomorphism `τ₀ : K₁ ≃+* K₂` inducing the prime correspondence of `a`
  (`hbase`; the base-level form of Neukirch's Lemma 5.2, *strictly weaker* than the conclusion),
* **(W)** the level-wise weak Neukirch–Uchida input `NK.ReconstructField.LevelIsoInput ϕ hϕ`
  (Uchida's weak theorem, derived from `NK.UchidaKummer.IsWeakUchida` by
  `NK.ReconstructField.levelIsoInput_of_isWeakUchida`),
* the Kummer input `ℓ.Prime`, `∃ ζ : K₁, IsPrimitiveRoot ζ ℓ`, and
* **(c)** the Čebotarev density input `NK.Reconstruct.ChebotarevInput K₁ K₁'`

there is `σ : K₂' ≃+* K₁'` with `Conjugates σ ϕ`.

This eliminates hypothesis `(d)` of `NK.Reconstruct.exists_sigma_of_localCorrespondence_sigmaFree`
— which was *equivalent* to the conclusion
(`NK.Reconstruct.exists_conjugates_iff_exists_realizesPlaceMap`) and therefore could not be
counted as an input — and it does not assume the Frobenius correspondence (b): the prime
identification of levels transports Frobenius elements, so (b) is a *theorem* on this route. -/
theorem exists_sigma_of_localCorrespondence_of_levelIso (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂))
    (hϕ : IsHomeomorph ϕ) (a : LocalCorrespondence ϕ) (τ₀ : K₁ ≃+* K₂)
    (hbase : ∀ 𝔭 : NK.Chebotarev.PrimeIdeal K₁,
      a.primeMap 𝔭 = primeTransport τ₀ 𝔭)
    (hlev : NK.ReconstructField.LevelIsoInput ϕ hϕ) {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hμ : ∃ ζ : K₁, IsPrimitiveRoot ζ ℓ)
    (hc : ChebotarevInput K₁ K₁') :
    ∃ σ : K₂' ≃+* K₁', Submission.NeukirchUchida.Conjugates σ ϕ :=
  exists_sigma_of_levelPrimeIdentification ϕ hϕ a τ₀
    (levelPrimeIdentification ϕ hϕ a τ₀ hbase hlev hℓ hμ) hc

/-- **The core theorem of the area, with the weak Neukirch–Uchida theorem as a single input.**

Same statement as `NK.Reconstruct.exists_sigma_of_localCorrespondence_of_levelIso`, with the
level-wise input `LevelIsoInput` replaced by Uchida's weak Neukirch–Uchida theorem
`NK.UchidaKummer.IsWeakUchida ℓ` (two number fields with isomorphic absolute Galois groups are
isomorphic), which is a *theorem about number fields*, not about the pair `(K₁', K₂')` under
consideration.

The statement is given for fields in `Type` because `NK.UchidaKummer.IsWeakUchida` is stated
there (`NK.ReconstructField.levelIsoInput_of_isWeakUchida`), which is the case in which the
challenge target is stated. -/
theorem exists_sigma_of_localCorrespondence_of_weakUchida {k₁ k₂ k₁' k₂' : Type}
    [Field k₁] [Field k₂] [Field k₁'] [Field k₂'] [NumberField k₁] [NumberField k₂]
    [Algebra k₁ k₁'] [Algebra k₂ k₂'] [IsSepClosure k₁ k₁'] [IsSepClosure k₂ k₂']
    (ϕ : Gal(k₁'/k₁) ≃* Gal(k₂'/k₂)) (hϕ : IsHomeomorph ϕ)
    (a : LocalCorrespondence ϕ) (τ₀ : k₁ ≃+* k₂)
    (hbase : ∀ 𝔭 : NK.Chebotarev.PrimeIdeal k₁, a.primeMap 𝔭 = primeTransport τ₀ 𝔭)
    {ℓ : ℕ} (hW : NK.UchidaKummer.IsWeakUchida ℓ) (hℓ : ℓ.Prime)
    (hμ : ∃ ζ : k₁, IsPrimitiveRoot ζ ℓ) (hc : ChebotarevInput k₁ k₁') :
    ∃ σ : k₂' ≃+* k₁', Submission.NeukirchUchida.Conjugates σ ϕ :=
  exists_sigma_of_localCorrespondence_of_levelIso ϕ hϕ a τ₀ hbase
    (NK.ReconstructField.levelIsoInput_of_isWeakUchida hW ϕ hϕ) hℓ hμ hc

/-- **Triviality of the centralizer of `Gal(K'/K)` inside `Aut(K')`** (CoNF (12.1.6) in the form
used for uniqueness): the input of `Submission.NeukirchUchida.unique_sigma_of_centralizer_trivial`,
obtained from the ambient `Commons.FieldTheory.Galois.eq_one_of_preserves_and_centralizes` and the
*proved* triviality of the centre of an absolute Galois group of a number field
(`Submission.NeukirchUchida.center_trivial_of_sepClosure`, CoNF (12.1.6)).

This is a one-line instantiation of the uniqueness machinery of
`Submission/NeukirchUchida/Uniqueness.lean` (whose mathematics is proved in the commons); it is
included so that the `∃!` statement below can be exported from this area *without* importing
`Submission/NeukirchUchida/Core.lean` and hence without depending on the one remaining `sorry` of
the workspace. -/
theorem centralizer_trivial_of_sepClosure {K : Type*} [Field K] [NumberField K] {K' : Type*}
    [Field K'] [Algebra K K'] [IsSepClosure K K'] (c : K' ≃+* K')
    (hpres : ∀ x ∈ (algebraMap K K').range, c x ∈ (algebraMap K K').range)
    (hcomm : ∀ g : Gal(K'/K), c.trans (g.toRingEquiv.trans c.symm) = g.toRingEquiv) :
    c = 1 :=
  Commons.FieldTheory.Galois.eq_one_of_preserves_and_centralizes
    (fun (F : Type) [Field F] [NumberField F] (F' : Type) [Field F'] [Algebra F F']
        [IsSepClosure F F'] (c' : Gal(F'/F)) (h' : ∀ g : Gal(F'/F), c' * g = g * c') =>
      Submission.NeukirchUchida.center_trivial_of_sepClosure c' h')
    c hpres hcomm

/-- **The existence half of Neukirch–Uchida from the σ-free inputs, in the form `∃!`.**

Combining `NK.Reconstruct.exists_sigma_of_localCorrespondence_of_levelIso` with the *proved*
uniqueness half of the theorem (`Submission.NeukirchUchida.unique_sigma`, which rests on
`centralizer_trivial`, i.e. on the triviality of the centre of an absolute Galois group of a number
field, CoNF (12.1.6)) gives unique existence. -/
theorem existsUnique_sigma_of_localCorrespondence_of_levelIso
    (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (hϕ : IsHomeomorph ϕ) (a : LocalCorrespondence ϕ)
    (τ₀ : K₁ ≃+* K₂)
    (hbase : ∀ 𝔭 : NK.Chebotarev.PrimeIdeal K₁, a.primeMap 𝔭 = primeTransport τ₀ 𝔭)
    (hlev : NK.ReconstructField.LevelIsoInput ϕ hϕ) {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hμ : ∃ ζ : K₁, IsPrimitiveRoot ζ ℓ) (hc : ChebotarevInput K₁ K₁') :
    ∃! σ : K₂' ≃+* K₁', Submission.NeukirchUchida.Conjugates σ ϕ := by
  obtain ⟨σ, hσ⟩ :=
    exists_sigma_of_localCorrespondence_of_levelIso ϕ hϕ a τ₀ hbase hlev hℓ hμ hc
  exact ⟨σ, hσ, fun y hy =>
    Submission.NeukirchUchida.unique_sigma_of_centralizer_trivial
      (fun c hpres hcomm => centralizer_trivial_of_sepClosure c hpres hcomm) ϕ hy hσ⟩

end NK.Reconstruct
