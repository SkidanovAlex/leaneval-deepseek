import Submission.NK.ReconstructField.LevelCandidate
import Submission.NK.ReconstructField.LevelMatch
import Submission.NK.ReconstructField.exists_level_galois_image
import Submission.NK.ReconstructField.exists_sigma_levelMatch_of_levelPrimeIdentification
import Submission.NK.ReconstructField.compactness_conjHomEquiv
import Submission.NK.ReconstructField.Weak
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The reconstruction of `σ` from the weak Neukirch–Uchida theorem

This file assembles the reconstruction of CoNF XII §12.2 from

* **(A)** the place correspondence `a : NK.Reconstruct.LocalCorrespondence ϕ` of CoNF (12.1.9),
* **(W)** the *level-wise weak Neukirch–Uchida input* `NK.ReconstructField.LevelIsoInput` (for
  every finite level `L ⊆ K₁'` the levels `L` and `levelMap ϕ L` are isomorphic) — a consequence of
  Uchida's weak theorem `NK.UchidaKummer.IsWeakUchida`, and
* **(I)** the *level-wise prime identification* `NK.ReconstructField.LevelPrimeIdentification`
  (Neukirch's Lemma *`alpha identifies with sigma on primes`*): for every finite Galois level `L`
  whose image under `ϕ` is Galois over `ℚ`, there is an isomorphism `τ : L ≃+* levelMap ϕ L` of
  levels whose induced map on primes is the correspondence `a` and which is compatible with a fixed
  base-field isomorphism `τ₀ : K₁ ≃+* K₂`.

The proof is the compactness argument of §12.2: for every finite Galois level `L`, the matching
condition `NK.ReconstructField.LevelMatch ϕ hϕ σ hσ L` is satisfiable by a base-field-mapping
isomorphism `σ` of the separable closures; the sets of such `σ` (written as twists of a fixed lift
of `τ₀`) are closed in the compact group `Gal(K₂'/K₂)` and have the finite intersection property, so
a single `σ` satisfies them for all `L`, i.e. `conjHomEquiv hσ = ϕ`, i.e.
`Submission.NeukirchUchida.Conjugates σ ϕ`.
-/

set_option linter.unusedVariables false

namespace NK.ReconstructField

open NK.Reconstruct
open scoped Pointwise

variable {K₁ K₂ K₁' K₂' : Type*} [Field K₁] [Field K₂] [Field K₁'] [Field K₂']
  [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
  [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']

/-- **The level-wise prime identification (Neukirch's Lemma `alpha identifies with sigma on
primes`), σ-free form.**

For every finite Galois level `L ⊆ K₁'` whose image `levelMap ϕ L` is Galois over `ℚ`, there is an
isomorphism `τ : ↥L ≃+* ↥(levelMap ϕ L)` of the two levels which

* induces the prime correspondence `a` of CoNF (12.1.9) on primes
  (`NK.Reconstruct.primeTransport τ = NK.ReconstructField.levelPrimeMap ϕ hϕ a L`), and
* is compatible with the fixed base-field isomorphism `τ₀ : K₁ ≃+* K₂`.

The input mentions **no** global isomorphism of the separable closures and no realization of the
place correspondence: it is a family of isomorphisms of finite levels only. -/
def LevelPrimeIdentification (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (hϕ : IsHomeomorph ϕ)
    (a : NK.Reconstruct.LocalCorrespondence ϕ) (τ₀ : K₁ ≃+* K₂) : Prop :=
  ∀ (L : IntermediateField K₁ K₁') [FiniteDimensional K₁ L] [Normal K₁ L] [NumberField ↥L]
    [FiniteDimensional K₂ (NK.Reconstruct.levelMap ϕ L)]
    [Normal K₂ (NK.Reconstruct.levelMap ϕ L)] [NumberField ↥(NK.Reconstruct.levelMap ϕ L)]
    [IsGalois ℚ ↥(NK.Reconstruct.levelMap ϕ L)],
    ∃ τ : ↥L ≃+* ↥(NK.Reconstruct.levelMap ϕ L),
      NK.Reconstruct.primeTransport τ = NK.ReconstructField.levelPrimeMap ϕ hϕ a L ∧
        (∀ x : K₁, τ (algebraMap K₁ ↥L x) =
          algebraMap K₂ ↥(NK.Reconstruct.levelMap ϕ L) (τ₀ x))

/-- The matching condition is monotone in the level. -/
theorem levelMatch_of_le {ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)} {hϕ : IsHomeomorph ϕ} {σ : K₂' ≃+* K₁'}
    {hσ : Submission.NeukirchUchida.MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂') σ}
    {L L' : IntermediateField K₁ K₁'} [FiniteDimensional K₁ L] [Normal K₁ L] [NumberField ↥L]
    [FiniteDimensional K₂ (NK.Reconstruct.levelMap ϕ L)]
    [Normal K₂ (NK.Reconstruct.levelMap ϕ L)] [NumberField ↥(NK.Reconstruct.levelMap ϕ L)]
    [FiniteDimensional K₁ L'] [Normal K₁ L'] [NumberField ↥L']
    [FiniteDimensional K₂ (NK.Reconstruct.levelMap ϕ L')]
    [Normal K₂ (NK.Reconstruct.levelMap ϕ L')] [NumberField ↥(NK.Reconstruct.levelMap ϕ L')]
    (h : L ≤ L') (hm : LevelMatch ϕ hϕ σ hσ L') : LevelMatch ϕ hϕ σ hσ L :=
  fun g => IntermediateField.fixingSubgroup_antitone (levelMap_mono ϕ h) (hm g)

/-- **The reconstruction of `σ` from the level-wise inputs.**

Given the place correspondence `(A)`, a base-field isomorphism `τ₀ : K₁ ≃+* K₂` and the level-wise
prime identification `(I)`, there is a base-field-mapping isomorphism `σ : K₂' ≃+* K₁'` inducing
`ϕ`, and the σ-based Frobenius correspondence of Shimizu's Lemma 2.1.5 follows. -/
theorem exists_sigma_of_placeMap_and_frobenius_of_levelPrimeIdentification
    (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (hϕ : IsHomeomorph ϕ)
    (a : NK.Reconstruct.LocalCorrespondence ϕ) (τ₀ : K₁ ≃+* K₂)
    (hident : LevelPrimeIdentification ϕ hϕ a τ₀) :
    ∃ σ : K₂' ≃+* K₁',
      Submission.NeukirchUchida.MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂') σ ∧
        NK.Reconstruct.FrobeniusCorrespondence ϕ σ := by
  -- every finite Galois level admits a matching isomorphism
  have hL : ∀ (L : IntermediateField K₁ K₁') [FiniteDimensional K₁ L] [Normal K₁ L]
      [NumberField ↥L] [FiniteDimensional K₂ (NK.Reconstruct.levelMap ϕ L)]
      [Normal K₂ (NK.Reconstruct.levelMap ϕ L)] [NumberField ↥(NK.Reconstruct.levelMap ϕ L)],
      ∃ (σ : K₂' ≃+* K₁')
        (hσ : Submission.NeukirchUchida.MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂') σ),
        (∀ x : K₁, σ (algebraMap K₂ K₂' (τ₀ x)) = algebraMap K₁ K₁' x) ∧
          NK.ReconstructField.LevelMatch ϕ hϕ σ hσ L := by
    intro L _ _ _ _ _ _
    obtain ⟨L', hfd, hnf, hnf2, hle, hgal⟩ := exists_level_galois_image ϕ hϕ L
    haveI := hfd
    haveI := hnf
    haveI := hnf2
    haveI : FiniteDimensional K₂ (NK.Reconstruct.levelMap ϕ L') :=
      NK.Reconstruct.finiteDimensional_levelMap hϕ L'
    haveI : Normal K₂ (NK.Reconstruct.levelMap ϕ L') :=
      NK.Reconstruct.normal_levelMap hϕ L'
    haveI : NumberField ↥(NK.Reconstruct.levelMap ϕ L') :=
      NK.Reconstruct.numberField_levelMap hϕ L'
    obtain ⟨σ, hσ, hbase, hmatch⟩ :=
      exists_sigma_levelMatch_of_levelPrimeIdentification ϕ hϕ a τ₀ hident L'
    exact ⟨σ, hσ, hbase, levelMatch_of_le hle hmatch⟩
  -- compactness
  obtain ⟨σ, hσ, hconj⟩ := compactness_conjHomEquiv ϕ hϕ τ₀ hL
  refine ⟨σ, hσ, frobeniusCorrespondence_of_conjugates ?_⟩
  refine ⟨hσ, fun g => ?_⟩
  rw [← hconj]
  exact (Submission.NeukirchUchida.conj_toRingEquiv hσ g).symm

end NK.ReconstructField
