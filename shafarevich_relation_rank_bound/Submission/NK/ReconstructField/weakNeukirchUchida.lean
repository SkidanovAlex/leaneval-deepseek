import Submission.NK.ReconstructField.MainFinal
import Submission.NK.ReconstructField.key_finite_prime_match
import Submission.NK.ReconstructField.exists_level_galois_image
import Submission.NK.ReconstructField.levelPrimeMap_liesOver
import Submission.NK.ReconstructField.localDegree_primeTransport
import Submission.NK.ReconstructField.primeTransport_eq_levelPrimeMap_imp_base

/-!
# The base-level reconstruction input `WeakNeukirchUchida` is a theorem

The theorem `NK.ReconstructField.exists_sigma_of_placeMap_and_frobenius_of_weakUchida` of
`MainFinal.lean` takes, besides `(A)` and the level-wise weak Neukirch–Uchida input, the
*base-level* prime compatibility `hbase : ∀ 𝔭, a.primeMap 𝔭 = primeTransport τ₀ 𝔭` of a base
isomorphism `τ₀ : K₁ ≃+* K₂` (the σ-free predicate `NK.ReconstructField.WeakNeukirchUchida a` of
`Targets.lean`).

This file derives that input from the others: a level isomorphism realising the level prime
correspondence (`exists_levelIso_primeTransport`, obtained from `(A)`, the level-wise weak theorem
and the differentiation lemma — the pinning `key_finite_prime_match` plus the finiteness of the set
of isomorphisms of a number field) induces a *base* isomorphism whose prime transport is
`a.primeMap` (`exists_primeTransport_eq_primeMap`; the argument uses the freeness at a completely
split prime to get the base alignment and then compares contractions).

Consequently the final theorem below needs **only** `(A)`, the weak Neukirch–Uchida theorem at
levels, `ℓ` prime and `μ_ℓ ⊆ K₁` — no base-level compatibility is assumed.
-/

set_option linter.unusedVariables false

namespace NK.ReconstructField

open NK.Reconstruct
open scoped Pointwise

variable {K₁ K₂ K₁' K₂' : Type*} [Field K₁] [Field K₂] [Field K₁'] [Field K₂']
  [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
  [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']

/-- A number field has finitely many isomorphisms to another number field. -/
private theorem finite_ringEquiv_of_numberField {L L₂ : Type*} [Field L] [NumberField L]
    [Field L₂] [NumberField L₂] [Algebra ℚ L] [Algebra ℚ L₂] [FiniteDimensional ℚ L] :
    Finite (L ≃+* L₂) := by
  refine Finite.of_injective
    (fun e : L ≃+* L₂ => (AlgEquiv.ofRingEquiv (f := e) (fun q =>
      RingHom.congr_fun (RingHom.ext_rat (f := (e : L →+* L₂).comp (algebraMap ℚ L))
        (g := algebraMap ℚ L₂)) q) : L →ₐ[ℚ] L₂)) ?_
  intro e f h
  ext x
  exact DFunLike.congr_fun h x

/-- **A level isomorphism realising the whole level prime correspondence.**

By the finiteness of the set of isomorphisms `↥L ≃+* ↥(levelMap ϕ L)`, the finitary pinning
`key_finite_prime_match` upgrades to a single isomorphism whose prime map is the entire
correspondence `levelPrimeMap ϕ hϕ a L`. -/
theorem exists_levelIso_primeTransport {ℓ : ℕ}
    (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (hϕ : IsHomeomorph ϕ)
    (a : NK.Reconstruct.LocalCorrespondence ϕ)
    (hlev : LevelIsoInput ϕ hϕ) (hℓ : ℓ.Prime) (hμ : ∃ ζ : K₁, IsPrimitiveRoot ζ ℓ)
    (L : IntermediateField K₁ K₁') [FiniteDimensional K₁ L] [Normal K₁ L] [NumberField ↥L]
    [FiniteDimensional K₂ (NK.Reconstruct.levelMap ϕ L)]
    [Normal K₂ (NK.Reconstruct.levelMap ϕ L)] [NumberField ↥(NK.Reconstruct.levelMap ϕ L)]
    [IsGalois ℚ ↥(NK.Reconstruct.levelMap ϕ L)] :
    ∃ τ : ↥L ≃+* ↥(NK.Reconstruct.levelMap ϕ L),
      NK.Reconstruct.primeTransport τ =
        NK.ReconstructField.levelPrimeMap ϕ hϕ a L := by
  classical
  haveI hfin : Finite (↥L ≃+* ↥(NK.Reconstruct.levelMap ϕ L)) :=
    finite_ringEquiv_of_numberField (L := ↥L) (L₂ := ↥(NK.Reconstruct.levelMap ϕ L))
  haveI : Fintype (↥L ≃+* ↥(NK.Reconstruct.levelMap ϕ L)) := Fintype.ofFinite _
  let S : Finset (NK.Chebotarev.PrimeIdeal ↥L) :=
    Finset.univ.biUnion (fun e : ↥L ≃+* ↥(NK.Reconstruct.levelMap ϕ L) =>
      if h : ∃ P, NK.Reconstruct.primeTransport e P ≠
          NK.ReconstructField.levelPrimeMap ϕ hϕ a L P then {h.choose} else ∅)
  obtain ⟨τ, hτ⟩ := key_finite_prime_match ϕ hϕ a hlev hℓ hμ L S
  have hτ' : NK.Reconstruct.primeTransport τ =
      NK.ReconstructField.levelPrimeMap ϕ hϕ a L := by
    funext P
    by_contra hP
    have hex : ∃ P, NK.Reconstruct.primeTransport τ P ≠
        NK.ReconstructField.levelPrimeMap ϕ hϕ a L P := ⟨P, hP⟩
    have hmem : hex.choose ∈ S := by
      refine Finset.mem_biUnion.mpr ⟨τ, Finset.mem_univ τ, ?_⟩
      rw [dif_pos hex]
      exact Finset.mem_singleton_self _
    exact hex.choose_spec (hτ hex.choose hmem)
  exact ⟨τ, hτ'⟩

set_option maxHeartbeats 1600000 in
/-- **The base-level compatibility is a theorem.**  A level isomorphism whose prime map is the level
prime correspondence induces a base-field isomorphism whose prime transport is `a.primeMap`. -/
theorem exists_primeTransport_eq_primeMap_of_levelIso {ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)}
    (hϕ : IsHomeomorph ϕ) (a : NK.Reconstruct.LocalCorrespondence ϕ)
    (L : IntermediateField K₁ K₁') [FiniteDimensional K₁ L] [Normal K₁ L] [NumberField ↥L]
    [FiniteDimensional K₂ (NK.Reconstruct.levelMap ϕ L)]
    [Normal K₂ (NK.Reconstruct.levelMap ϕ L)] [NumberField ↥(NK.Reconstruct.levelMap ϕ L)]
    [IsGalois ℚ ↥(NK.Reconstruct.levelMap ϕ L)]
    (τ : ↥L ≃+* ↥(NK.Reconstruct.levelMap ϕ L))
    (hτ : NK.Reconstruct.primeTransport τ =
      NK.ReconstructField.levelPrimeMap ϕ hϕ a L) :
    ∃ σ' : K₁ ≃+* K₂, ∀ P : NK.Chebotarev.PrimeIdeal K₁,
      NK.Reconstruct.primeTransport σ' P = a.primeMap P := by
  classical
  obtain ⟨p, hp⟩ := Commons.NumberTheory.NumberField.exists_prime_splitsCompletely
    (K := ℚ) (L := ↥(NK.Reconstruct.levelMap ϕ L))
  have hsplit : ∀ Q : NK.Chebotarev.PrimeIdeal ↥(NK.Reconstruct.levelMap ϕ L),
      Q.asIdeal.LiesOver p.asIdeal →
        Q.asIdeal.ramificationIdx (NumberField.RingOfIntegers ℚ) = 1 ∧
          Q.asIdeal.inertiaDeg (NumberField.RingOfIntegers ℚ) = 1 := by
    intro Q hQ
    have hl := (NK.UchidaKummer.API.splitsCompletely_iff_forall_localDeg_eq_one
      (K := ℚ) (L := ↥(NK.Reconstruct.levelMap ϕ L)) p).mp hp Q hQ
    rw [NK.UchidaKummer.localDeg] at hl
    exact mul_eq_one.mp hl
  have hML : NK.Reconstruct.MapsBaseLevel L (NK.Reconstruct.levelMap ϕ L) τ :=
    mapsBaseLevel_of_conjRingEquiv_eq ϕ hϕ L τ
      (conjRingEquiv_eq_levelMapEquiv_of_primeTransport_eq ϕ hϕ a L τ hτ p hsplit)
  refine ⟨NK.Reconstruct.PrimeTransportInv.transportBaseEquiv hML, fun P => ?_⟩
  have hσ'spec : ∀ x : K₁,
      τ (algebraMap K₁ ↥L x) = algebraMap K₂ ↥(NK.Reconstruct.levelMap ϕ L)
        (NK.Reconstruct.PrimeTransportInv.transportBaseEquiv hML x) :=
    fun x => NK.Reconstruct.PrimeTransportInv.transportBaseEquiv_spec hML x
  obtain ⟨P', hP'⟩ := NK.Chebotarev.exists_primeIdeal_liesOver (K := K₁) (L := ↥L) P
  apply IsDedekindDomain.HeightOneSpectrum.ext
  have h1 : (NK.Reconstruct.primeTransport
        (NK.Reconstruct.PrimeTransportInv.transportBaseEquiv hML) P).asIdeal =
      (NK.Reconstruct.primeTransport τ P').asIdeal.under (NumberField.RingOfIntegers K₂) := by
    have h := NK.ReconstructField.under_map_ringOfIntegersEquiv τ
      (NK.Reconstruct.PrimeTransportInv.transportBaseEquiv hML) hσ'spec P'.asIdeal
    rw [hP'.over.symm,
      ← NK.ReconstructField.primeTransport_asIdeal
        (NK.Reconstruct.PrimeTransportInv.transportBaseEquiv hML) P] at h
    rw [← h, ← NK.ReconstructField.primeTransport_asIdeal τ P']
  have h2 : (a.primeMap P).asIdeal =
      (NK.Reconstruct.primeTransport τ P').asIdeal.under (NumberField.RingOfIntegers K₂) := by
    have hlev : (NK.Reconstruct.primeTransport τ P').asIdeal =
        (NK.ReconstructField.levelPrimeMap ϕ hϕ a L P').asIdeal :=
      congrArg IsDedekindDomain.HeightOneSpectrum.asIdeal (congrFun hτ P')
    have hlies : (NK.ReconstructField.levelPrimeMap ϕ hϕ a L P').asIdeal.under
          (NumberField.RingOfIntegers K₂) = (a.primeMap P).asIdeal :=
      (NK.ReconstructField.levelPrimeMap_liesOver ϕ hϕ a L P P' hP').over.symm
    rw [hlev, hlies]
  rw [h1]
  exact h2.symm

/-- **The base-level compatibility `WeakNeukirchUchida a` is a theorem.**

From `(A)`, the level-wise weak Neukirch–Uchida theorem and the differentiation hypotheses there is
a base-field isomorphism `σ' : K₁ ≃+* K₂` whose induced prime correspondence is `a.primeMap`. -/
theorem exists_primeTransport_eq_primeMap {ℓ : ℕ}
    (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (hϕ : IsHomeomorph ϕ)
    (a : NK.Reconstruct.LocalCorrespondence ϕ)
    (hlev : LevelIsoInput ϕ hϕ) (hℓ : ℓ.Prime) (hμ : ∃ ζ : K₁, IsPrimitiveRoot ζ ℓ) :
    ∃ σ' : K₁ ≃+* K₂, ∀ P : NK.Chebotarev.PrimeIdeal K₁,
      NK.Reconstruct.primeTransport σ' P = a.primeMap P := by
  obtain ⟨L, hfd, hnf, hnf2, -, hgal⟩ :=
    exists_level_galois_image ϕ hϕ (⊥ : IntermediateField K₁ K₁')
  haveI := hfd
  haveI := hnf
  haveI := hnf2
  haveI : FiniteDimensional K₂ (NK.Reconstruct.levelMap ϕ L) :=
    NK.Reconstruct.finiteDimensional_levelMap hϕ L
  haveI : Normal K₂ (NK.Reconstruct.levelMap ϕ L) := NK.Reconstruct.normal_levelMap hϕ L
  haveI : NumberField ↥(NK.Reconstruct.levelMap ϕ L) :=
    NK.Reconstruct.numberField_levelMap hϕ L
  obtain ⟨τ, hτ⟩ := exists_levelIso_primeTransport ϕ hϕ a hlev hℓ hμ L
  exact exists_primeTransport_eq_primeMap_of_levelIso hϕ a L τ hτ

/-- **The reconstruction of `σ` (CoNF XII §12.2) — final form.**

The inputs are exactly: **(A)** the place correspondence `a : LocalCorrespondence ϕ` of
CoNF (12.1.9), **(W)** the level-wise weak Neukirch–Uchida theorem `LevelIsoInput ϕ hϕ` (Uchida's
theorem, nu2d §6, derived from `NK.UchidaKummer.IsWeakUchida` by
`NK.ReconstructField.levelIsoInput_of_isWeakUchida`), and the number-theoretic hypotheses
`ℓ` prime and `μ_ℓ ⊆ K₁` of the differentiation lemma.  No base-level compatibility is assumed and
the conclusion asserts no place realisation of `σ`: the output is a `MapsBase` isomorphism
`σ : K₂' ≃+* K₁'` with the Frobenius correspondence, and with
`NK.Mine.exists_sigma_of_frobeniusCorrespondence` it gives `Conjugates σ ϕ`. -/
theorem exists_sigma_of_placeMap_and_frobenius_of_levelIsoInput {ℓ : ℕ}
    (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (hϕ : IsHomeomorph ϕ)
    (a : NK.Reconstruct.LocalCorrespondence ϕ)
    (hlev : LevelIsoInput ϕ hϕ) (hℓ : ℓ.Prime) (hμ : ∃ ζ : K₁, IsPrimitiveRoot ζ ℓ) :
    ∃ σ : K₂' ≃+* K₁',
      Submission.NeukirchUchida.MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂') σ ∧
        NK.Reconstruct.FrobeniusCorrespondence ϕ σ := by
  obtain ⟨τ₀, hbase⟩ := exists_primeTransport_eq_primeMap ϕ hϕ a hlev hℓ hμ
  exact exists_sigma_of_placeMap_and_frobenius_of_weakUchida ϕ hϕ a τ₀
    (fun 𝔭 => (hbase 𝔭).symm) hlev hℓ hμ

end NK.ReconstructField
