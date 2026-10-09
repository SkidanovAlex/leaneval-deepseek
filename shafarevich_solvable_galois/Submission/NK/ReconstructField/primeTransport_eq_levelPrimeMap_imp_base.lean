import Mathlib
import Submission.NK.ReconstructField.conjRingEquiv_eq_levelMapEquiv_of_primeTransport_eq
import Submission.NK.ReconstructField.mapsBaseLevel_of_conjRingEquiv_eq
import Submission.NK.ReconstructField.localDegree_primeTransport
import Submission.NK.ReconstructField.levelPrimeMap_liesOver
import Submission.NK.Chebotarev.Basic
import Submission.NK.UchidaKummer.SplitPrimes
import Submission.NK.UchidaKummer.API.splitsCompletely_iff_forall_localDeg_eq_one
import Submission.Commons.NumberTheory.NumberField.exists_prime_splitsCompletely
import Submission.Commons.NumberTheory.NumberField.numberField_of_intermediateField
import Submission.Commons.NumberTheory.NumberField.exists_heightOneSpectrum_liesOver
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The base-field compatibility of a level isomorphism inducing the prime correspondence

Let `ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)` be a homeomorphic isomorphism of absolute Galois groups of
number fields, `a` a local correspondence of CoNF (12.1.9) for `ϕ`, `τ₀ : K₁ ≃+* K₂` a base-field
isomorphism whose transport of primes reproduces the prime correspondence of `a`, and let
`L ⊆ K₁'` be a finite normal level with corresponding level `M = levelMap ϕ L ⊆ K₂'`.  If a level
isomorphism `τ : ↥L ≃+* ↥M` transports primes exactly as the finite-level prime correspondence of
`ϕ` (`primeTransport τ = levelPrimeMap ϕ hϕ a L`), then:

* `τ` is compatible with the base fields (`NK.Reconstruct.MapsBaseLevel L M τ`), and
* `τ` restricts to `τ₀` on the embedded copy of `K₁`.

The proof has two halves.

* The *Galois half*: since `↥M` is Galois over `ℚ`, there is a rational prime `p` splitting
  completely in `M`; at such a prime the Galois action is free, and comparing
  `primeTransport τ` with the Galois-equivariant correspondence `levelPrimeMap` shows that
  conjugating `Gal(↥L/K₁)` by `τ` reproduces `levelMapEquiv hϕ L`.  Artin's theorem then gives
  `MapsBaseLevel L M τ` (`mapsBaseLevel_of_conjRingEquiv_eq`, fed by
  `conjRingEquiv_eq_levelMapEquiv_of_primeTransport_eq`).

* The *arithmetic half*: the induced base-field isomorphism `σ' : K₁ ≃+* K₂` of `MapsBaseLevel`
  and `τ₀` induce the same map on primes — both are computed as the prime of `K₂` below
  `primeTransport τ P` for a prime `P` of `𝓞 L` above a given prime of `K₁`, using that the prime
  correspondence of `a` on `K₁` is the transport along `τ₀`.  Since an isomorphism of number
  fields is determined by its action on primes (`eq_one_of_primeTransport_eq_self_aux`), `σ' = τ₀`.
-/

set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000

namespace NK.ReconstructField

open NK.Reconstruct
open scoped Pointwise

section Aux

variable {K₁ K₂ K₁' K₂' : Type*} [Field K₁] [Field K₂] [Field K₁'] [Field K₂']
  [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']

/-- **The ring homomorphism `K₁ →+* K₂` induced by a base-level-compatible level isomorphism.** -/
private noncomputable def baseHomAux {L₁ : IntermediateField K₁ K₁'} {L₂ : IntermediateField K₂ K₂'}
    {τ : ↥L₁ ≃+* ↥L₂} (h : NK.Reconstruct.MapsBaseLevel L₁ L₂ τ) : K₁ →+* K₂ where
  toFun a := Classical.choose (h.1 a)
  map_one' := by
    refine FaithfulSMul.algebraMap_injective K₂ ↥L₂ ?_
    rw [← Classical.choose_spec (h.1 1)]
    simp
  map_zero' := by
    refine FaithfulSMul.algebraMap_injective K₂ ↥L₂ ?_
    rw [← Classical.choose_spec (h.1 0)]
    simp
  map_add' a b := by
    refine FaithfulSMul.algebraMap_injective K₂ ↥L₂ ?_
    calc (algebraMap K₂ ↥L₂) (Classical.choose (h.1 (a + b)))
        = τ ((algebraMap K₁ ↥L₁) (a + b)) := (Classical.choose_spec (h.1 (a + b))).symm
      _ = τ ((algebraMap K₁ ↥L₁) a + (algebraMap K₁ ↥L₁) b) := by rw [map_add]
      _ = τ ((algebraMap K₁ ↥L₁) a) + τ ((algebraMap K₁ ↥L₁) b) := by rw [map_add]
      _ = (algebraMap K₂ ↥L₂) (Classical.choose (h.1 a))
            + (algebraMap K₂ ↥L₂) (Classical.choose (h.1 b)) := by
            rw [← Classical.choose_spec (h.1 a), ← Classical.choose_spec (h.1 b)]
      _ = (algebraMap K₂ ↥L₂) (Classical.choose (h.1 a) + Classical.choose (h.1 b)) := by
            rw [map_add]
  map_mul' a b := by
    refine FaithfulSMul.algebraMap_injective K₂ ↥L₂ ?_
    calc (algebraMap K₂ ↥L₂) (Classical.choose (h.1 (a * b)))
        = τ ((algebraMap K₁ ↥L₁) (a * b)) := (Classical.choose_spec (h.1 (a * b))).symm
      _ = τ ((algebraMap K₁ ↥L₁) a * (algebraMap K₁ ↥L₁) b) := by rw [map_mul]
      _ = τ ((algebraMap K₁ ↥L₁) a) * τ ((algebraMap K₁ ↥L₁) b) := by rw [map_mul]
      _ = (algebraMap K₂ ↥L₂) (Classical.choose (h.1 a))
            * (algebraMap K₂ ↥L₂) (Classical.choose (h.1 b)) := by
            rw [← Classical.choose_spec (h.1 a), ← Classical.choose_spec (h.1 b)]
      _ = (algebraMap K₂ ↥L₂) (Classical.choose (h.1 a) * Classical.choose (h.1 b)) := by
            rw [map_mul]

/-- The defining property of `baseHomAux`. -/
private lemma baseHomAux_spec {L₁ : IntermediateField K₁ K₁'} {L₂ : IntermediateField K₂ K₂'}
    {τ : ↥L₁ ≃+* ↥L₂} (h : NK.Reconstruct.MapsBaseLevel L₁ L₂ τ) (a : K₁) :
    τ (algebraMap K₁ ↥L₁ a) = algebraMap K₂ ↥L₂ (baseHomAux h a) :=
  Classical.choose_spec (h.1 a)

/-- The inverse direction of the induced base-field map. -/
private noncomputable def baseHomSymmAux {L₁ : IntermediateField K₁ K₁'}
    {L₂ : IntermediateField K₂ K₂'}
    {τ : ↥L₁ ≃+* ↥L₂} (h : NK.Reconstruct.MapsBaseLevel L₁ L₂ τ) : K₂ →+* K₁ where
  toFun b := Classical.choose (h.2 b)
  map_one' := by
    refine FaithfulSMul.algebraMap_injective K₁ ↥L₁ ?_
    rw [← Classical.choose_spec (h.2 1)]
    simp
  map_zero' := by
    refine FaithfulSMul.algebraMap_injective K₁ ↥L₁ ?_
    rw [← Classical.choose_spec (h.2 0)]
    simp
  map_add' a b := by
    refine FaithfulSMul.algebraMap_injective K₁ ↥L₁ ?_
    calc (algebraMap K₁ ↥L₁) (Classical.choose (h.2 (a + b)))
        = τ.symm ((algebraMap K₂ ↥L₂) (a + b)) := (Classical.choose_spec (h.2 (a + b))).symm
      _ = τ.symm ((algebraMap K₂ ↥L₂) a + (algebraMap K₂ ↥L₂) b) := by rw [map_add]
      _ = τ.symm ((algebraMap K₂ ↥L₂) a) + τ.symm ((algebraMap K₂ ↥L₂) b) := by rw [map_add]
      _ = (algebraMap K₁ ↥L₁) (Classical.choose (h.2 a))
            + (algebraMap K₁ ↥L₁) (Classical.choose (h.2 b)) := by
            rw [← Classical.choose_spec (h.2 a), ← Classical.choose_spec (h.2 b)]
      _ = (algebraMap K₁ ↥L₁) (Classical.choose (h.2 a) + Classical.choose (h.2 b)) := by
            rw [map_add]
  map_mul' a b := by
    refine FaithfulSMul.algebraMap_injective K₁ ↥L₁ ?_
    calc (algebraMap K₁ ↥L₁) (Classical.choose (h.2 (a * b)))
        = τ.symm ((algebraMap K₂ ↥L₂) (a * b)) := (Classical.choose_spec (h.2 (a * b))).symm
      _ = τ.symm ((algebraMap K₂ ↥L₂) a * (algebraMap K₂ ↥L₂) b) := by rw [map_mul]
      _ = τ.symm ((algebraMap K₂ ↥L₂) a) * τ.symm ((algebraMap K₂ ↥L₂) b) := by rw [map_mul]
      _ = (algebraMap K₁ ↥L₁) (Classical.choose (h.2 a))
            * (algebraMap K₁ ↥L₁) (Classical.choose (h.2 b)) := by
            rw [← Classical.choose_spec (h.2 a), ← Classical.choose_spec (h.2 b)]
      _ = (algebraMap K₁ ↥L₁) (Classical.choose (h.2 a) * Classical.choose (h.2 b)) := by
            rw [map_mul]

/-- The defining property of `baseHomSymmAux`. -/
private lemma baseHomSymmAux_spec {L₁ : IntermediateField K₁ K₁'} {L₂ : IntermediateField K₂ K₂'}
    {τ : ↥L₁ ≃+* ↥L₂} (h : NK.Reconstruct.MapsBaseLevel L₁ L₂ τ) (b : K₂) :
    τ.symm (algebraMap K₂ ↥L₂ b) = algebraMap K₁ ↥L₁ (baseHomSymmAux h b) :=
  Classical.choose_spec (h.2 b)

/-- **The ring isomorphism `K₁ ≃+* K₂` of base fields induced by a base-level-compatible
isomorphism of levels.** -/
private noncomputable def baseEquivAux {L₁ : IntermediateField K₁ K₁'}
    {L₂ : IntermediateField K₂ K₂'}
    {τ : ↥L₁ ≃+* ↥L₂} (h : NK.Reconstruct.MapsBaseLevel L₁ L₂ τ) : K₁ ≃+* K₂ where
  toFun := baseHomAux h
  invFun := baseHomSymmAux h
  left_inv a := by
    refine FaithfulSMul.algebraMap_injective K₁ ↥L₁ ?_
    calc (algebraMap K₁ ↥L₁) (baseHomSymmAux h (baseHomAux h a))
        = τ.symm ((algebraMap K₂ ↥L₂) (baseHomAux h a)) :=
          (baseHomSymmAux_spec h (baseHomAux h a)).symm
      _ = τ.symm (τ ((algebraMap K₁ ↥L₁) a)) := by rw [baseHomAux_spec h a]
      _ = (algebraMap K₁ ↥L₁) a := by rw [RingEquiv.symm_apply_apply]
  right_inv b := by
    refine FaithfulSMul.algebraMap_injective K₂ ↥L₂ ?_
    calc (algebraMap K₂ ↥L₂) (baseHomAux h (baseHomSymmAux h b))
        = τ ((algebraMap K₁ ↥L₁) (baseHomSymmAux h b)) :=
          (baseHomAux_spec h (baseHomSymmAux h b)).symm
      _ = τ (τ.symm ((algebraMap K₂ ↥L₂) b)) := by rw [baseHomSymmAux_spec h b]
      _ = (algebraMap K₂ ↥L₂) b := by rw [RingEquiv.apply_symm_apply]
  map_mul' := (baseHomAux h).map_mul
  map_add' := (baseHomAux h).map_add

/-- The defining property of `baseEquivAux`. -/
private lemma baseEquivAux_spec {L₁ : IntermediateField K₁ K₁'} {L₂ : IntermediateField K₂ K₂'}
    {τ : ↥L₁ ≃+* ↥L₂} (h : NK.Reconstruct.MapsBaseLevel L₁ L₂ τ) (a : K₁) :
    τ (algebraMap K₁ ↥L₁ a) = algebraMap K₂ ↥L₂ (baseEquivAux h a) :=
  baseHomAux_spec h a

end Aux

/-! ## An automorphism of a number field fixing every prime is trivial -/

/-- **A ring automorphism of a number field fixing every finite prime is trivial.** -/
private lemma eq_one_of_primeTransport_eq_self_aux {K : Type*} [Field K] [NumberField K]
    (σ : K ≃+* K)
    (h : ∀ P : NK.Chebotarev.PrimeIdeal K, NK.Reconstruct.primeTransport σ P = P) :
    σ = 1 := by
  classical
  have hfix : ∀ q : ℚ, σ (algebraMap ℚ K q) = algebraMap ℚ K q := by
    intro q
    simpa using map_ratCast σ q
  let σa : K ≃ₐ[ℚ] K := AlgEquiv.ofRingEquiv (f := σ) hfix
  let F : IntermediateField ℚ K := IntermediateField.fixedField (Subgroup.zpowers σa)
  haveI hFfd : FiniteDimensional ↥F K := inferInstance
  haveI hFgal : IsGalois ↥F K := IsGalois.of_fixed_field K (Subgroup.zpowers σa)
  haveI hFnum : NumberField ↥F :=
    Commons.NumberTheory.NumberField.numberField_of_intermediateField F
  have hfixF : ∀ x : ↥F, σ (algebraMap ↥F K x) = algebraMap ↥F K x := by
    intro x
    have hx : (x : K) ∈ F := x.2
    have hmem : σa (x : K) = (x : K) :=
      (IntermediateField.mem_fixedField_iff (Subgroup.zpowers σa) (x : K)).mp hx σa
        (Subgroup.mem_zpowers σa)
    show σ (x : K) = (x : K)
    rw [← AlgEquiv.ofRingEquiv_apply (f := σ) hfix (x : K)]
    exact hmem
  let σF : K ≃ₐ[↥F] K := AlgEquiv.ofRingEquiv (f := σ) hfixF
  have hσFcoe : σF.toRingEquiv = σ := by
    apply RingEquiv.ext
    intro x
    exact AlgEquiv.ofRingEquiv_apply (f := σ) hfixF x
  obtain ⟨𝔮, hsplit⟩ :=
    Commons.NumberTheory.NumberField.exists_prime_splitsCompletely (K := ↥F) (L := K)
  obtain ⟨P, hP⟩ :=
    Commons.NumberTheory.NumberField.exists_heightOneSpectrum_liesOver (K := ↥F) (L := K) 𝔮
  have hsmul : σF • P = P := by
    rw [← NK.ReconstructField.primeTransport_eq_smul σF P, hσFcoe]
    exact h P
  have hσF1 : σF = 1 :=
    NK.UchidaKummer.eq_one_of_smul_eq_of_splitsCompletely hsplit hP hsmul
  have hcoe : (σF.toRingEquiv : K ≃+* K) = 1 := by rw [hσF1]; rfl
  rwa [hσFcoe] at hcoe

/-! ## The base-field compatibility of a level isomorphism inducing the prime correspondence -/

theorem primeTransport_eq_levelPrimeMap_imp_base {K₁ K₂ K₁' K₂' : Type*} [Field K₁] [Field K₂]
    [Field K₁'] [Field K₂'] [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
    [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']
    (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (hϕ : IsHomeomorph ϕ)
    (a : NK.Reconstruct.LocalCorrespondence ϕ) (τ₀ : K₁ ≃+* K₂)
    (hbase : ∀ 𝔭 : NK.Chebotarev.PrimeIdeal K₁,
      a.primeMap 𝔭 = NK.Reconstruct.primeTransport τ₀ 𝔭)
    (L : IntermediateField K₁ K₁') [FiniteDimensional K₁ L] [Normal K₁ L] [NumberField ↥L]
    [FiniteDimensional K₂ (NK.Reconstruct.levelMap ϕ L)]
    [Normal K₂ (NK.Reconstruct.levelMap ϕ L)] [NumberField ↥(NK.Reconstruct.levelMap ϕ L)]
    [IsGalois ℚ ↥(NK.Reconstruct.levelMap ϕ L)]
    (τ : ↥L ≃+* ↥(NK.Reconstruct.levelMap ϕ L))
    (hτ : NK.Reconstruct.primeTransport τ =
      NK.ReconstructField.levelPrimeMap ϕ hϕ a L) :
    NK.Reconstruct.MapsBaseLevel L (NK.Reconstruct.levelMap ϕ L) τ ∧
      (∀ x : K₁, τ (algebraMap K₁ ↥L x) =
        algebraMap K₂ ↥(NK.Reconstruct.levelMap ϕ L) (τ₀ x)) := by
  classical
  haveI hgalL : IsGalois K₁ ↥L := Commons.FieldTheory.Galois.isGalois_of_normal_of_charZero
  haveI hgalM : IsGalois K₂ ↥(NK.Reconstruct.levelMap ϕ L) :=
    Commons.FieldTheory.Galois.isGalois_of_normal_of_charZero
  -- a rational prime splitting completely in the transported level
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
  -- the conjugation by `τ` reproduces the correspondence of `ϕ` on the Galois groups
  have hML : NK.Reconstruct.MapsBaseLevel L (NK.Reconstruct.levelMap ϕ L) τ :=
    mapsBaseLevel_of_conjRingEquiv_eq ϕ hϕ L τ
      (conjRingEquiv_eq_levelMapEquiv_of_primeTransport_eq ϕ hϕ a L τ hτ p hsplit)
  refine ⟨hML, ?_⟩
  -- the base-field isomorphism induced by `τ`
  let σ' : K₁ ≃+* K₂ := baseEquivAux hML
  have hσ'spec : ∀ x : K₁, τ (algebraMap K₁ ↥L x) =
      algebraMap K₂ ↥(NK.Reconstruct.levelMap ϕ L) (σ' x) := fun x => baseEquivAux_spec hML x
  -- the two isomorphisms `σ'` and `τ₀` induce the same map on primes
  have hprime : ∀ P : NK.Chebotarev.PrimeIdeal K₁,
      NK.Reconstruct.primeTransport σ' P = NK.Reconstruct.primeTransport τ₀ P := by
    intro P
    obtain ⟨P', hP'⟩ := NK.Chebotarev.exists_primeIdeal_liesOver (K := K₁) (L := ↥L) P
    apply IsDedekindDomain.HeightOneSpectrum.ext
    have h1 : (NK.Reconstruct.primeTransport σ' P).asIdeal
        = (NK.Reconstruct.primeTransport τ P').asIdeal.under (NumberField.RingOfIntegers K₂) := by
      have h := NK.ReconstructField.under_map_ringOfIntegersEquiv τ σ' hσ'spec P'.asIdeal
      rw [hP'.over.symm, ← NK.ReconstructField.primeTransport_asIdeal σ' P] at h
      rw [← h, ← NK.ReconstructField.primeTransport_asIdeal τ P']
    have h2 : (NK.Reconstruct.primeTransport τ₀ P).asIdeal
        = (NK.Reconstruct.primeTransport τ P').asIdeal.under (NumberField.RingOfIntegers K₂) := by
      have hlev : (NK.Reconstruct.primeTransport τ P').asIdeal
          = (NK.ReconstructField.levelPrimeMap ϕ hϕ a L P').asIdeal :=
        congrArg IsDedekindDomain.HeightOneSpectrum.asIdeal (congrFun hτ P')
      have hlies : (NK.ReconstructField.levelPrimeMap ϕ hϕ a L P').asIdeal.under
            (NumberField.RingOfIntegers K₂) = (a.primeMap P).asIdeal :=
        (NK.ReconstructField.levelPrimeMap_liesOver ϕ hϕ a L P P' hP').over.symm
      rw [hlev, hlies, ← congrArg IsDedekindDomain.HeightOneSpectrum.asIdeal (hbase P)]
    rw [h1, h2]
  -- the ratio `τ₀⁻¹ ∘ σ'` fixes every prime, hence is trivial
  let ψ : K₁ ≃+* K₁ := σ'.trans τ₀.symm
  have hψ : ∀ P : NK.Chebotarev.PrimeIdeal K₁, NK.Reconstruct.primeTransport ψ P = P := by
    intro P
    have h1 : NK.Reconstruct.primeTransport ψ P
        = NK.Reconstruct.primeTransport τ₀.symm (NK.Reconstruct.primeTransport σ' P) :=
      primeTransport_trans σ' τ₀.symm P
    rw [h1, hprime P]
    have h2 := primeTransport_trans τ₀ τ₀.symm P
    rw [show τ₀.trans τ₀.symm = RingEquiv.refl K₁ from RingEquiv.ext (fun x => by simp),
      primeTransport_refl] at h2
    exact h2.symm
  have hσ'τ₀ : σ' = τ₀ := by
    have hψ1 : ψ = 1 := eq_one_of_primeTransport_eq_self_aux ψ hψ
    ext x
    have hx : τ₀.symm (σ' x) = x := by
      have h := congrArg (fun (θ : K₁ ≃+* K₁) => θ x) hψ1
      change τ₀.symm (σ' x) = x at h
      exact h
    have h2 := congrArg (fun y : K₁ => τ₀ y) hx
    simpa using h2
  intro x
  calc τ (algebraMap K₁ ↥L x)
      = algebraMap K₂ ↥(NK.Reconstruct.levelMap ϕ L) (σ' x) := hσ'spec x
    _ = algebraMap K₂ ↥(NK.Reconstruct.levelMap ϕ L) (τ₀ x) := by rw [hσ'τ₀]


end NK.ReconstructField
