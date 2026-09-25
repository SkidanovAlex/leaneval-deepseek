import Mathlib
import Submission.NK.Reconstruct.Transport
import Submission.NK.Reconstruct.isFrobAt_primeTransport_iff_inv
import Submission.NK.Reconstruct.finiteDimensional_sigmaLevel
import Submission.NK.Reconstruct.normal_sigmaLevel
import Submission.NK.Reconstruct.mapsBaseLevel_sigmaLevelEquiv
import Submission.NK.Reconstruct.restrictNormalHom_conjHomEquiv
import Submission.NK.Mine.eq_of_preserves_decompositionGroup_and_frobenius
import Submission.Commons.NumberTheory.NumberField.numberField_of_intermediateField
import Submission.Commons.FieldTheory.Galois.isGalois_of_normal_of_charZero

/-!
# A Frobenius correspondence forces the conjugating isomorphism (Neukirch–Uchida)

Let `K₁`, `K₂` be number fields with separable closures `K₁'`, `K₂'`, let
`ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)` be an isomorphism of absolute Galois groups and let
`σ : K₂' ≃+* K₁'` be a field isomorphism carrying the embedded copy of `K₂` onto the embedded copy
of `K₁` (`Submission.NeukirchUchida.MapsBase`).  Assume the *Frobenius correspondence*
`NK.Reconstruct.FrobeniusCorrespondence ϕ σ`: at every pair of finite levels `L₁/K₁`, `L₂/K₂`
related by `σ`, and every prime `P` of `𝓞 L₁` lying over an unramified prime of `K₁` at which `g`
is a Frobenius element, the element `ϕ g` is a Frobenius element at the corresponding prime of
`𝓞 L₂`.

Then `ϕ` is the conjugation by `σ`: `ϕ g = σ ∘ g ∘ σ⁻¹` for every `g`.  The proof does *not* use
Čebotarev's density theorem: it suffices that the Frobenius elements at unramified primes generate
the Galois group of every finite Galois level (`NK.Mine.FrobeniusGenerateTopUnramified`).  The
detection of `ϕ` by its action on Frobenius elements is `NK.Mine.eq_of_preserves_frobenius`,
applied to the automorphism `ϕ ∘ conjHomEquiv hσ⁻¹` of `Gal(K₂'/K₂)`.

The main auxiliary results proved here are

* `NK.Mine.ramificationIdx_primeTransport` — a level isomorphism compatible with the base fields
  preserves ramification indices of corresponding primes;
* `NK.Mine.primeTransport_symm_transport` — the obvious inverse property of `primeTransport`;
* `NK.Mine.restrictNormalHom_conjHomEquiv_symm` — the restriction of the inverse of
  `conjHomEquiv` to a finite level.
-/

namespace NK.Mine

open NumberField

/-- **A ring equivalence of Dedekind domains induces a ring equivalence of their ideal monoids.**
This is `Ideal.map` bundled, used to transport multiplicities (hence ramification indices). -/
noncomputable def idealMapRingEquiv {R S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S) :
    Ideal R ≃+* Ideal S :=
  RingEquiv.ofBijective (Ideal.mapHom e) (by
    have hcR : (e.symm : S →+* R).comp (e : R →+* S) = RingHom.id R := by ext x; simp
    have hcS : (e : R →+* S).comp (e.symm : S →+* R) = RingHom.id S := by ext x; simp
    constructor
    · intro I J h
      have h' : Ideal.map (e : R →+* S) I = Ideal.map (e : R →+* S) J := h
      have hkey : ∀ (K : Ideal R),
          Ideal.map (e.symm : S →+* R) (Ideal.map (e : R →+* S) K) = K := by
        intro K
        rw [Ideal.map_map, hcR, Ideal.map_id]
      have h2 := congrArg (fun (K : Ideal S) => Ideal.map (e.symm : S →+* R) K) h'
      rw [hkey I, hkey J] at h2
      exact h2
    · intro J
      refine ⟨Ideal.map (e.symm : S →+* R) J, ?_⟩
      show Ideal.map (e : R →+* S) (Ideal.map (e.symm : S →+* R) J) = J
      rw [Ideal.map_map, hcS, Ideal.map_id])

/-- `NK.Reconstruct.ringOfIntegersEquiv` is the canonical `RingOfIntegers.mapRingEquiv`. -/
lemma ringOfIntegersEquiv_eq_mapRingEquiv {L₁ L₂ : Type*} [Field L₁] [Field L₂]
    (τ : L₁ ≃+* L₂) :
    NK.Reconstruct.ringOfIntegersEquiv τ = NumberField.RingOfIntegers.mapRingEquiv τ := by
  ext x
  rw [NK.Reconstruct.ringOfIntegersEquiv_apply, NumberField.RingOfIntegers.mapRingEquiv_apply]

/-- The inverse of `RingOfIntegers.mapRingEquiv` is the map of the inverse isomorphism. -/
lemma mapRingEquiv_symm {K L : Type*} [Field K] [Field L] (e : K ≃+* L) :
    (NumberField.RingOfIntegers.mapRingEquiv e).symm =
      NumberField.RingOfIntegers.mapRingEquiv e.symm := by
  ext x
  rw [NumberField.RingOfIntegers.mapRingEquiv_symm_apply,
    NumberField.RingOfIntegers.mapRingEquiv_apply]

/-- **A level isomorphism compatible with the base fields preserves ramification indices.**

For `τ : ↥L₁ ≃+* ↥L₂` a ring isomorphism of finite levels compatible with the embeddings of the
number fields `K₁`, `K₂` (`NK.Reconstruct.MapsBaseLevel`), and a prime `P` of `𝓞 L₁`, the
transported prime `primeTransport τ P` of `𝓞 L₂` has the same ramification index over `𝓞 K₂` as
`P` has over `𝓞 K₁`.

The proof reduces the ramification index to the multiplicity of the prime in the extension of the
base prime (`Ideal.IsDedekindDomain.ramificationIdx_eq_multiplicity`) and transports this
multiplicity along the ring equivalence of ideal monoids induced by `τ`. -/
theorem ramificationIdx_primeTransport {K₁ K₂ K₁' K₂' : Type*} [Field K₁] [Field K₂]
    [Field K₁'] [Field K₂'] [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
    [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂'] {L₁ : IntermediateField K₁ K₁'}
    {L₂ : IntermediateField K₂ K₂'} [FiniteDimensional K₁ ↥L₁] [NumberField ↥L₁]
    [FiniteDimensional K₂ ↥L₂] [NumberField ↥L₂] {τ : ↥L₁ ≃+* ↥L₂}
    (h : NK.Reconstruct.MapsBaseLevel L₁ L₂ τ) (P : NK.Chebotarev.PrimeIdeal ↥L₁) :
    (NK.Reconstruct.primeTransport τ P).asIdeal.ramificationIdx (NumberField.RingOfIntegers K₂) =
      P.asIdeal.ramificationIdx (NumberField.RingOfIntegers K₁) := by
  let ea : 𝓞 ↥L₁ →+* 𝓞 ↥L₂ := NK.Reconstruct.ringOfIntegersEquiv τ
  let eb : 𝓞 K₁ →+* 𝓞 K₂ :=
    NumberField.RingOfIntegers.mapRingEquiv (NK.Reconstruct.PrimeTransportInv.transportBaseEquiv h)
  let f₂ : 𝓞 K₂ →+* 𝓞 ↥L₂ := algebraMap _ _
  let f₁ : 𝓞 K₁ →+* 𝓞 ↥L₁ := algebraMap _ _
  have hcomp : f₂.comp eb = ea.comp f₁ := by
    apply RingHom.ext
    intro x
    exact (NK.Reconstruct.PrimeTransportInv.ringOfIntegersEquiv_map_transportBase h x).symm
  have hpt : (NK.Reconstruct.primeTransport τ P).asIdeal = Ideal.map ea P.asIdeal := by
    show (NK.Reconstruct.primeTransport τ P).asIdeal =
      Ideal.map (NK.Reconstruct.ringOfIntegersEquiv τ) P.asIdeal
    exact NK.Reconstruct.PrimeTransportInv.primeTransport_asIdeal P
  have hp0 : Ideal.map f₁ (P.asIdeal.under (𝓞 K₁)) ≠ ⊥ := by
    rw [Ideal.under_def]
    exact Ideal.map_ne_bot_of_ne_bot
      (Ideal.IsIntegral.comap_ne_bot (𝓞 K₁) P.ne_bot)
  have hmap : Ideal.map f₂ ((Ideal.map ea P.asIdeal).under (𝓞 K₂)) =
      Ideal.map ea (Ideal.map f₁ (P.asIdeal.under (𝓞 K₁))) := by
    have h1 : (Ideal.map ea P.asIdeal).under (𝓞 K₂) =
        Ideal.map eb (P.asIdeal.under (𝓞 K₁)) := by
      show (NK.Reconstruct.primeTransport τ P).asIdeal.under (𝓞 K₂) =
        Ideal.map (NumberField.RingOfIntegers.mapRingEquiv
          (NK.Reconstruct.PrimeTransportInv.transportBaseEquiv h))
          (P.asIdeal.under (𝓞 K₁))
      exact NK.Reconstruct.PrimeTransportInv.under_primeTransport_eq_map h P
    rw [h1, Ideal.map_map, Ideal.map_map, hcomp]
  have hp0' : Ideal.map f₂ ((Ideal.map ea P.asIdeal).under (𝓞 K₂)) ≠ ⊥ := by
    rw [hmap]
    intro hbot
    refine hp0 ?_
    rw [Ideal.map_eq_bot_iff_of_injective] at hbot
    · exact hbot
    · show Function.Injective (NK.Reconstruct.ringOfIntegersEquiv τ)
      exact (NK.Reconstruct.ringOfIntegersEquiv τ).injective
  have hprime : (Ideal.map ea P.asIdeal).IsPrime := by
    show (NK.Reconstruct.primeTransport τ P).asIdeal.IsPrime
    exact Ideal.map_isPrime_of_equiv (NK.Reconstruct.ringOfIntegersEquiv τ)
  calc (NK.Reconstruct.primeTransport τ P).asIdeal.ramificationIdx (𝓞 K₂)
      = (Ideal.map ea P.asIdeal).ramificationIdx (𝓞 K₂) := by rw [hpt]
    _ = multiplicity (Ideal.map ea P.asIdeal)
          (Ideal.map f₂ ((Ideal.map ea P.asIdeal).under (𝓞 K₂))) :=
        Ideal.IsDedekindDomain.ramificationIdx_eq_multiplicity _ _ hp0'
    _ = multiplicity (Ideal.map ea P.asIdeal)
          (Ideal.map ea (Ideal.map f₁ (P.asIdeal.under (𝓞 K₁)))) := by
        rw [hmap]
    _ = multiplicity P.asIdeal
          (Ideal.map f₁ (P.asIdeal.under (𝓞 K₁))) :=
        multiplicity_map_eq (idealMapRingEquiv (NK.Reconstruct.ringOfIntegersEquiv τ))
    _ = P.asIdeal.ramificationIdx (𝓞 K₁) :=
        (Ideal.IsDedekindDomain.ramificationIdx_eq_multiplicity _ _ hp0).symm

/-- **The primes of two corresponding levels are matched by `primeTransport` and its inverse.**

For a level isomorphism `τ : ↥L₁ ≃+* ↥L₂` of finite levels and a prime `P` of `𝓞 L₂`, transporting
`P` to `𝓞 L₁` by `τ⁻¹` and back by `τ` returns `P`. -/
theorem primeTransport_symm_transport {K₁ K₂ K₁' K₂' : Type*} [Field K₁] [Field K₂] [Field K₁']
    [Field K₂'] [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
    [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂'] {L₁ : IntermediateField K₁ K₁'}
    {L₂ : IntermediateField K₂ K₂'} [FiniteDimensional K₁ ↥L₁] [NumberField ↥L₁]
    [FiniteDimensional K₂ ↥L₂] [NumberField ↥L₂] {τ : ↥L₁ ≃+* ↥L₂}
    (P : NK.Chebotarev.PrimeIdeal ↥L₂) :
    NK.Reconstruct.primeTransport τ (NK.Reconstruct.primeTransport τ.symm P) = P := by
  apply IsDedekindDomain.HeightOneSpectrum.ext
  show Ideal.map (NK.Reconstruct.ringOfIntegersEquiv τ)
      (Ideal.map (NK.Reconstruct.ringOfIntegersEquiv τ.symm) P.asIdeal) = P.asIdeal
  rw [ringOfIntegersEquiv_eq_mapRingEquiv, ringOfIntegersEquiv_eq_mapRingEquiv,
    ← mapRingEquiv_symm τ]
  show Ideal.map (NumberField.RingOfIntegers.mapRingEquiv τ : 𝓞 ↥L₁ →+* 𝓞 ↥L₂)
      (Ideal.map ((NumberField.RingOfIntegers.mapRingEquiv τ).symm : 𝓞 ↥L₂ →+* 𝓞 ↥L₁)
        P.asIdeal) = P.asIdeal
  rw [Ideal.map_map]
  have hc : ((NumberField.RingOfIntegers.mapRingEquiv τ) : 𝓞 ↥L₁ →+* 𝓞 ↥L₂).comp
      (((NumberField.RingOfIntegers.mapRingEquiv τ).symm) : 𝓞 ↥L₂ →+* 𝓞 ↥L₁) =
      RingHom.id _ := by
    apply RingHom.ext; intro x; simp
  rw [hc, Ideal.map_id]

section LevelRestriction

variable {K₁ K₂ K₁' K₂' : Type*} [Field K₁] [Field K₂] [Field K₁'] [Field K₂']
  [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
  [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']

/-- **The two round trips of `conjAlgEquiv`.**  The conjugate by `τ` of the conjugate by `τ⁻¹` is
the original automorphism.  (The companion of `NK.Reconstruct.conjAlgEquiv_conjAlgEquiv_symm` in
the opposite order.) -/
lemma conjAlgEquiv_symm_conjAlgEquiv {L₁ : IntermediateField K₁ K₁'}
    {L₂ : IntermediateField K₂ K₂'} (τ : ↥L₁ ≃+* ↥L₂)
    (h : NK.Reconstruct.MapsBaseLevel L₁ L₂ τ) (v : Gal(↥L₁/K₁)) :
    NK.Reconstruct.conjAlgEquiv τ.symm h.symm (NK.Reconstruct.conjAlgEquiv τ h v) = v := by
  ext x
  simp only [NK.Reconstruct.conjAlgEquiv_apply]
  simp

/-- **The restriction of the inverse of `conjHomEquiv` to a finite level.**

`Submission.NeukirchUchida.conjHomEquiv hσ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)` is the conjugation by
`σ`.  On the finite level `L ⊆ K₂'`, the inverse isomorphism is the conjugation by the level
isomorphism `sigmaLevelEquiv σ hσ L : σ(L) ≃+* L` — in the direction of the inverse. -/
lemma restrictNormalHom_conjHomEquiv_symm (σ : K₂' ≃+* K₁')
    (hσ : Submission.NeukirchUchida.MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂') σ)
    (L : IntermediateField K₂ K₂') [FiniteDimensional K₂ L] [Normal K₂ L] [NumberField ↥L]
    [FiniteDimensional K₁ ↥(NK.Reconstruct.sigmaLevel σ hσ L)]
    [Normal K₁ ↥(NK.Reconstruct.sigmaLevel σ hσ L)]
    (g : Gal(K₂'/K₂)) :
    AlgEquiv.restrictNormalHom (NK.Reconstruct.sigmaLevel σ hσ L)
        ((Submission.NeukirchUchida.conjHomEquiv hσ).symm g) =
      NK.Reconstruct.conjAlgEquiv (NK.Reconstruct.sigmaLevelEquiv σ hσ L).symm
        (NK.Reconstruct.mapsBaseLevel_sigmaLevelEquiv σ hσ L).symm
        (AlgEquiv.restrictNormalHom L g) := by
  have h1 := NK.Reconstruct.restrictNormalHom_conjHomEquiv σ hσ L
    (h := NK.Reconstruct.mapsBaseLevel_sigmaLevelEquiv σ hσ L)
    ((Submission.NeukirchUchida.conjHomEquiv hσ).symm g)
  simp only [MulEquiv.apply_symm_apply] at h1
  have h2 := congrArg (NK.Reconstruct.conjAlgEquiv (NK.Reconstruct.sigmaLevelEquiv σ hσ L).symm
    (NK.Reconstruct.mapsBaseLevel_sigmaLevelEquiv σ hσ L).symm) h1
  rw [conjAlgEquiv_symm_conjAlgEquiv] at h2
  exact h2.symm

end LevelRestriction

theorem exists_sigma_of_frobeniusCorrespondence
    {K₁ K₂ K₁' K₂' : Type*} [Field K₁] [Field K₂] [Field K₁'] [Field K₂']
    [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
    [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']
    (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (σ : K₂' ≃+* K₁')
    (hσ : Submission.NeukirchUchida.MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂') σ)
    (b : NK.Reconstruct.FrobeniusCorrespondence ϕ σ) :
    ∃ σ' : K₂' ≃+* K₁', Submission.NeukirchUchida.Conjugates σ' ϕ := by
  -- `ϕ` is the conjugation by `σ`: we show that the automorphism
  -- `ρ = ϕ ∘ (conjHomEquiv hσ)⁻¹` of `Gal(K₂'/K₂)` is the identity.
  have hdetect : (Submission.NeukirchUchida.conjHomEquiv hσ).symm.trans ϕ = 1 := by
    refine eq_of_preserves_frobenius (K := K₂) (K' := K₂')
      ((Submission.NeukirchUchida.conjHomEquiv hσ).symm.trans ϕ) ?_
    intro L _ _ P g he hg
    haveI hLnf : NumberField ↥L :=
      Commons.NumberTheory.NumberField.numberField_of_intermediateField L
    haveI hLnormal : Normal K₂ L := inferInstance
    let L₁ : IntermediateField K₁ K₁' := NK.Reconstruct.sigmaLevel σ hσ L
    haveI hL₁fd : FiniteDimensional K₁ L₁ :=
      NK.Reconstruct.finiteDimensional_sigmaLevel σ hσ L
    haveI hL₁n : Normal K₁ L₁ := NK.Reconstruct.normal_sigmaLevel σ hσ L
    haveI hL₁nf : NumberField ↥L₁ :=
      Commons.NumberTheory.NumberField.numberField_of_intermediateField L₁
    haveI hL₁gal : IsGalois K₁ ↥L₁ :=
      Commons.FieldTheory.Galois.isGalois_of_normal_of_charZero
    let τ : ↥L₁ ≃+* ↥L := NK.Reconstruct.sigmaLevelEquiv σ hσ L
    have hτbase : NK.Reconstruct.MapsBaseLevel L₁ L τ :=
      NK.Reconstruct.mapsBaseLevel_sigmaLevelEquiv σ hσ L
    have hτσ : ∀ x : ↥L₁, (τ x : K₂') = σ.symm (x : K₁') := fun x =>
      NK.Reconstruct.sigmaLevelEquiv_apply σ hσ L x
    let P₁ : NK.Chebotarev.PrimeIdeal ↥L₁ := NK.Reconstruct.primeTransport τ.symm P
    -- the transported prime is indeed the preimage of `P`
    have hP₁ : NK.Reconstruct.primeTransport τ P₁ = P :=
      primeTransport_symm_transport (τ := τ) P
    -- `h` is a Frobenius element at `P₁`
    have hP₁frob : NK.Chebotarev.IsFrobAt P₁
        (AlgEquiv.restrictNormalHom L₁ ((Submission.NeukirchUchida.conjHomEquiv hσ).symm g)) := by
      have hA : AlgEquiv.restrictNormalHom L₁
            ((Submission.NeukirchUchida.conjHomEquiv hσ).symm g) =
          NK.Reconstruct.conjAlgEquiv τ.symm hτbase.symm
            (AlgEquiv.restrictNormalHom L g) := restrictNormalHom_conjHomEquiv_symm σ hσ L g
      rw [hA, ← NK.Reconstruct.isFrobAt_primeTransport_iff_inv (h := hτbase)
        (AlgEquiv.restrictNormalHom L g) P₁, hP₁]
      exact hg
    -- `P₁` is unramified over `K₁`
    have hram : P₁.asIdeal.ramificationIdx (𝓞 K₁) = 1 := by
      rw [← ramificationIdx_primeTransport hτbase P₁, hP₁]
      exact he
    -- the Frobenius correspondence gives that `ϕ h` is a Frobenius at `P`
    let p : NK.Chebotarev.PrimeIdeal K₁ :=
      ⟨P₁.asIdeal.under (𝓞 K₁), Ideal.IsPrime.under (𝓞 K₁) P₁.asIdeal, by
        rw [Ideal.under_def]
        exact Ideal.IsIntegral.comap_ne_bot (𝓞 K₁) P₁.ne_bot⟩
    have hb := b L L₁ τ hτσ p P₁ (Ideal.over_under P₁.asIdeal) hram
      ((Submission.NeukirchUchida.conjHomEquiv hσ).symm g) hP₁frob
    rwa [hP₁] at hb
  -- hence `ϕ = conjHomEquiv hσ`
  have hϕ : ϕ = Submission.NeukirchUchida.conjHomEquiv hσ := by
    apply MulEquiv.ext
    intro g
    have hu := congrArg (fun (e : Gal(K₂'/K₂) ≃* Gal(K₂'/K₂)) =>
      e (Submission.NeukirchUchida.conjHomEquiv hσ g)) hdetect
    rw [MulEquiv.trans_apply, MulEquiv.symm_apply_apply] at hu
    simpa using hu
  refine ⟨σ, hσ, ?_⟩
  intro g
  rw [hϕ]
  exact Submission.NeukirchUchida.conj_toRingEquiv hσ g

end NK.Mine
