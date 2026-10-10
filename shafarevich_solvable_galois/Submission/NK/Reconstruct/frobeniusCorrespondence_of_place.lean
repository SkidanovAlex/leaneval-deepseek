import Mathlib.FieldTheory.KrullTopology
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.RamificationInertia.Ramification
import Submission.NK.Reconstruct.PlaceCorrespondence
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The σ-based Frobenius correspondence from the place-based one

The *Frobenius correspondence* (input (b) of the reconstruction of Neukirch–Uchida) has two
equivalent presentations, compare `Submission/Work/Reconstruct/PlaceCorrespondence.lean`:

* the σ-free, place-based one, `NK.Reconstruct.FrobeniusCorrespondencePlace ϕ hϕ a`, and
* the σ-based one, `NK.Reconstruct.FrobeniusCorrespondence ϕ σ`, consumed by the endgame of
`NK.Reconstruct.exists_sigma_of_frobeniusCorrespondence`.

This file proves the passage between them: given a *realizing* field isomorphism `σ` of the place
correspondence `a` (`hreal`), the agreement of the level correspondences of `ϕ` and of `σ`
(`hlvl`), the place-based Frobenius correspondence `b` implies the σ-based one,
`NK.Reconstruct.FrobeniusCorrespondence ϕ σ`.

The mathematical content is:

* the level `L₁ ⊆ K₁'` of a pair identified by `σ` is `σ(L₂)` (`eq_sigmaLevel_of_ringEquiv`), so
  the level `levelMap ϕ L₁` of `ϕ` is `L₂` (`hlvl`);
* a place `A` of `K₁'` over a given prime `P` of the level `L₁` exists
  (`exists_place_over_prime`), and the level-prime of `A` is `P` (`primeOfLevel_eq_of_comap_eq`);
* the Frobenius statement produced by `b` at the level `L₁` is transported across the equality
  `levelMap ϕ L₁ = L₂` (`isFrobAt_primeOfLevel_of_eq`);
* the transported level-prime is `primeTransport τ P`, because `σ` realizes the place
  correspondence `a` (`comap_placeMap_level`) and because the valuation subring of the transformed
  prime is the transform of the valuation subring (`valuationSubringAtPrime_primeTransport`).
-/

set_option linter.style.haveILetI false

namespace NK.Reconstruct

open IsDedekindDomain

variable {K₁ K₂ K₁' K₂' : Type*} [Field K₁] [Field K₂] [Field K₁'] [Field K₂']
  [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
  [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']

/-! ## Transport of the ring of integers along a field isomorphism -/

/-- The isomorphism of rings of integers induced by a field isomorphism intertwines the two
inclusions of the rings of integers. -/
@[simp] lemma ringOfIntegersEquiv_algebraMap {L₁ L₂ : Type*} [Field L₁] [NumberField L₁] [Field L₂]
    [NumberField L₂] (τ : L₁ ≃+* L₂) (a : NumberField.RingOfIntegers L₁) :
    τ (algebraMap (NumberField.RingOfIntegers L₁) L₁ a) =
      algebraMap (NumberField.RingOfIntegers L₂) L₂ (ringOfIntegersEquiv τ a) := by
  simp

/-- The inverse form of `ringOfIntegersEquiv_algebraMap`. -/
@[simp] lemma ringOfIntegersEquiv_symm_algebraMap {L₁ L₂ : Type*} [Field L₁] [NumberField L₁]
    [Field L₂] [NumberField L₂] (τ : L₁ ≃+* L₂) (a : NumberField.RingOfIntegers L₂) :
    τ.symm (algebraMap (NumberField.RingOfIntegers L₂) L₂ a) =
      algebraMap (NumberField.RingOfIntegers L₁) L₁ ((ringOfIntegersEquiv τ).symm a) := by
  apply_fun τ
  rw [RingEquiv.apply_symm_apply,
    ringOfIntegersEquiv_algebraMap τ ((ringOfIntegersEquiv τ).symm a),
    RingEquiv.apply_symm_apply]

/-! ## The valuation subring of a transported prime -/

/-- **Membership in the valuation subring of a transported prime.**  For a ring isomorphism
`τ : L₁ ≃+* L₂` of number fields and a prime `P` of `𝓞 L₁`, an element `y : L₂` lies in the
valuation subring of `𝓞 L₂` at the transported prime `primeTransport τ P` if and only if `τ.symm y`
lies in the valuation subring of `𝓞 L₁` at `P`.  This is the elementwise form of
`valuationSubringAtPrime_primeTransport`, obtained from the localisation description of
`valuationSubringAtPrime`. -/
lemma key_valuationSubringAtPrime {L₁ L₂ : Type*} [Field L₁] [NumberField L₁] [Field L₂]
    [NumberField L₂] (τ : L₁ ≃+* L₂) (P : NK.Chebotarev.PrimeIdeal L₁) (y : L₂) :
    y ∈ IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime L₂ (primeTransport τ P) ↔
      τ.symm y ∈ IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime L₁ P := by
  rw [Commons.RingTheory.Valuation.mem_valuationSubringAtPrime,
    Commons.RingTheory.Valuation.mem_valuationSubringAtPrime]
  constructor
  · rintro ⟨a, s, hs, hy⟩
    refine ⟨(ringOfIntegersEquiv τ).symm a, (ringOfIntegersEquiv τ).symm s, ?_, ?_⟩
    · rw [Ideal.mem_primeCompl_iff]
      intro hmem
      refine (Ideal.mem_primeCompl_iff.mp hs) ?_
      change s ∈ Ideal.map (ringOfIntegersEquiv τ) P.asIdeal
      simpa using Ideal.mem_map_of_mem (ringOfIntegersEquiv τ) hmem
    · rw [hy]
      simp only [map_mul, map_inv₀]
      simp only [ringOfIntegersEquiv_symm_algebraMap]
  · rintro ⟨a, s, hs, hy⟩
    refine ⟨ringOfIntegersEquiv τ a, ringOfIntegersEquiv τ s, ?_, ?_⟩
    · rw [Ideal.mem_primeCompl_iff]
      intro hmem
      change ringOfIntegersEquiv τ s ∈ Ideal.map (ringOfIntegersEquiv τ) P.asIdeal at hmem
      obtain ⟨z, hz, hzx⟩ := (Ideal.mem_map_iff_of_surjective (ringOfIntegersEquiv τ)
        (ringOfIntegersEquiv τ).surjective).mp hmem
      exact (Ideal.mem_primeCompl_iff.mp hs) ((ringOfIntegersEquiv τ).injective hzx ▸ hz)
    · have h := congrArg τ hy
      simp only [map_mul, map_inv₀] at h
      simp only [RingEquiv.apply_symm_apply, ringOfIntegersEquiv_algebraMap] at h
      exact h

/-- **The valuation subring of a transported prime is the transform of the valuation subring.**
For a ring isomorphism `τ : L₁ ≃+* L₂` of number fields and a prime `P` of `𝓞 L₁`, the valuation
subring of `L₂` at the transported prime `primeTransport τ P` is the preimage under `τ.symm` of the
valuation subring of `L₁` at `P`. -/
lemma valuationSubringAtPrime_primeTransport {L₁ L₂ : Type*} [Field L₁] [NumberField L₁]
    [Field L₂] [NumberField L₂] (τ : L₁ ≃+* L₂) (P : NK.Chebotarev.PrimeIdeal L₁) :
    IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime L₂ (primeTransport τ P)
      = (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime L₁ P).comap
          (τ.symm : L₂ →+* L₁) := by
  ext y
  rw [ValuationSubring.mem_comap]
  exact key_valuationSubringAtPrime τ P y

/-! ## Places over primes of an intermediate level -/

/-- **A place of `K'` over a prime of an intermediate level.**  Let `L` be a finite level of
`K'/K` which is a number field, `p` a prime of `K` and `P` a prime of `𝓞 L` above `p`.  Then there
is a place `A` of `K'` whose trace on `L` is the valuation ring of `P`, and whose trace on `K` is
the valuation ring of `p`. -/
lemma exists_place_over_prime {K K' : Type*} [Field K] [NumberField K] [Field K'] [Algebra K K']
    (L : IntermediateField K K') [FiniteDimensional K L] [NumberField ↥L]
    (p : NK.Chebotarev.PrimeIdeal K) (P : NK.Chebotarev.PrimeIdeal ↥L)
    (hP : P.asIdeal.LiesOver p.asIdeal) :
    ∃ A : ValuationSubring K', A.comap (algebraMap ↥L K') =
        IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥L P ∧
      A.comap (algebraMap K K') =
        IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K p := by
  obtain ⟨A, hA⟩ := Commons.RingTheory.Valuation.exists_valuationSubring_comap_eq
    (K := ↥L) (L := K') (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥L P)
  refine ⟨A, hA, ?_⟩
  have hcomp : (algebraMap ↥L K').comp (algebraMap K ↥L) = algebraMap K K' := by
    ext x; exact IsScalarTower.algebraMap_apply K ↥L K' x
  rw [← hcomp, ← ValuationSubring.comap_comap, hA]
  exact Commons.RingTheory.Valuation.comap_valuationSubringAtPrime p P hP

/-- **The level-prime of a place.**  If the trace of a place `A` of `K'` on the level `L` is the
valuation ring at the prime `P`, then the prime of `𝓞 L` attached to `A` is `P`. -/
lemma primeOfLevel_eq_of_comap_eq {K K' : Type*} [Field K] [NumberField K] [Field K']
    [Algebra K K'] [IsSepClosure K K'] (L : IntermediateField K K') [NumberField ↥L]
    {A : ValuationSubring K'} {P : NK.Chebotarev.PrimeIdeal ↥L}
    (h : A.comap (algebraMap ↥L K') =
        IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥L P)
    (hA : A.comap (algebraMap ↥L K') ≠ ⊤) :
    primeOfLevel A L hA = P := by
  have h1 := primeOfLevel_spec A L hA
  rw [h] at h1
  exact Commons.RingTheory.Valuation.valuationSubringAtPrime_injective h1.symm

/-! ## Transport of Frobenius statements along an equality of levels -/

/-- **The Frobenius statement attached to a place is independent of the level.**  If `T = T'` are
intermediate fields of `K'/K`, then the statement that the restriction of `g` to `T` is a Frobenius
element at the level-prime of a place `B` of `K'` is equivalent to the corresponding statement for
the target `T'`: both are the statement that `g`, restricted to the level, is the Frobenius at the
prime below the place `B`. -/
theorem isFrobAt_primeOfLevel_of_eq {K K' : Type*} [Field K] [NumberField K] [Field K']
    [Algebra K K'] [IsSepClosure K K'] {T T' : IntermediateField K K'} (h : T = T')
    [FiniteDimensional K T] [NumberField ↥T] [Normal K T]
    [FiniteDimensional K T'] [NumberField ↥T'] [Normal K T']
    (B : ValuationSubring K') (hB : B.comap (algebraMap K K') ≠ ⊤) (g : Gal(K'/K)) :
    NK.Chebotarev.IsFrobAt (primeOfLevel B T (comap_level_ne_top hB T))
      (AlgEquiv.restrictNormalHom T g) ↔
    NK.Chebotarev.IsFrobAt (primeOfLevel B T' (comap_level_ne_top hB T'))
      (AlgEquiv.restrictNormalHom T' g) := by
  subst h
  exact Iff.rfl

/-! ## The level of `K₁'` attached to a level of `K₂'` by a realizing isomorphism -/

variable {K₁ K₂ K₁' K₂' : Type*} [Field K₁] [Field K₂] [Field K₁'] [Field K₂']
  [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
  [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']

/-- **A ring isomorphism of levels lying above `σ` determines its source level.**  If
`τ : ↥L₁ ≃+* ↥L₂` has `(τ x : K₂') = σ.symm (x : K₁')` for all `x`, then `L₁` is the image of
`L₂` under `σ`, i.e. `L₁ = sigmaLevel σ hσ L₂`. -/
theorem eq_sigmaLevel_of_ringEquiv (σ : K₂' ≃+* K₁')
    (hσ : Submission.NeukirchUchida.MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂') σ)
    {L₁ : IntermediateField K₁ K₁'} {L₂ : IntermediateField K₂ K₂'}
    (τ : ↥L₁ ≃+* ↥L₂) (hτ : ∀ x : ↥L₁, (τ x : K₂') = σ.symm (x : K₁')) :
    L₁ = sigmaLevel σ hσ L₂ := by
  ext x
  rw [mem_sigmaLevel]
  constructor
  · intro hx
    rw [← hτ ⟨x, hx⟩]
    exact (τ ⟨x, hx⟩).2
  · intro hx
    set y : ↥L₁ := τ.symm ⟨σ.symm x, hx⟩ with hy
    have h1 : (τ y : K₂') = σ.symm (y : K₁') := hτ y
    have h2 : (τ y : K₂') = σ.symm x := by simp [y]
    have h3 : (y : K₁') = x := by
      apply RingEquiv.injective σ.symm
      exact h1.symm.trans h2
    rw [← h3]
    exact y.2

/-- **The trace of a place below a corresponding place of the two levels.**  If `σ` realizes the
place correspondence `a` and `τ : ↥L₁ ≃+* ↥L₂` is the restriction of `σ.symm`, then the trace on
`𝓞 L₂` of the place `a.placeMap A` of `K₂'` is the transform, under `τ`, of the trace on `𝓞 L₁` of
the place `A` of `K₁'`. -/
lemma comap_placeMap_level {ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)} (a : LocalCorrespondence ϕ)
    (σ : K₂' ≃+* K₁')
    (hreal : ∀ A : FinitePlaceOf K₁ K₁', (a.placeMap A).1.comap (σ.symm : K₁' →+* K₂') = A.1)
    {L₁ : IntermediateField K₁ K₁'} {L₂ : IntermediateField K₂ K₂'}
    (τ : ↥L₁ ≃+* ↥L₂) (hτ : ∀ x : ↥L₁, (τ x : K₂') = σ.symm (x : K₁'))
    (A : FinitePlaceOf K₁ K₁') :
    (a.placeMap A).1.comap (algebraMap ↥L₂ K₂') =
      (A.1.comap (algebraMap ↥L₁ K₁')).comap (τ.symm : ↥L₂ →+* ↥L₁) := by
  ext y
  rw [ValuationSubring.mem_comap, ValuationSubring.mem_comap, ValuationSubring.mem_comap,
    ← hreal A, ValuationSubring.mem_comap]
  have key : σ.symm (algebraMap ↥L₁ K₁' (τ.symm y)) = algebraMap ↥L₂ K₂' y := by
    have h1 := hτ (τ.symm y)
    rw [RingEquiv.apply_symm_apply] at h1
    exact h1.symm
  exact Iff.of_eq (congrArg (fun z => z ∈ (a.placeMap A).1) key.symm)

/-! ## The Frobenius correspondence in the `σ`-based form -/

theorem frobeniusCorrespondence_of_place {K₁ K₂ K₁' K₂' : Type*} [Field K₁] [Field K₂] [Field K₁']
    [Field K₂'] [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
    [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂'] {ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)}
    (hϕ : IsHomeomorph ϕ) (a : NK.Reconstruct.LocalCorrespondence ϕ) (σ : K₂' ≃+* K₁')
    (hσ : Submission.NeukirchUchida.MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂') σ)
    (hreal : ∀ A : NK.Reconstruct.FinitePlaceOf K₁ K₁',
      (a.placeMap A).1.comap (σ.symm : K₁' →+* K₂') = A.1)
    (hlvl : NK.Reconstruct.AgreesOnLevels ϕ hϕ σ hσ)
    (b : NK.Reconstruct.FrobeniusCorrespondencePlace ϕ hϕ a) :
    NK.Reconstruct.FrobeniusCorrespondence ϕ σ := by
  intro L₂ _ _ _ L₁ _ _ _ τ hτ p P hP hunr g hg
  -- the level `L₁` is the image of `L₂` under `σ`
  have hL₁ : L₁ = sigmaLevel σ hσ L₂ := eq_sigmaLevel_of_ringEquiv σ hσ τ hτ
  subst hL₁
  -- hence the level of `ϕ` attached to it is `L₂`
  have hlevel : levelMap ϕ (sigmaLevel σ hσ L₂) = L₂ := hlvl L₂
  haveI hfdL : FiniteDimensional K₂ (levelMap ϕ (sigmaLevel σ hσ L₂)) :=
    finiteDimensional_levelMap hϕ (sigmaLevel σ hσ L₂)
  haveI hnL : Normal K₂ (levelMap ϕ (sigmaLevel σ hσ L₂)) :=
    normal_levelMap hϕ (sigmaLevel σ hσ L₂)
  haveI hnfL : NumberField ↥(levelMap ϕ (sigmaLevel σ hσ L₂)) :=
    numberField_levelMap hϕ (sigmaLevel σ hσ L₂)
  -- a place of `K₁'` over the prime `P` of the level
  obtain ⟨A, hAcomap, hAval⟩ := exists_place_over_prime (sigmaLevel σ hσ L₂) p P hP
  have hAne : A.comap (algebraMap K₁ K₁') ≠ ⊤ := by
    rw [hAval]; exact Commons.RingTheory.Valuation.valuationSubringAtPrime_ne_top p
  let A' : FinitePlaceOf K₁ K₁' := ⟨A, hAne⟩
  have hAL : (A'.1).comap (algebraMap ↥(sigmaLevel σ hσ L₂) K₁') ≠ ⊤ :=
    comap_level_ne_top A'.2 (sigmaLevel σ hσ L₂)
  have hprime : primeOfLevel A'.1 (sigmaLevel σ hσ L₂) hAL = P :=
    primeOfLevel_eq_of_comap_eq (sigmaLevel σ hσ L₂) hAcomap hAL
  -- the place-based Frobenius correspondence
  have hb : NK.Chebotarev.IsFrobAt
      (primeOfLevel (a.placeMap A').1 (levelMap ϕ (sigmaLevel σ hσ L₂))
        (comap_level_ne_top (a.placeMap A').2 (levelMap ϕ (sigmaLevel σ hσ L₂))))
      (AlgEquiv.restrictNormalHom (levelMap ϕ (sigmaLevel σ hσ L₂)) (ϕ g)) :=
    b (sigmaLevel σ hσ L₂) A' g (by rw [hprime]; exact hg)
  -- transported to the level `L₂`
  have hb₂ : NK.Chebotarev.IsFrobAt
      (primeOfLevel (a.placeMap A').1 L₂ (comap_level_ne_top (a.placeMap A').2 L₂))
      (AlgEquiv.restrictNormalHom L₂ (ϕ g)) :=
    (isFrobAt_primeOfLevel_of_eq hlevel (a.placeMap A').1 (a.placeMap A').2 (ϕ g)).mp hb
  -- the transported level-prime is the transport of `P` along `τ`
  have hQ : primeOfLevel (a.placeMap A').1 L₂ (comap_level_ne_top (a.placeMap A').2 L₂)
      = primeTransport τ P := by
    apply Commons.RingTheory.Valuation.valuationSubringAtPrime_injective (K := ↥L₂)
    rw [← primeOfLevel_spec (a.placeMap A').1 L₂ (comap_level_ne_top (a.placeMap A').2 L₂),
      comap_placeMap_level a σ hreal τ hτ A', hAcomap,
      ← valuationSubringAtPrime_primeTransport τ P]
  rw [hQ] at hb₂
  exact hb₂

end NK.Reconstruct
