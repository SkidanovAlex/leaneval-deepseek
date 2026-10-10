import Mathlib.FieldTheory.KrullTopology
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Submission.NK.ReconstructField.LevelMatch
import Submission.NK.ReconstructField.exists_ringEquiv_mapsBase_of_mapsBaseLevel
import Submission.NK.ReconstructField.levelPrimeMap_smul_of_lift
import Submission.NK.UchidaKummer.SplitPrimes
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The level-wise matching condition from the finite-level prime identification

`NK.ReconstructField.LevelMatch ϕ hϕ σ hσ L` says that a base-field-mapping isomorphism
`σ : K₂' ≃+* K₁'` of the separable closures agrees with `ϕ` on the finite Galois level `L ⊆ K₁'`,
modulo the corresponding level `levelMap ϕ L ⊆ K₂'`.  This file produces such a `σ` from the
*finite-level prime identification*: the hypothesis `hident` says that at every finite Galois
level `L` there is an isomorphism `τ : ↥L ≃+* ↥(levelMap ϕ L)` with `τ ∘ i₁ = i₂ ∘ τ₀` for a fixed
base-field isomorphism `τ₀ : K₁ ≃+* K₂` whose transport of primes reproduces the prime
correspondence `levelPrimeMap ϕ hϕ a L` induced by the local correspondence `a`.

The mathematical content is that the *prime* correspondence at a finite level determines the
correspondence of Galois groups: if the transport of primes along `τ` agrees with the prime
correspondence attached to `ϕ`, then conjugating `Gal(↥L/K₁)` by `τ` reproduces the restriction of
`ϕ` to the level (`LevelMatchAux.conjAlgEquiv_eq_restrictNormalHom_of_primeTransport_eq`).  The
argument is a single-prime argument: choose a prime `𝔭` of `K₂` splitting completely in
`levelMap ϕ L`; two elements of `Gal(levelMap ϕ L/K₂)` agreeing on the primes above `𝔭` are equal
(`NK.UchidaKummer.eq_of_forall_smul_eq_of_splitsCompletely`), and the transport of primes along
`τ` makes the two Galois elements agree on *all* primes, because every prime of `levelMap ϕ L` is
the transport of a prime of `L`.

The extension of `τ` to the separable closures (`exists_ringEquiv_mapsBase_of_mapsBaseLevel`) then
carries the level isomorphism to a `MapsBase` isomorphism `σ : K₂' ≃+* K₁'` with `σ∘i₂ = i₁∘τ₀`,
and the level condition follows by restricting the conjugation by `σ` to `levelMap ϕ L`.
-/

set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 400000

namespace NK.ReconstructField.LevelMatchAux

open NK.Reconstruct
open scoped Pointwise NumberField

variable {K₁ K₂ K₁' K₂' : Type*} [Field K₁] [Field K₂] [Field K₁'] [Field K₂']
  [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
  [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']

/-! ## Two round trips

The transport of primes along a ring isomorphism of number fields is a bijection (its inverse is the
transport along the inverse isomorphism), and the conjugation across a level isomorphism is a group
isomorphism (its inverse is the conjugation across the inverse isomorphism). -/

/-- **The transport of primes along an isomorphism of number fields is a bijection**: transporting a
prime to the other side and back returns it. -/
lemma primeTransport_symm_transport {A B : Type*} [Field A] [NumberField A] [Field B]
    [NumberField B] (e : A ≃+* B) (Q : NK.Chebotarev.PrimeIdeal B) :
    NK.Reconstruct.primeTransport e (NK.Reconstruct.primeTransport e.symm Q) = Q := by
  let e' : 𝓞 A →+* 𝓞 B := NK.Reconstruct.ringOfIntegersEquiv e
  let e'' : 𝓞 B →+* 𝓞 A := NK.Reconstruct.ringOfIntegersEquiv e.symm
  have hcomp : e'.comp e'' = RingHom.id (𝓞 B) := by
    apply RingHom.ext
    intro y
    apply NumberField.RingOfIntegers.eq_iff.mp
    show ((NK.Reconstruct.ringOfIntegersEquiv e
      (NK.Reconstruct.ringOfIntegersEquiv e.symm y) : 𝓞 B) : B) = ((y : 𝓞 B) : B)
    rw [NK.Reconstruct.ringOfIntegersEquiv_apply, NK.Reconstruct.ringOfIntegersEquiv_apply,
      RingEquiv.apply_symm_apply]
  apply IsDedekindDomain.HeightOneSpectrum.ext
  show Ideal.map e' (Ideal.map e'' Q.asIdeal) = Q.asIdeal
  rw [Ideal.map_map, hcomp, Ideal.map_id]

/-- **The round trip of the conjugation across a level isomorphism.** -/
lemma conjAlgEquiv_symm_conjAlgEquiv {L₁ : IntermediateField K₁ K₁'}
    {L₂ : IntermediateField K₂ K₂'} (τ : ↥L₁ ≃+* ↥L₂) (h : NK.Reconstruct.MapsBaseLevel L₁ L₂ τ)
    (d : Gal(↥L₁/K₁)) :
    NK.Reconstruct.conjAlgEquiv τ.symm h.symm (NK.Reconstruct.conjAlgEquiv τ h d) = d := by
  ext x
  simp only [NK.Reconstruct.conjAlgEquiv_apply]
  simp

/-! ## The arithmetic action on transported primes

The transport of primes along a level isomorphism `τ : ↥L₁ ≃+* ↥L₂` is compatible with the Galois
action up to conjugation by `τ`. -/

/-- **The conjugate of a Galois automorphism acts on transported primes by transporting the action
of the automorphism.**

The arithmetic content is the elementwise identity `ringOfIntegersEquiv τ ∘ d = u ∘
ringOfIntegersEquiv τ` on the rings of integers (`d` and `u` being the restrictions of `d` and of
`u = conjAlgEquiv τ h d`), from which the identity of the ideals follows by functoriality of
`Ideal.map`; the two ideals `(conjAlgEquiv τ h d) • primeTransport τ P` and
`primeTransport τ (d • P)` are their `asIdeal`s. -/
lemma conjAlgEquiv_smul_primeTransport {L₁ : IntermediateField K₁ K₁'}
    {L₂ : IntermediateField K₂ K₂'} [FiniteDimensional K₁ ↥L₁] [NumberField ↥L₁]
    [FiniteDimensional K₂ ↥L₂] [NumberField ↥L₂] [IsGalois K₁ ↥L₁] [IsGalois K₂ ↥L₂]
    {τ : ↥L₁ ≃+* ↥L₂} (h : NK.Reconstruct.MapsBaseLevel L₁ L₂ τ) (d : Gal(↥L₁/K₁))
    (P : NK.Chebotarev.PrimeIdeal ↥L₁) :
    NK.Reconstruct.conjAlgEquiv τ h d • (NK.Reconstruct.primeTransport τ P) =
      NK.Reconstruct.primeTransport τ (d • P) := by
  let u : Gal(↥L₂/K₂) := NK.Reconstruct.conjAlgEquiv τ h d
  let τ' : 𝓞 ↥L₁ →+* 𝓞 ↥L₂ := NK.Reconstruct.ringOfIntegersEquiv τ
  let d' : 𝓞 ↥L₁ →+* 𝓞 ↥L₁ := galRestrict (𝓞 K₁) K₁ (↥L₁) (𝓞 ↥L₁) d
  let u' : 𝓞 ↥L₂ →+* 𝓞 ↥L₂ := galRestrict (𝓞 K₂) K₂ (↥L₂) (𝓞 ↥L₂) u
  have hd : d = NK.Reconstruct.conjAlgEquiv τ.symm h.symm u := by
    rw [show u = NK.Reconstruct.conjAlgEquiv τ h d from rfl, conjAlgEquiv_symm_conjAlgEquiv]
  have hcomp : u'.comp τ' = τ'.comp d' := by
    apply RingHom.ext
    intro x
    change galRestrict (𝓞 K₂) K₂ (↥L₂) (𝓞 ↥L₂) u
        (NK.Reconstruct.ringOfIntegersEquiv τ x) =
      NK.Reconstruct.ringOfIntegersEquiv τ
        (galRestrict (𝓞 K₁) K₁ (↥L₁) (𝓞 ↥L₁) d x)
    rw [hd]
    apply NumberField.RingOfIntegers.eq_iff.mp
    simp only [NK.Reconstruct.ringOfIntegersEquiv_apply, algebraMap_galRestrict_apply,
      NK.Reconstruct.conjAlgEquiv_apply, RingEquiv.symm_symm, RingEquiv.apply_symm_apply]
  have hid : Ideal.map u' (Ideal.map τ' P.asIdeal) = Ideal.map τ' (Ideal.map d' P.asIdeal) := by
    rw [Ideal.map_map, Ideal.map_map, hcomp]
  apply IsDedekindDomain.HeightOneSpectrum.ext
  show (u • NK.Reconstruct.primeTransport τ P).asIdeal =
    (NK.Reconstruct.primeTransport τ (d • P)).asIdeal
  rw [NK.Chebotarev.smul_primeIdeal_asIdeal,
    show (NK.Reconstruct.primeTransport τ P).asIdeal = Ideal.map τ' P.asIdeal from rfl,
    show (NK.Reconstruct.primeTransport τ (d • P)).asIdeal =
      Ideal.map τ' (d • P).asIdeal from rfl,
    NK.Chebotarev.smul_primeIdeal_asIdeal]
  exact hid

/-! ## The prime identification determines the correspondence of Galois groups -/

/-- **The finite-level prime identification pins down the correspondence of Galois groups.**

Let `L ⊆ K₁'` be a finite normal level with corresponding level `L₂ = levelMap ϕ L ⊆ K₂'`, and let
`τ : ↥L ≃+* ↥L₂` be a ring isomorphism compatible with the two base fields.  If the transport of
primes along `τ` is the prime correspondence `levelPrimeMap ϕ hϕ a L` induced by `ϕ` and the local
correspondence `a`, then conjugating `Gal(↥L/K₁)` by `τ` reproduces the restriction of `ϕ`:

`conjAlgEquiv τ h (restrictNormalHom L g) = restrictNormalHom (levelMap ϕ L) (ϕ g)` for every
`g : Gal(K₁'/K₁)`.

Proof: both sides are elements of `Gal(levelMap ϕ L/K₂)`.  Choose a prime `𝔭` of `K₂` splitting
completely in `levelMap ϕ L`; two elements of `Gal(levelMap ϕ L/K₂)` agreeing on all primes above
`𝔭` are equal.  Every prime `Q` of `levelMap ϕ L` is of the form `Q = primeTransport τ P` for some
prime `P` of `L`, and then
`conjAlgEquiv τ h (g|_L) • Q = primeTransport τ (g|_L • P) = levelPrimeMap (g|_L • P)`,
while the prime correspondence is `Gal`-equivariant:
`levelPrimeMap (g|_L • P) = (ϕ g) • levelPrimeMap P = (ϕ g) • Q`. -/
theorem conjAlgEquiv_eq_restrictNormalHom_of_primeTransport_eq
    (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (hϕ : IsHomeomorph ϕ)
    (a : NK.Reconstruct.LocalCorrespondence ϕ)
    (L : IntermediateField K₁ K₁') [FiniteDimensional K₁ L] [Normal K₁ L] [NumberField ↥L]
    [FiniteDimensional K₂ (NK.Reconstruct.levelMap ϕ L)]
    [Normal K₂ (NK.Reconstruct.levelMap ϕ L)] [NumberField ↥(NK.Reconstruct.levelMap ϕ L)]
    (τ : ↥L ≃+* ↥(NK.Reconstruct.levelMap ϕ L))
    (hτ : NK.Reconstruct.MapsBaseLevel L (NK.Reconstruct.levelMap ϕ L) τ)
    (hcorr : NK.Reconstruct.primeTransport τ =
      NK.ReconstructField.levelPrimeMap ϕ hϕ a L) :
    ∀ g : Gal(K₁'/K₁),
      NK.Reconstruct.conjAlgEquiv τ hτ (AlgEquiv.restrictNormalHom L g) =
        AlgEquiv.restrictNormalHom (NK.Reconstruct.levelMap ϕ L) (ϕ g) := by
  haveI : IsGalois K₁ ↥L := Commons.FieldTheory.Galois.isGalois_of_normal_of_charZero
  haveI : IsGalois K₂ ↥(NK.Reconstruct.levelMap ϕ L) :=
    Commons.FieldTheory.Galois.isGalois_of_normal_of_charZero
  intro g
  obtain ⟨𝔭, -, h𝔭⟩ :=
    NK.UchidaKummer.exists_splitsCompletely_notMem (K := K₂)
      (L := ↥(NK.Reconstruct.levelMap ϕ L)) (∅ : Finset (NK.Chebotarev.PrimeIdeal K₂))
  refine NK.UchidaKummer.eq_of_forall_smul_eq_of_splitsCompletely (K := K₂)
    (L := ↥(NK.Reconstruct.levelMap ϕ L)) h𝔭 ?_
  intro Q _
  set P : NK.Chebotarev.PrimeIdeal ↥L := NK.Reconstruct.primeTransport τ.symm Q with hP
  have hPQ : NK.Reconstruct.primeTransport τ P = Q := by
    rw [hP]
    exact primeTransport_symm_transport τ Q
  calc NK.Reconstruct.conjAlgEquiv τ hτ (AlgEquiv.restrictNormalHom L g) • Q
      = NK.Reconstruct.conjAlgEquiv τ hτ (AlgEquiv.restrictNormalHom L g) •
          (NK.Reconstruct.primeTransport τ P) := by rw [hPQ]
    _ = NK.Reconstruct.primeTransport τ ((AlgEquiv.restrictNormalHom L g) • P) :=
        conjAlgEquiv_smul_primeTransport hτ (AlgEquiv.restrictNormalHom L g) P
    _ = NK.ReconstructField.levelPrimeMap ϕ hϕ a L
          ((AlgEquiv.restrictNormalHom L g) • P) := by rw [hcorr]
    _ = AlgEquiv.restrictNormalHom (NK.Reconstruct.levelMap ϕ L) (ϕ g) •
          NK.ReconstructField.levelPrimeMap ϕ hϕ a L P :=
        NK.ReconstructField.levelPrimeMap_smul_of_lift ϕ hϕ a L g P
    _ = AlgEquiv.restrictNormalHom (NK.Reconstruct.levelMap ϕ L) (ϕ g) • Q := by
        rw [← hcorr, hPQ]

/-! ## The restriction of the conjugated isomorphism to the corresponding level -/

/-- **The restriction of `conjHomEquiv hσ` is the conjugation by the level isomorphism.**

Let `σ : K₂' ≃+* K₁'` be a base-field-mapping isomorphism of the separable closures whose
restriction to the level `L₂ ⊆ K₂'` is the inverse of the level isomorphism `τ : ↥L₁ ≃+* ↥L₂`
(`σ (x : K₂') = ((τ.symm x : ↥L₁) : K₁')`).  Then the restriction of the conjugated isomorphism
`conjHomEquiv hσ` to `L₂` is exactly the conjugation by `τ`. -/
theorem restrictNormalHom_conjHomEquiv_eq_conjAlgEquiv
    {L₁ : IntermediateField K₁ K₁'} {L₂ : IntermediateField K₂ K₂'}
    [FiniteDimensional K₂ ↥L₂] [Normal K₂ ↥L₂] [NumberField ↥L₂]
    [FiniteDimensional K₁ ↥L₁] [Normal K₁ ↥L₁] [NumberField ↥L₁]
    (σ : K₂' ≃+* K₁')
    (hσ : Submission.NeukirchUchida.MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂') σ)
    (τ : ↥L₁ ≃+* ↥L₂) (hτ : NK.Reconstruct.MapsBaseLevel L₁ L₂ τ)
    (hστ : ∀ x : ↥L₂, σ (x : K₂') = ((τ.symm x : ↥L₁) : K₁'))
    (g : Gal(K₁'/K₁)) :
    AlgEquiv.restrictNormalHom L₂ (Submission.NeukirchUchida.conjHomEquiv hσ g) =
      NK.Reconstruct.conjAlgEquiv τ hτ (AlgEquiv.restrictNormalHom L₁ g) := by
  have hsymm : ∀ y : ↥L₁, σ.symm ((y : ↥L₁) : K₁') = ((τ y : ↥L₂) : K₂') := by
    intro y
    refine (RingEquiv.symm_apply_eq σ).mpr ?_
    rw [hστ (τ y), RingEquiv.symm_apply_apply]
  ext x
  rw [AlgEquiv.restrictNormalHom_apply,
    show Submission.NeukirchUchida.conjHomEquiv hσ g = Submission.NeukirchUchida.conj hσ g
      from rfl,
    Submission.NeukirchUchida.conj_apply, NK.Reconstruct.conjAlgEquiv_apply, hστ x,
    ← AlgEquiv.restrictNormalHom_apply L₁ g (τ.symm x),
    hsymm (AlgEquiv.restrictNormalHom L₁ g (τ.symm x))]

end NK.ReconstructField.LevelMatchAux

namespace NK.ReconstructField

open NK.Reconstruct
open scoped Pointwise

theorem exists_sigma_levelMatch_of_levelPrimeIdentification {K₁ K₂ K₁' K₂' : Type*} [Field K₁]
    [Field K₂] [Field K₁'] [Field K₂'] [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁']
    [Algebra K₂ K₂'] [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']
    (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (hϕ : IsHomeomorph ϕ)
    (a : NK.Reconstruct.LocalCorrespondence ϕ) (τ₀ : K₁ ≃+* K₂)
    (hident : ∀ (L : IntermediateField K₁ K₁') [FiniteDimensional K₁ L] [Normal K₁ L]
      [NumberField ↥L] [FiniteDimensional K₂ (NK.Reconstruct.levelMap ϕ L)]
      [Normal K₂ (NK.Reconstruct.levelMap ϕ L)] [NumberField ↥(NK.Reconstruct.levelMap ϕ L)]
      [IsGalois ℚ ↥(NK.Reconstruct.levelMap ϕ L)],
      ∃ τ : ↥L ≃+* ↥(NK.Reconstruct.levelMap ϕ L),
        NK.Reconstruct.primeTransport τ =
            NK.ReconstructField.levelPrimeMap ϕ hϕ a L ∧
          (∀ x : K₁, τ (algebraMap K₁ ↥L x) =
            algebraMap K₂ ↥(NK.Reconstruct.levelMap ϕ L) (τ₀ x))) :
    ∀ (L : IntermediateField K₁ K₁') [FiniteDimensional K₁ L] [Normal K₁ L] [NumberField ↥L]
      [FiniteDimensional K₂ (NK.Reconstruct.levelMap ϕ L)]
      [Normal K₂ (NK.Reconstruct.levelMap ϕ L)] [NumberField ↥(NK.Reconstruct.levelMap ϕ L)]
      [IsGalois ℚ ↥(NK.Reconstruct.levelMap ϕ L)],
      ∃ (σ : K₂' ≃+* K₁')
        (hσ : Submission.NeukirchUchida.MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂') σ),
        (∀ x : K₁, σ (algebraMap K₂ K₂' (τ₀ x)) = algebraMap K₁ K₁' x) ∧
          NK.ReconstructField.LevelMatch ϕ hϕ σ hσ L := by
  intro L _ _ _ _ _ _ _
  -- the level isomorphism and its two properties
  obtain ⟨τ, hcorr, hbase⟩ := hident L
  -- it is compatible with the base fields
  have hτ : NK.Reconstruct.MapsBaseLevel L (NK.Reconstruct.levelMap ϕ L) τ := by
    constructor
    · intro x
      exact ⟨τ₀ x, hbase x⟩
    · intro b
      refine ⟨τ₀.symm b, (RingEquiv.symm_apply_eq τ).mpr ?_⟩
      rw [hbase (τ₀.symm b), RingEquiv.apply_symm_apply]
  -- extend it to an isomorphism of the separable closures
  obtain ⟨σ, hσ, hσL⟩ := NK.ReconstructField.exists_ringEquiv_mapsBase_of_mapsBaseLevel
    (K₁ := K₁) (K₂ := K₂) (K₁' := K₁') (K₂' := K₂') L (NK.Reconstruct.levelMap ϕ L) τ hτ
  refine ⟨σ, hσ, ?_, ?_⟩
  · -- the base fields are mapped according to `τ₀`
    intro x
    have hst : algebraMap K₂ K₂' (τ₀ x) =
        algebraMap ↥(NK.Reconstruct.levelMap ϕ L) K₂'
          (algebraMap K₂ ↥(NK.Reconstruct.levelMap ϕ L) (τ₀ x)) :=
      IsScalarTower.algebraMap_apply K₂ ↥(NK.Reconstruct.levelMap ϕ L) K₂' (τ₀ x)
    have hkey : τ.symm (algebraMap K₂ ↥(NK.Reconstruct.levelMap ϕ L) (τ₀ x)) =
        algebraMap K₁ ↥L x :=
      (RingEquiv.symm_apply_eq τ).mpr (hbase x).symm
    calc σ (algebraMap K₂ K₂' (τ₀ x))
        = σ (algebraMap ↥(NK.Reconstruct.levelMap ϕ L) K₂'
            (algebraMap K₂ ↥(NK.Reconstruct.levelMap ϕ L) (τ₀ x))) := by rw [hst]
      _ = ((τ.symm (algebraMap K₂ ↥(NK.Reconstruct.levelMap ϕ L) (τ₀ x)) : ↥L) : K₁') :=
          hσL _
      _ = ((algebraMap K₁ ↥L x : ↥L) : K₁') := by rw [hkey]
      _ = algebraMap K₁ K₁' x :=
          (IsScalarTower.algebraMap_apply K₁ ↥L K₁' x).symm
  · -- the level condition
    have hcore :=
      LevelMatchAux.conjAlgEquiv_eq_restrictNormalHom_of_primeTransport_eq ϕ hϕ a L τ hτ hcorr
    haveI : IsGalois K₂ ↥(NK.Reconstruct.levelMap ϕ L) :=
      Commons.FieldTheory.Galois.isGalois_of_normal_of_charZero
    intro g
    have h₁ : AlgEquiv.restrictNormalHom (NK.Reconstruct.levelMap ϕ L)
          (Submission.NeukirchUchida.conjHomEquiv hσ g) =
        AlgEquiv.restrictNormalHom (NK.Reconstruct.levelMap ϕ L) (ϕ g) := by
      rw [LevelMatchAux.restrictNormalHom_conjHomEquiv_eq_conjAlgEquiv (L₁ := L)
        (L₂ := NK.Reconstruct.levelMap ϕ L) σ hσ τ hτ hσL g, hcore g]
    rw [← IntermediateField.restrictNormalHom_ker (NK.Reconstruct.levelMap ϕ L),
      MonoidHom.mem_ker, map_mul, map_inv, h₁, mul_inv_cancel]

end NK.ReconstructField
