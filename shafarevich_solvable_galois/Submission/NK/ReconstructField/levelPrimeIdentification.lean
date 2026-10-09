import Mathlib
import Submission.NK.ReconstructField.MainWeakNU
import Submission.NK.ReconstructField.eq_of_isNormal_of_algEquiv
import Submission.NK.ReconstructField.localDegree_primeTransport
import Submission.NK.ReconstructField.primeOfLevel_placeMap_eq_of_comap_eq_gen
import Submission.NK.ReconstructField.ncard_primesOver_levelPrimeMapGen
import Submission.NK.ReconstructField.LevelPrimeBijective
import Submission.NK.ReconstructField.compactness_conjHomEquiv
import Submission.NK.UchidaKummer.Differentiation.isDifferentiable_of_kummerMachinery
import Submission.NK.UchidaKummer.Kummer.machinery_of_isPrimitiveRoot
import Submission.NK.ReconstructField.key_finite_prime_match
import Submission.NK.ReconstructField.primeTransport_eq_levelPrimeMap_imp_base
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The level-wise prime identification (Neukirch's Lemma, CoNF XII §12.2)

This file proves `NK.ReconstructField.levelPrimeIdentification`: from

* the level-wise weak Neukirch–Uchida input `LevelIsoInput ϕ hϕ` (every finite level `L ⊆ K₁'` is
  isomorphic to its image `levelMap ϕ L`),
* the compatibility `hbase` of the local correspondence `a` with the base-field isomorphism
  `τ₀ : K₁ ≃+* K₂` on the primes of `K₁`, and
* the Kummer-theoretic hypotheses `hℓ : ℓ.Prime`, `hμ : ∃ ζ : K₁, IsPrimitiveRoot ζ ℓ`

one obtains the level-wise prime identification `LevelPrimeIdentification ϕ hϕ a τ₀`: for every
finite normal level `L` whose image under `ϕ` is Galois over `ℚ` there is an isomorphism
`τ : ↥L ≃+* ↥(levelMap ϕ L)` whose induced map on primes is the correspondence
`levelPrimeMap ϕ hϕ a L` of `ϕ`, and which is compatible with `τ₀` on the embedded copy of `K₁`.

The two ingredients are delegated:

* `key_finite_prime_match` — the differentiation/pinning step: for *finitely many* prescribed
  primes `S` of `L` there is a level isomorphism whose prime map agrees with `levelPrimeMap` on
  `S`.  (Differentiation over the base field `↥L` via `μ_ℓ ⊆ K₁`, the weak theorem at the level
  `levelMap ϕ L`, the Perlis alignment of the image level, and the counting argument which
  distinguishes the primes by the number of their lifts.)
* `primeTransport_eq_levelPrimeMap_imp_base` — from the *global* prime map equality one gets the
  base-field compatibility with `τ₀` (via the rigidity of the place system and the uniqueness of a
  number-field isomorphism with prescribed action on primes).

The finiteness of the set of isomorphisms `↥L ≃+* ↥(levelMap ϕ L)` (both are number fields)
upgrades the finitary input to the global prime map equality by a finite-intersection argument.
-/

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace NK.ReconstructField

open NK.Reconstruct
open scoped Pointwise

/-- **There are only finitely many ring isomorphisms between two number fields.**  Both are
finite-dimensional over `ℚ`, and a ring isomorphism of fields of characteristic zero is an
`ℚ`-algebra homomorphism, so this follows from the finiteness of `ℚ`-algebra homomorphisms (an
`ℚ`-algebra homomorphism out of a finite-dimensional extension is determined by the image of a
primitive element, hence by a root of a fixed polynomial). -/
private theorem finite_ringEquiv_of_numberField {L L₂ : Type*} [Field L] [NumberField L] [Field L₂]
    [NumberField L₂] [Algebra ℚ L] [Algebra ℚ L₂] [FiniteDimensional ℚ L] :
    Finite (L ≃+* L₂) := by
  refine Finite.of_injective
    (fun e : L ≃+* L₂ => (AlgEquiv.ofRingEquiv (f := e) (fun q =>
      RingHom.congr_fun (RingHom.ext_rat (f := (e : L →+* L₂).comp (algebraMap ℚ L))
        (g := algebraMap ℚ L₂)) q) : L →ₐ[ℚ] L₂))
    ?_
  intro e f h
  ext x
  exact DFunLike.congr_fun h x

/-- **The global prime map equality at a finite level** from the level-wise weak theorem: by the
finiteness of the set of isomorphisms `↥L ≃+* ↥(levelMap ϕ L)` (a number field has finitely many
isomorphisms), the finitary pinning `key_finite_prime_match` upgrades to a single isomorphism whose
prime map is the whole correspondence `levelPrimeMap ϕ hϕ a L`. -/
private theorem exists_primeTransport_eq_levelPrimeMap
    {K₁ K₂ K₁' K₂' : Type*} [Field K₁] [Field K₂] [Field K₁'] [Field K₂']
    [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
    [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂'] {ℓ : ℕ}
    (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (hϕ : IsHomeomorph ϕ)
    (a : NK.Reconstruct.LocalCorrespondence ϕ)
    (hlev : NK.ReconstructField.LevelIsoInput ϕ hϕ) (hℓ : ℓ.Prime)
    (hμ : ∃ ζ : K₁, IsPrimitiveRoot ζ ℓ)
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
  -- the finite set of "witnesses": for every bad isomorphism, one prime at which it is bad
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

/-- **The level-wise prime identification (Neukirch's Lemma `alpha identifies with sigma on
primes`, level form).**

Let `ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)` be a homeomorphic isomorphism of absolute Galois groups,
`a` its local correspondence, `τ₀ : K₁ ≃+* K₂` a base-field isomorphism inducing the prime
correspondence of `a` (`hbase`), and assume the level-wise weak Neukirch–Uchida input `hlev` (every
finite level is isomorphic to its image) together with the Kummer hypotheses `hℓ`, `hμ`.  Then for
every finite normal level `L ⊆ K₁'` whose image `levelMap ϕ L` is Galois over `ℚ` there is an
isomorphism `τ : ↥L ≃+* ↥(levelMap ϕ L)` of the two levels whose induced prime map is the prime
correspondence `levelPrimeMap ϕ hϕ a L` and which is compatible with `τ₀` on `K₁`. -/
theorem levelPrimeIdentification {K₁ K₂ K₁' K₂' : Type*} [Field K₁] [Field K₂] [Field K₁'] [Field K₂']
    [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
    [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂'] {ℓ : ℕ}
    (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (hϕ : IsHomeomorph ϕ)
    (a : NK.Reconstruct.LocalCorrespondence ϕ) (τ₀ : K₁ ≃+* K₂)
    (hbase : ∀ 𝔭 : NK.Chebotarev.PrimeIdeal K₁,
      a.primeMap 𝔭 = NK.Reconstruct.primeTransport τ₀ 𝔭)
    (hlev : NK.ReconstructField.LevelIsoInput ϕ hϕ) (hℓ : ℓ.Prime)
    (hμ : ∃ ζ : K₁, IsPrimitiveRoot ζ ℓ) :
    NK.ReconstructField.LevelPrimeIdentification ϕ hϕ a τ₀ := by
  intro L _ _ _ _ _ _ _
  obtain ⟨τ, hτ⟩ := exists_primeTransport_eq_levelPrimeMap ϕ hϕ a hlev hℓ hμ L
  obtain ⟨-, hbasecompat⟩ :=
    primeTransport_eq_levelPrimeMap_imp_base ϕ hϕ a τ₀ hbase L τ hτ
  exact ⟨τ, hτ, hbasecompat⟩

end NK.ReconstructField
