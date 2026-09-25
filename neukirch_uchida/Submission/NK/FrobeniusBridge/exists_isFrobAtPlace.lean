import Mathlib
import Submission.NK.FrobeniusBridge.Descent
import Submission.NK.FrobeniusBridge.Basic

/-!
# Existence of a Frobenius element at a place

The infinite-level Frobenius predicate `NK.FrobeniusBridge.IsFrobAtPlace A g` says that the
restriction of `g : Gal(K'/K)` to *every* finite normal intermediate field `L ⊆ K'` is an
arithmetic Frobenius element at the prime of `𝓞 L` lying below the place `A`.

This file proves that such an element always exists, by the standard compactness argument on the
projective system of finite normal levels: at each level `L` the set of elements restricting to a
Frobenius element at the level is nonempty (a Frobenius element at the prime of `𝓞 L` exists by
`NK.Chebotarev.exists_isFrobAt` and lifts to `Gal(K'/K)` by surjectivity of the restriction map),
closed in the Krull topology (it is the preimage of a subset of the finite group `Gal(L/K)`), and
the family is directed because a Frobenius element at a prime of `𝓞 M` restricts to a Frobenius
element at the prime below it (`NK.FrobeniusBridge.frobAtLevel_restrict`, whose input is the
compatibility of the primes below `A` along the level system,
`NK.FrobeniusBridge.primeOfLevel_under`).
-/

namespace NK.FrobeniusBridge

open scoped Classical Pointwise

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

universe u

variable {K K' : Type*} [Field K] [NumberField K] [Field K'] [Algebra K K'] [IsSepClosure K K']

/-- **A Frobenius element at a single finite normal level exists.**  For a finite normal
intermediate field `L ⊆ K'` (a number field) and a place `A` of `K'` over a finite prime of `K`,
there is `g : Gal(K'/K)` whose restriction to `L` is an arithmetic Frobenius element at the prime
of `𝓞 L` below `A`. -/
theorem exists_frobAtLevel (A : FinitePlaceOf K K') (L : IntermediateField K K')
    [FiniteDimensional K L] [Normal K L] [NumberField ↥L] :
    ∃ g : Gal(K'/K), frobAtLevel A L g := by
  classical
  haveI hgal : IsGalois K ↥L := Commons.FieldTheory.Galois.isGalois_of_normal_of_charZero
  -- The prime of `𝓞 L` below the place `A`, and the prime of `𝓞 K` below it.
  let P : NK.Chebotarev.PrimeIdeal ↥L :=
    NK.Reconstruct.primeOfLevel A.1 L (NK.Reconstruct.comap_level_ne_top A.2 L)
  let p : NK.Chebotarev.PrimeIdeal K :=
    ⟨P.asIdeal.under (NumberField.RingOfIntegers K), inferInstance,
      Ideal.under_ne_bot (NumberField.RingOfIntegers K) P.ne_bot⟩
  have hp : P.asIdeal.LiesOver p.asIdeal := ⟨rfl⟩
  -- a Frobenius element at `P`, lifted to `Gal(K'/K)`
  obtain ⟨ρ, hρ⟩ := NK.Chebotarev.exists_isFrobAt (K := K) (L := ↥L) p P hp
  obtain ⟨σ, hσ⟩ := AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := ↥L) (E := K') ρ
  refine ⟨σ, ?_⟩
  rw [frobAtLevel_def, hσ]
  exact hρ

/-- **The level-wise Frobenius condition is a closed condition in the Krull topology.**  It is the
preimage under the restriction map `Gal(K'/K) →* Gal(L/K)` to the finite (discrete) group
`Gal(L/K)` of the set of Frobenius elements at the prime of `𝓞 L` below `A`. -/
theorem isClosed_frobAtLevel (A : FinitePlaceOf K K') (L : IntermediateField K K')
    [FiniteDimensional K L] [Normal K L] [NumberField ↥L] :
    IsClosed {g : Gal(K'/K) | frobAtLevel A L g} := by
  have hEq : {g : Gal(K'/K) | frobAtLevel A L g} =
      (AlgEquiv.restrictNormalHom (F := K) (K₁ := K') L) ⁻¹'
      {ρ : Gal(↥L/K) | NK.Chebotarev.IsFrobAt
        (NK.Reconstruct.primeOfLevel A.1 L (NK.Reconstruct.comap_level_ne_top A.2 L)) ρ} := by
    ext g
    simp only [Set.mem_preimage, Set.mem_ofPred_eq]
    exact frobAtLevel_def A L g
  rw [hEq]
  exact IsClosed.preimage (InfiniteGalois.restrictNormalHom_continuous L) (isClosed_discrete _)

/-- **Every place of a separable closure has a Frobenius element**: there is `g : Gal(K'/K)`
whose restriction to every finite normal level is an arithmetic Frobenius element at the prime
below the place.

The proof is the compactness argument on the projective system of finite normal levels: the sets
of elements that are Frobenius elements at the level `L` are nonempty, closed, and directed. -/
theorem exists_isFrobAtPlace {K K' : Type*} [Field K] [NumberField K]
    [Field K'] [Algebra K K'] [IsSepClosure K K']
    (A : NK.FrobeniusBridge.FinitePlaceOf K K') :
    ∃ g : Gal(K'/K), NK.FrobeniusBridge.IsFrobAtPlace A g := by
  classical
  -- The index set: the finite normal intermediate fields which are number fields.
  let ι := {L : IntermediateField K K' // FiniteDimensional K L ∧ Normal K L ∧ NumberField ↥L}
  haveI hneι : Nonempty ι := ⟨⟨⊥, inferInstance, inferInstance, inferInstance⟩⟩
  -- The level-wise Frobenius condition.
  let t : ι → Set Gal(K'/K) := fun L => by
    haveI h1 : FiniteDimensional K L.1 := L.2.1
    haveI h2 : Normal K L.1 := L.2.2.1
    haveI h3 : NumberField ↥L.1 := L.2.2.2
    exact {g | frobAtLevel A L.1 g}
  -- Each level condition is satisfied.
  have hne : ∀ L : ι, (t L).Nonempty := by
    intro L
    haveI h1 : FiniteDimensional K L.1 := L.2.1
    haveI h2 : Normal K L.1 := L.2.2.1
    haveI h3 : NumberField ↥L.1 := L.2.2.2
    exact exists_frobAtLevel A L.1
  -- The family is directed: the condition at the compositum implies the conditions at the factors,
  -- because a Frobenius element restricts to a Frobenius element at the prime below.
  have hdir : Directed (· ⊇ ·) t := by
    intro L₁ L₂
    haveI h1a : FiniteDimensional K L₁.1 := L₁.2.1
    haveI h1b : Normal K L₁.1 := L₁.2.2.1
    haveI h1c : NumberField ↥L₁.1 := L₁.2.2.2
    haveI h2a : FiniteDimensional K L₂.1 := L₂.2.1
    haveI h2b : Normal K L₂.1 := L₂.2.2.1
    haveI h2c : NumberField ↥L₂.1 := L₂.2.2.2
    let M : IntermediateField K K' := L₁.1 ⊔ L₂.1
    haveI hMa : FiniteDimensional K M := inferInstance
    haveI hMb : Normal K M := inferInstance
    haveI hMc : NumberField ↥M :=
      Commons.NumberTheory.NumberField.numberField_of_intermediateField (K := K) (K' := K') M
    refine ⟨⟨M, hMa, hMb, hMc⟩, ?_, ?_⟩
    · intro g hg
      letI : Algebra ↥L₁.1 ↥M :=
        (Subsemiring.inclusion (show L₁.1 ≤ M from le_sup_left)).toAlgebra
      haveI : IsScalarTower K ↥L₁.1 ↥M := IsScalarTower.of_algebraMap_eq fun x => rfl
      haveI : IsScalarTower ↥L₁.1 ↥M K' := IsScalarTower.of_algebraMap_eq fun x => rfl
      exact frobAtLevel_restrict (show L₁.1 ≤ M from le_sup_left) A hg
    · intro g hg
      letI : Algebra ↥L₂.1 ↥M :=
        (Subsemiring.inclusion (show L₂.1 ≤ M from le_sup_right)).toAlgebra
      haveI : IsScalarTower K ↥L₂.1 ↥M := IsScalarTower.of_algebraMap_eq fun x => rfl
      haveI : IsScalarTower ↥L₂.1 ↥M K' := IsScalarTower.of_algebraMap_eq fun x => rfl
      exact frobAtLevel_restrict (show L₂.1 ≤ M from le_sup_right) A hg
  -- Each level condition is closed.
  have hcl : ∀ L : ι, IsClosed (t L) := by
    intro L
    haveI h1 : FiniteDimensional K L.1 := L.2.1
    haveI h2 : Normal K L.1 := L.2.2.1
    haveI h3 : NumberField ↥L.1 := L.2.2.2
    exact isClosed_frobAtLevel A L.1
  -- Compactness of the Krull topology: the intersection of the family is nonempty.
  obtain ⟨σ, hσ⟩ :=
    IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed t hdir hne
      (fun L => (hcl L).isCompact) hcl
  refine ⟨σ, ?_⟩
  intro L hfin hnorm hnf
  exact Set.mem_iInter.mp hσ ⟨L, hfin, hnorm, hnf⟩

end NK.FrobeniusBridge
