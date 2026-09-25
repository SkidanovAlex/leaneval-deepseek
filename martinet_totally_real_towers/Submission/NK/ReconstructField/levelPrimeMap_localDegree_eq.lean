import Mathlib
import Submission.NK.ReconstructField.LevelPrimeBijective
import Submission.NK.ReconstructField.ncard_primesOver_levelMap
import Submission.NeukirchUchida.GaloisIso

namespace NK.ReconstructField

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

/-- **The finite-level prime correspondence preserves the local degree** `e·f`.

Let `L ⊆ K₁'` be a finite normal level which is a number field, `L₂ = levelMap ϕ L` the
corresponding level, `𝔭` a finite prime of `K₁` and `a` the local correspondence of `ϕ`.  Then the
local degree `e·f` of `𝔭` in `L/K₁` equals that of `a.primeMap 𝔭` in `L₂/K₂`.

Both extensions are Galois (char. `0`), so `e·f` is the common value of `e(P)·f(P)` over the
primes `P` above `𝔭`, and the fundamental identity
`#(primes over 𝔭) · (e·f) = [L : K₁]` holds.  The two sides are compared through the two facts
about the finite-level prime correspondence:

* the number of primes above `𝔭` in `L` equals the number above `a.primeMap 𝔭` in `L₂`
  (`NK.ReconstructField.ncard_primesOver_levelMap`);
* the degrees agree, `[L : K₁] = [L₂ : K₂]`, because the induced isomorphism of Galois groups
  `levelMapEquiv ϕ hϕ L` is an equivalence (`IsGalois.card_aut_eq_finrank`).

Cancelling the (nonzero) common factor `#(primes over 𝔭)` gives the claim. -/
theorem levelPrimeMap_localDegree_eq
    {K₁ K₂ K₁' K₂' : Type*} [Field K₁] [Field K₂] [Field K₁'] [Field K₂']
    [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
    [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']
    (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (hϕ : IsHomeomorph ϕ)
    (a : NK.Reconstruct.LocalCorrespondence ϕ)
    (L : IntermediateField K₁ K₁') [FiniteDimensional K₁ L] [Normal K₁ L] [NumberField ↥L]
    [FiniteDimensional K₂ (NK.Reconstruct.levelMap ϕ L)]
    [Normal K₂ (NK.Reconstruct.levelMap ϕ L)]
    [NumberField ↥(NK.Reconstruct.levelMap ϕ L)]
    (𝔭 : NK.Chebotarev.PrimeIdeal K₁) :
    𝔭.asIdeal.ramificationIdxIn (NumberField.RingOfIntegers ↥L) *
        𝔭.asIdeal.inertiaDegIn (NumberField.RingOfIntegers ↥L) =
      (a.primeMap 𝔭).asIdeal.ramificationIdxIn
          (NumberField.RingOfIntegers ↥(NK.Reconstruct.levelMap ϕ L)) *
        (a.primeMap 𝔭).asIdeal.inertiaDegIn
          (NumberField.RingOfIntegers ↥(NK.Reconstruct.levelMap ϕ L)) := by
  -- both levels define Galois extensions of the respective base fields
  haveI : IsGalois K₁ ↥L := Commons.FieldTheory.Galois.isGalois_of_normal_of_charZero
  haveI : IsGalois K₂ ↥(NK.Reconstruct.levelMap ϕ L) := NK.Reconstruct.isGalois_levelMap hϕ L
  -- the fundamental identity at the level `L`
  have hmul₁ : (𝔭.asIdeal.primesOver (NumberField.RingOfIntegers ↥L)).ncard *
      (𝔭.asIdeal.ramificationIdxIn (NumberField.RingOfIntegers ↥L) *
       𝔭.asIdeal.inertiaDegIn (NumberField.RingOfIntegers ↥L)) = Module.finrank K₁ ↥L := by
    letI : MulSemiringAction Gal(↥L/K₁) (NumberField.RingOfIntegers ↥L) :=
      IsIntegralClosure.MulSemiringAction (NumberField.RingOfIntegers K₁) K₁ ↥L
        (NumberField.RingOfIntegers ↥L)
    haveI : IsGaloisGroup Gal(↥L/K₁) (NumberField.RingOfIntegers K₁)
        (NumberField.RingOfIntegers ↥L) :=
      IsGaloisGroup.of_isFractionRing Gal(↥L/K₁) (NumberField.RingOfIntegers K₁)
        (NumberField.RingOfIntegers ↥L) K₁ ↥L
    haveI : Finite Gal(↥L/K₁) := inferInstance
    rw [Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn 𝔭.asIdeal
      (NumberField.RingOfIntegers ↥L) Gal(↥L/K₁)]
    exact IsGalois.card_aut_eq_finrank K₁ ↥L
  -- the fundamental identity at the corresponding level
  have hmul₂ : ((a.primeMap 𝔭).asIdeal.primesOver
        (NumberField.RingOfIntegers ↥(NK.Reconstruct.levelMap ϕ L))).ncard *
      ((a.primeMap 𝔭).asIdeal.ramificationIdxIn
          (NumberField.RingOfIntegers ↥(NK.Reconstruct.levelMap ϕ L)) *
       (a.primeMap 𝔭).asIdeal.inertiaDegIn
          (NumberField.RingOfIntegers ↥(NK.Reconstruct.levelMap ϕ L))) =
      Module.finrank K₂ ↥(NK.Reconstruct.levelMap ϕ L) := by
    letI : MulSemiringAction Gal(↥(NK.Reconstruct.levelMap ϕ L)/K₂)
        (NumberField.RingOfIntegers ↥(NK.Reconstruct.levelMap ϕ L)) :=
      IsIntegralClosure.MulSemiringAction (NumberField.RingOfIntegers K₂) K₂
        ↥(NK.Reconstruct.levelMap ϕ L)
        (NumberField.RingOfIntegers ↥(NK.Reconstruct.levelMap ϕ L))
    haveI : IsGaloisGroup Gal(↥(NK.Reconstruct.levelMap ϕ L)/K₂)
        (NumberField.RingOfIntegers K₂)
        (NumberField.RingOfIntegers ↥(NK.Reconstruct.levelMap ϕ L)) :=
      IsGaloisGroup.of_isFractionRing Gal(↥(NK.Reconstruct.levelMap ϕ L)/K₂)
        (NumberField.RingOfIntegers K₂)
        (NumberField.RingOfIntegers ↥(NK.Reconstruct.levelMap ϕ L)) K₂
        ↥(NK.Reconstruct.levelMap ϕ L)
    haveI : Finite Gal(↥(NK.Reconstruct.levelMap ϕ L)/K₂) := inferInstance
    rw [Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn (a.primeMap 𝔭).asIdeal
      (NumberField.RingOfIntegers ↥(NK.Reconstruct.levelMap ϕ L))
      Gal(↥(NK.Reconstruct.levelMap ϕ L)/K₂)]
    exact IsGalois.card_aut_eq_finrank K₂ ↥(NK.Reconstruct.levelMap ϕ L)
  -- the two numbers of primes over the corresponding primes agree
  have hcard := NK.ReconstructField.ncard_primesOver_levelMap hϕ a L 𝔭
  -- the two degrees agree
  have hfin : Module.finrank K₁ ↥L = Module.finrank K₂ ↥(NK.Reconstruct.levelMap ϕ L) := by
    rw [← IsGalois.card_aut_eq_finrank K₁ ↥L,
      ← IsGalois.card_aut_eq_finrank K₂ ↥(NK.Reconstruct.levelMap ϕ L)]
    exact Nat.card_congr (NK.Reconstruct.levelMapEquiv hϕ L).toEquiv
  -- there is at least one prime above `𝔭`, so the common factor is positive
  obtain ⟨P, hP⟩ := NK.Chebotarev.exists_primeIdeal_liesOver (K := K₁) (L := ↥L) 𝔭
  have hnpos : 0 < (𝔭.asIdeal.primesOver (NumberField.RingOfIntegers ↥L)).ncard := by
    rw [Set.ncard_pos]
    exact ⟨P.asIdeal, P.isPrime, hP⟩
  -- the two fundamental identities agree
  have heq : (𝔭.asIdeal.primesOver (NumberField.RingOfIntegers ↥L)).ncard *
      (𝔭.asIdeal.ramificationIdxIn (NumberField.RingOfIntegers ↥L) *
       𝔭.asIdeal.inertiaDegIn (NumberField.RingOfIntegers ↥L)) =
    (𝔭.asIdeal.primesOver (NumberField.RingOfIntegers ↥L)).ncard *
      ((a.primeMap 𝔭).asIdeal.ramificationIdxIn
          (NumberField.RingOfIntegers ↥(NK.Reconstruct.levelMap ϕ L)) *
       (a.primeMap 𝔭).asIdeal.inertiaDegIn
          (NumberField.RingOfIntegers ↥(NK.Reconstruct.levelMap ϕ L))) := by
    rw [hmul₁, hfin, ← hmul₂, ← hcard]
  exact Nat.mul_left_cancel hnpos heq

end NK.ReconstructField
