import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.RingTheory.DedekindDomain.Factorization
import Submission.Work.SSGRoute.ZDataMup.ArtinReciprocity.IdealModulus.Defs
import Submission.Work.SSGRoute.ZDataMup.ZDataMupClean.UnramifiedBridge
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

open NumberField IsDedekindDomain
open scoped NumberField nonZeroDivisors

noncomputable section

namespace NK.CFTLib.ArtinReciprocityIdeal

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L]

/-- Only finitely many primes of `K` divide an ideal modulus `𝔪 ≠ ⊥`. -/
lemma finite_setOf_dvdPrime_clean (𝔪 : Ideal (𝓞 K)) (h𝔪 : 𝔪 ≠ ⊥) :
    {p : HeightOneSpectrum (𝓞 K) | DvdPrime 𝔪 p}.Finite := by
  refine (Ideal.finite_factors (I := 𝔪) h𝔪).subset ?_
  intro p hp
  simp only [Set.mem_ofPred_eq] at hp ⊢
  exact Ideal.dvd_iff_le.mpr hp

/-- **Surjectivity of the ideal Artin symbol on `I(𝔪)`.** -/
theorem surjId_clean (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsMulCommutative (L ≃ₐ[K] L)]
    (𝔪 : Ideal (NumberField.RingOfIntegers K)) (h𝔪 : 𝔪 ≠ ⊥)
    (hram : NK.CFTLib.ArtinReciprocityIdeal.ContainsRamified (K := K) (L := L) 𝔪) :
    ∀ σ : L ≃ₐ[K] L, ∃ A ∈ NK.CFTLib.ArtinReciprocityIdeal.idealCoprimeGroupId 𝔪,
      NK.CFTLib.Arl.artinSym (K := K) (L := L)
        (fun a b : L ≃ₐ[K] L => IsMulCommutative.is_comm.comm a b) A = σ := by
  classical
  have hcomm : ∀ a b : L ≃ₐ[K] L, a * b = b * a := fun a b => IsMulCommutative.is_comm.comm a b
  -- ## The finite set of primes dividing `𝔪`
  have hfin : {p : HeightOneSpectrum (𝓞 K) | DvdPrime 𝔪 p}.Finite :=
    finite_setOf_dvdPrime_clean (K := K) 𝔪 h𝔪
  let T : Finset (NK.Chebotarev.PrimeIdeal K) := hfin.toFinset
  have hTmem : ∀ p : NK.Chebotarev.PrimeIdeal K, p ∈ T ↔ DvdPrime 𝔪 p :=
    fun p => hfin.mem_toFinset
  -- ## The Artin symbol as a homomorphism on the group of fractional ideals
  let φ : Frac K →* (L ≃ₐ[K] L) :=
    { toFun := fun A => NK.CFTLib.Arl.artinSym hcomm (A : FractionalIdeal (𝓞 K)⁰ K)
      map_one' := by
        rw [Units.val_one]
        exact NK.CFTLib.Arl.artinSym_one hcomm
      map_mul' := fun A B => by
        rw [Units.val_mul]
        exact NK.CFTLib.Arl.artinSym_mul hcomm (frac_val_ne_zero A) (frac_val_ne_zero B) }
  -- ## Frobenius elements at the primes outside `T` generate the Galois group
  have hgen := NK.GlobalCFTdeep.SecondInequality.frobeniusGenerateTop_of_notMem
    (K := K) (L := L) T
  -- ... and each of them is the Artin symbol of a prime ideal not dividing `𝔪`
  have hSP : {σ : L ≃ₐ[K] L | ∃ p : NK.Chebotarev.PrimeIdeal K, p ∉ T ∧
      NK.Chebotarev.IsFrobAtPrime (K := K) (L := L) p σ}
      ⊆ ((idealCoprimeGroupId 𝔪).map φ : Set (L ≃ₐ[K] L)) := by
    rintro σ ⟨p, hpT, hfrob⟩
    have hpT' : ¬ DvdPrime 𝔪 p := fun h => hpT ((hTmem p).mpr h)
    have heq : Ideal.ramificationIdxIn p.asIdeal (𝓞 L) = 1 := by
      by_contra h
      exact hpT' (hram p h)
    have hunr : NK.CFTLib.ArtinReciprocityIdeal.IsUnramified (K := K) (L := L) p := by
      have h1 : NK.HeckeL.IsUnramifiedIn (K := K) (L := L) p :=
        Work.SSGRoute.ZDataMup.isUnramifiedIn_of_ramificationIdxIn_eq_one_clean (K := K) (L := L) p heq
      intro q hq
      exact h1 q hq
    refine ⟨idealUnit p.asIdeal p.ne_bot, Subgroup.subset_closure ⟨p, hpT', rfl⟩, ?_⟩
    show NK.CFTLib.Arl.artinSym hcomm
      (↑(idealUnit p.asIdeal p.ne_bot) : FractionalIdeal (𝓞 K)⁰ K) = σ
    rw [show (↑(idealUnit p.asIdeal p.ne_bot) : FractionalIdeal (𝓞 K)⁰ K) = ↑p.asIdeal from rfl,
      NK.CFTLib.Arl.artinSym_prime hcomm p]
    exact (NK.Chebotarev.isFrobAtPrime_iff_frobAtPrime_eq hcomm p hunr σ).mp hfrob
  intro σ
  have htop : (⊤ : Subgroup (L ≃ₐ[K] L)) ≤ (idealCoprimeGroupId 𝔪).map φ := by
    rw [← hgen]
    exact (Subgroup.closure_le _).mpr hSP
  obtain ⟨A, hA, hAσ⟩ := Subgroup.mem_map.mp (htop (Subgroup.mem_top σ))
  exact ⟨A, hA, hAσ⟩

end NK.CFTLib.ArtinReciprocityIdeal
