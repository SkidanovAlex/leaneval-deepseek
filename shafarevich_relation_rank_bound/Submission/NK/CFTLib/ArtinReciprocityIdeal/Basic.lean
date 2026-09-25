import Mathlib
import Submission.NK.Chebotarev.LFunctions
import Submission.NK.Chebotarev.IsFrobAtRestrictNormalHom

/-!
# The Artin symbol of an ideal: the elementary part

This module sets up the elementary (reciprocity-free) part of the ideal-theoretic Artin map for a
finite abelian extension `L / K` of number fields:

* `NK.CFTLib.frobAtPrime_prod_irrel` — the product of the `σ p ^ e p` over a prescribed
  factorisation of a principal ideal does not depend on the choice of the Frobenius elements
  (`NK.Chebotarev.frobAtPrime` is the chosen one), as long as the primes are unramified.  This is
  what reduces the target theorem `NK.CFTLib.ArtinReciprocityIdeal` to a statement about
  `NK.Chebotarev.frobAtPrime`.
* `NK.CFTLib.exists_isFrobAtPrime_restrict` — consistency: the restriction of the Frobenius at
  `p` in `L/K` to an intermediate finite normal subextension is the Frobenius at `p` thereof.  This
  is what reduces the abelian case of the target to the cyclic one.
-/

namespace NK.CFTLib

open NK.Chebotarev

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

/-- **The product of Frobenius elements over a factorisation is independent of the choices**, for
primes which are unramified in the (abelian) extension. -/
theorem frobAtPrime_prod_irrel (hcomm : ∀ a b : Gal(L/K), a * b = b * a)
    (s : Finset (PrimeIdeal K)) (e : PrimeIdeal K → ℕ)
    (σ : PrimeIdeal K → Gal(L/K))
    (hunr : ∀ p ∈ s, ∀ P : PrimeIdeal L, P.asIdeal.LiesOver p.asIdeal →
      P.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) = 1)
    (hσ : ∀ p ∈ s, IsFrobAtPrime (K := K) (L := L) p (σ p)) :
    (s.toList.map (fun p => σ p ^ e p)).prod
      = (s.toList.map (fun p => (frobAtPrime (K := K) (L := L) p) ^ e p)).prod := by
  have h' : ∀ p ∈ s, σ p = frobAtPrime (K := K) (L := L) p := by
    intro p hp
    exact (isFrobAtPrime_iff_frobAtPrime_eq (K := K) (L := L) hcomm p (hunr p hp) (σ p)).mp
      (hσ p hp) |>.symm
  have h2 : ∀ p ∈ s.toList, (fun p => σ p ^ e p) p
      = (fun p => (frobAtPrime (K := K) (L := L) p) ^ e p) p := by
    intro p hp
    simp only
    rw [h' p (Finset.mem_toList.mp hp)]
  rw [List.map_congr_left h2]

/-- **Consistency of the Artin symbol**: for a tower `K ⊆ M ⊆ L` with `M/K` finite normal and
`L/K` finite Galois, the restriction of a Frobenius element at `p` in `L/K` to `M` is a Frobenius
element at `p` in `M/K`. -/
theorem exists_isFrobAtPrime_restrict (M : IntermediateField K L) [FiniteDimensional K M]
    [NumberField ↥M] [Normal K M]
    {p : PrimeIdeal K} {σ : Gal(L/K)} (hσ : IsFrobAtPrime (K := K) (L := L) p σ) :
    IsFrobAtPrime (K := K) (L := ↥M) p (AlgEquiv.restrictNormalHom (F := K) (K₁ := L) M σ) := by
  obtain ⟨P, hP, hPσ⟩ := hσ
  refine ⟨P.under (NumberField.RingOfIntegers ↥M), ?_, ?_⟩
  · refine ⟨?_⟩
    rw [IsDedekindDomain.HeightOneSpectrum.under_asIdeal, Ideal.under_under]
    exact hP.over
  · exact NK.Chebotarev.IsFrobAtRestrictNormalHom (K := K) (M := L) M hP hPσ

end NK.CFTLib
