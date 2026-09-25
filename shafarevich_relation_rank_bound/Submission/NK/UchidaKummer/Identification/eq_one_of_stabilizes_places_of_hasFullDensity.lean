import Mathlib
import Submission.NK.UchidaKummer.Defs
import Submission.NK.UchidaKummer.SplitPrimes
import Submission.NK.Reconstruct.stabilizer_le_fixingSubgroup_iff_splitCompletely
import Submission.NK.Reconstruct.eq_of_restrictNormalHom_eq
import Submission.NeukirchUchida.PrimeCorrespondence
import Submission.Commons.RingTheory.Valuation.mem_stabilizer_valuationSubring_iff

/-!
# A Galois automorphism stabilising the places over a full-density set of primes is trivial

Let `K` be a number field with separable closure `K'` and let `R` be a set of finite primes of `K`
of full Dirichlet density.  If `k ∈ Gal(K'/K)` stabilises every place `A` of `K'` whose prime below
lies in `R`, then `k = 1`.

The proof is the standard combination of Čebotarev and the freeness of the action of the Galois
group above a completely split prime:

* if `k ≠ 1`, then `k` acts non-trivially on some finite Galois intermediate field `L ⊆ K'`;
* by `exists_splitsCompletely_mem_of_hasFullDensity` there is a prime `p ∈ R` splitting completely
  in `L`;
* `k` stabilises a place `B` of `K'` above `p` by hypothesis, so its restriction to `L` stabilises
  the induced place of `L` above `p`; since `p` splits completely, the decomposition group of that
  place is trivial, so the restriction of `k` to `L` is trivial — contradiction.
-/

namespace NK.UchidaKummer.Identification

open scoped Pointwise

theorem eq_one_of_stabilizes_places_of_hasFullDensity
    {K K' : Type*} [Field K] [NumberField K] [Field K'] [Algebra K K'] [IsSepClosure K K']
    {R : Set (NK.Chebotarev.PrimeIdeal K)} (hR : NK.UchidaKummer.HasFullDensity K R)
    (k : Gal(K'/K))
    (h : ∀ A : {A : ValuationSubring K' // A.comap (algebraMap K K') ≠ ⊤},
      Submission.NeukirchUchida.primeOf A.1 A.2 ∈ R → ∀ x : K', (x ∈ A.1 ↔ k x ∈ A.1)) :
    k = 1 := by
  classical
  refine NK.Reconstruct.eq_of_restrictNormalHom_eq (u := k) (v := 1) ?_
  intro L hLfin hLnorm hLnum
  -- A prime `p ∈ R` which splits completely in the finite Galois level `L`.
  obtain ⟨p, -, hpR, hsplit⟩ :=
    NK.UchidaKummer.exists_splitsCompletely_mem_of_hasFullDensity (K := K) (L := ↥L) hR ∅
  -- A place of `K'` above `p`.
  set B : ValuationSubring K' :=
    (Submission.NeukirchUchida.placeOver (K₁ := K) (K₁' := K') p).1 with hBdef
  have hB : B.comap (algebraMap K K') =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K p :=
    Submission.NeukirchUchida.placeOver_spec (K₁ := K) (K₁' := K') p
  have hBne : B.comap (algebraMap K K') ≠ ⊤ := by
    rw [hB]
    exact Commons.RingTheory.Valuation.valuationSubringAtPrime_ne_top p
  have hp_eq : Submission.NeukirchUchida.primeOf B hBne = p :=
    Commons.RingTheory.Valuation.valuationSubringAtPrime_injective (K := K)
      (by rw [← Submission.NeukirchUchida.primeOf_spec B hBne, hB])
  -- `k` stabilises `B`, by hypothesis.
  have hkstab : k ∈ MulAction.stabilizer Gal(K'/K) B :=
    (Commons.RingTheory.Valuation.mem_stabilizer_valuationSubring_iff B k).mpr
      (h ⟨B, hBne⟩ (by rw [hp_eq]; exact hpR))
  -- Since `p` splits completely in `L`, the stabiliser of `B` is contained in the fixing
  -- subgroup of `L`.
  have hle : MulAction.stabilizer Gal(K'/K) B ≤ L.fixingSubgroup :=
    (NK.Reconstruct.stabilizer_le_fixingSubgroup_iff_splitCompletely
      (K := K) (K' := K') (N := L) p B hB).mpr hsplit
  have hker : k ∈ (AlgEquiv.restrictNormalHom (F := K) (K₁ := K') L).ker := by
    rw [IntermediateField.restrictNormalHom_ker]
    exact hle hkstab
  simpa using MonoidHom.mem_ker.mp hker

end NK.UchidaKummer.Identification
