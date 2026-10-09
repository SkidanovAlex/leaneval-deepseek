import Mathlib
import Submission.NK.GlobalCFTdeep.Transport.PlaceDefs
import Submission.NK.GlobalCFTdeep.Transport.liesOver_placeEquiv
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.GlobalCFTdeep.Transport

/-- Auxiliary: the `finitePlaceEquiv`-image of the set of primes over `Q` is the set of primes
over the transported prime.  Membership is characterised by the "lies over" relation. -/
theorem mem_primesOverFinite_map_finitePlaceEquiv
    {K L K' L' : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [Field K'] [NumberField K'] [Field L'] [NumberField L'] [Algebra K' L']
    (eK : K ≃+* K') (eL : L ≃+* L')
    (hcomp : ∀ x : K, eL (algebraMap K L x) = algebraMap K' L' (eK x))
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L')) :
    q ∈ (NK.GlobalCFT.Place.primesOverFinite (K := K) (L := L) Q).map
          (finitePlaceEquiv eL).toEmbedding ↔
      q ∈ NK.GlobalCFT.Place.primesOverFinite (K := K') (L := L')
            (finitePlaceEquiv eK Q) := by
  classical
  rw [Finset.mem_map_equiv, NK.GlobalCFT.Place.mem_primesOverFinite,
    NK.GlobalCFT.Place.mem_primesOverFinite,
    finitePlaceEquiv_liesOver_iff eK eL hcomp]
  simp

theorem primesOverFinite_map_placeEquiv
    {K L K' L' : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [Field K'] [NumberField K'] [Field L'] [NumberField L'] [Algebra K' L']
    (eK : K ≃+* K') (eL : L ≃+* L')
    (hcomp : ∀ x : K, eL (algebraMap K L x) = algebraMap K' L' (eK x))
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    (NK.GlobalCFT.Place.primesOverFinite (K := K) (L := L) Q).map
        (NK.GlobalCFTdeep.Transport.finitePlaceEquiv eL).toEmbedding =
      NK.GlobalCFT.Place.primesOverFinite (K := K') (L := L')
        (NK.GlobalCFTdeep.Transport.finitePlaceEquiv eK Q) := by
  classical
  ext q
  exact mem_primesOverFinite_map_finitePlaceEquiv eK eL hcomp Q q

end NK.GlobalCFTdeep.Transport
