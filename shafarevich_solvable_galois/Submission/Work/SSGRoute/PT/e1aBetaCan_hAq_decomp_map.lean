import Mathlib
import Submission.Work.SSGRoute.PTDefs
import Submission.Work.SSGRoute.place_comap_valuationSubringAtPrime
import Submission.Work.SSGRoute.PT.e1aBetaCan_placeExists
import Submission.Work.SSGRoute.exists_mem_closure_decomp_mul_mem_fixingSubgroup
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.PT

/-- **The decomposition group of a finite place of `Ω` restricts onto the decomposition group of
the place of `K` below it.**

For a finite place `A` of `Ω` over `k` whose trace on the finite Galois extension `K/k` is the
prime `q` — expressed by the *lying-over* condition `hAq : x ∈ q ↔ v_A(x) < 1` on the ring of
integers of `K` — the image of the decomposition group `decomp k A ≤ G_k` under the restriction
`G_k →* Gal(K/k)` is exactly the stabiliser of the place `ofFinite q` of `K`:

  `(decomp k A).map (res k K) = decompK (ofFinite q)`.

The two inclusions are `Work.SSGRoute.decomp_map_le_stabilizer_of_comap_eq` and
`Work.SSGRoute.stabilizer_le_decomp_map_of_comap_eq`, both of which are stated with the
`comap`/`valuationSubringAtPrime` form of the lying-over condition; converting `hAq` into that
form is `Work.SSGRoute.place_comap_valuationSubringAtPrime`. -/
theorem e1aBetaCan_hAq_decomp_map (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] [NumberField K]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hAq : ∀ x : NumberField.RingOfIntegers K,
      x ∈ q.asIdeal ↔ A.valuation (((x : K) : Ω)) < 1) :
    (SSGRoute.decomp k A).map (SSGRoute.res k K) =
      SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q) := by
  have hAq' := Work.SSGRoute.place_comap_valuationSubringAtPrime k Ω K A hA q hAq
  apply le_antisymm
  · exact Work.SSGRoute.decomp_map_le_stabilizer_of_comap_eq k Ω K q A hA hAq'
  · exact Work.SSGRoute.stabilizer_le_decomp_map_of_comap_eq k Ω K q A hA hAq'

end Work.SSGRoute.PT
