import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.SSGRoute.frobeniusClass_realisation_below
import Submission.Work.SSGRoute.glue_fin_decomp_ex
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The place of `Ω` over a finite place of `K`, with its lying-over condition

The local dictionary of the landing clause (`PT/e1aBetaCan_localDictionary_fin_inj`) is
parametrised by a finite place `A` of `Ω` and the *lying-over condition*
`hAq : ∀ x : O_K, x ∈ q.asIdeal ↔ A.valuation ((x:K):Ω) < 1` with respect to the place `q` of `K`
under `A` (the same interface as node E7a, `local_ext_h1_bridge`).  For the assembly of
`e1aBetaCan_le_ker` one has to *produce* such an `A` from a given `q`; this file does that, by
repackaging `exists_isFinPlace_comap_eq` (the trace of `A` on `K` is `O_{K,q}`) through the two
standard bridges between `valuation < 1` and the prime ideal / the maximal ideal:

* `Work.SSGRoute.comap_valuation_lt_one_iff`
* `Work.SSGRoute.valuationSubringAtPrime_valuation_lt_one_iff_mem`.
-/

namespace Work.SSGRoute

/-- **Every finite place `q` of `K` is the trace of a finite place `A` of `Ω`, with the
lying-over condition in the `valuation < 1` form.** -/
theorem exists_isFinPlace_hAq (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [NumberField K] (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    ∃ A : ValuationSubring Ω, SSGRoute.IsFinPlace k A ∧
      ∀ x : NumberField.RingOfIntegers K,
        x ∈ q.asIdeal ↔ A.valuation (((x : K) : Ω)) < 1 := by
  obtain ⟨A, hcomap, hfin⟩ := exists_isFinPlace_comap_eq (k := k) (Ω := Ω) K q
  refine ⟨A, hfin, fun x => ?_⟩
  change x ∈ q.asIdeal ↔ A.valuation
    (algebraMap ↥K Ω (algebraMap (NumberField.RingOfIntegers ↥K) ↥K x)) < 1
  rw [← SSGRoute.comap_valuation_lt_one_iff (K := ↥K) (L := Ω) A
      (algebraMap (NumberField.RingOfIntegers ↥K) ↥K x),
    hcomap, Work.SSGRoute.FrobBelow.valuationSubringAtPrime_valuation_lt_one_iff_mem q x]

end Work.SSGRoute
