import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.SSGRoute.E7aAux
import Submission.Work.SSGRoute.isUnit_natCast_of_not_dvd_resCharAt
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

namespace Work.SSGRoute

/-- **The missing infrastructure piece of the E7a place glue: the `Algebra` structure of `K_w`
over `k_v`.**  With `𝔭 := Work.SSGRoute.primeUnder k A hA` the prime of `k` below the finite place
`A` of `Ω` (so `Work.SSGRoute.localFieldAt k A hA = 𝔭.adicCompletion k = k_v`) and `q` a finite place
of `K` whose prime lies below `A` (`hAq` is exactly the correspondence `x ∈ q ↔ v_A(x) < 1` on
`𝒪_K`), the primeness data and the compatibility of `Commons`' `adicCompletionMap` with the
structural maps are:

* `q.asIdeal` lies over `𝔭.asIdeal`, so `Work.SSGRoute.adicCompletionMapAt k Ω K A hA q hLies` is
  available as a ring hom `k_v →+* K_w`;
* it is compatible with the two `algebraMap k`'s, i.e. it extends `algebraMap k` (this is exactly the
  `hcompat` hypothesis of `Work.SSGRoute.exists_localField_subfield`);
* it is injective (a field embedding).

`RingHom.toAlgebra` of that map is the `Algebra (k_v) (K_w)` instance which is *not* in the library
and which this lane currently carries as a hypothesis everywhere.  Producing the data here once lets
those statements drop the hypothesis and name `K_w` as a `k_v`-algebra.  (Reviewers confirmed the
statement is a repackaging of `Commons.RingTheory.Henselian.adicCompletionMap_apply` and
`algebraMap_adicCompletion`, so the proof is short; the only real step is `hLies`, verbatim the first
step of the existing proof of `exists_localField_subfield`.) -/
theorem exists_adicCompletion_algebra_compat (k : Type) (Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsSepClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] [NumberField K] (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hAq : ∀ x : NumberField.RingOfIntegers K, x ∈ q.asIdeal ↔ A.valuation (((x : K) : Ω)) < 1) :
    ∃ hLies : q.asIdeal.LiesOver (Work.SSGRoute.primeUnder k A hA).asIdeal,
      (∀ x : k, Work.SSGRoute.adicCompletionMapAt k Ω K A hA q hLies
            (algebraMap k (Work.SSGRoute.localFieldAt k A hA) x) =
          algebraMap k (q.adicCompletion K) x) ∧
      Function.Injective (Work.SSGRoute.adicCompletionMapAt k Ω K A hA q hLies) := by
  -- **(1) `q` lies over the prime of `k` cut out by `A`.**  This is `hAq` transported through the
  -- identification `valuation_lt_one_iff_mem_primeOf_of_numberField` of membership in `𝔭` with the
  -- inequality `A.valuation · < 1` on `𝓞 k`.
  have hlies : q.asIdeal.LiesOver (Work.SSGRoute.primeUnder k A hA).asIdeal := by
    refine Ideal.LiesOver.mk ?_
    ext x
    rw [Ideal.mem_comap, hAq,
      ← valuation_lt_one_iff_mem_primeOf_of_numberField k Ω A hA x]
    exact Iff.rfl
  refine ⟨hlies, ?_, ?_⟩
  · -- **(2) compatibility with the two structural maps.**  Both `algebraMap k k_v` and
    -- `algebraMap k K_w` are the coercion `x ↦ (x : ·)` (`algebraMap_adicCompletion`), so
    -- `Commons.RingTheory.Henselian.adicCompletionMap_apply` applies verbatim.
    intro x
    have hx : algebraMap k (Work.SSGRoute.localFieldAt k A hA) x
        = (x : (Work.SSGRoute.primeUnder k A hA).adicCompletion k) := by
      rw [IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion]; rfl
    rw [hx]
    rw [Commons.RingTheory.Henselian.adicCompletionMap_apply (K := k) (L := ↥K)
      (Work.SSGRoute.primeUnder k A hA) q hlies x]
    rw [IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion (K := ↥K) (v := q)]
    rfl
  · -- **(3) `k_v →+* K_w` is injective**, a ring homomorphism out of a field into a nontrivial ring.
    exact RingHom.injective _

end Work.SSGRoute
