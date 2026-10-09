import Mathlib
import Submission.Work.SSGRoute.ExtChain.ChainGamma
import Submission.Work.SSGRoute.valuation_lt_one_algebraMap_iff
import Submission.Commons.RingTheory.Valuation.exists_heightOneSpectrum_eq_valuationSubringAtPrime
import Submission.Commons.NumberTheory.NumberField.ringOfIntegers_le_of_ne_top
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.ExtChain

open IsDedekindDomain

/-- **The prime of `𝓞 K` below a finite place of `Ω` over `k`.**

Let `k` be a number field, `Ω` an algebraic closure of `k`, `K ⊆ Ω` a finite extension of `k`, and
`A` a finite place of `Ω` (a valuation subring of `Ω` whose trace on `k` is proper).  Then the
trace `B = A ∩ K` is a proper valuation subring of the number field `K`, hence the local ring of a
unique prime `q` of `𝓞 K`; the prime `q` is characterised by

`x ∈ q ⟺ A.valuation (x : Ω) < 1`  for all `x ∈ 𝓞 K`.

The construction is `exists_heightOneSpectrum_eq_valuationSubringAtPrime` applied to `B`, while the
characterisation of `q` is the composition of

* `IsLocalization.AtPrime.to_map_mem_maximal_iff` (the prime is the trace of the maximal ideal of
  the local ring `B`),
* `ValuationSubring.valuation_lt_one_iff` (`< 1` is the maximal ideal of a valuation subring),
* `Work.SSGRoute.valuation_lt_one_algebraMap_iff` (comparison of the `< 1` sets along a `comap`). -/
theorem exists_primeUnder_hAq
    {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K] [NumberField K]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A) :
    ∃ q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      ∀ x : NumberField.RingOfIntegers K,
        x ∈ q.asIdeal ↔ A.valuation (((x : K) : Ω)) < 1 := by
  -- The trace of `A` on `K` is proper: a nontrivial place of `k` stays nontrivial on `K ⊇ k`.
  have hBne : A.comap (algebraMap K Ω) ≠ ⊤ := by
    intro htop
    refine hA ?_
    have h1 : (A.comap (algebraMap K Ω)).comap (algebraMap k K) = A.comap (algebraMap k Ω) := by
      rw [ValuationSubring.comap_comap, IsScalarTower.algebraMap_eq k K Ω]
    rw [← h1, htop]
    ext z
    simp [ValuationSubring.mem_comap]
  -- `A ∩ K` is the local ring of a unique prime of `𝓞 K`.
  obtain ⟨q, hq⟩ :=
    Commons.RingTheory.Valuation.exists_heightOneSpectrum_eq_valuationSubringAtPrime
      (A.comap (algebraMap K Ω)) hBne
      (Commons.NumberTheory.NumberField.ringOfIntegers_le_of_ne_top _ hBne)
  refine ⟨q, fun x => ?_⟩
  -- `q` is the trace of the maximal ideal of the local ring `valuationSubringAtPrime K q`.
  haveI : IsLocalization.AtPrime
      (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K q) q.asIdeal :=
    inferInstanceAs (IsLocalization q.asIdeal.primeCompl _)
  have h1 : x ∈ q.asIdeal ↔
      (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K q).valuation
        (algebraMap (NumberField.RingOfIntegers K) K x) < 1 := by
    rw [← IsLocalization.AtPrime.to_map_mem_maximal_iff
      (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K q) q.asIdeal x]
    exact ValuationSubring.valuation_lt_one_iff _ _
  -- the local ring `valuationSubringAtPrime K q` is the trace of `A` on `K`
  have h2 : (A.comap (algebraMap K Ω)).valuation
        (algebraMap (NumberField.RingOfIntegers K) K x) < 1 ↔
      A.valuation (((x : K) : Ω)) < 1 := by
    rw [← Work.SSGRoute.valuation_lt_one_algebraMap_iff A (A.comap (algebraMap K Ω)) rfl]
    rfl
  rw [h1, ← hq]
  exact h2

end Work.SSGRoute.ExtChain
