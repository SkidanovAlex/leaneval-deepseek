import Mathlib
import Submission.Work.SSGRoute.E7aAux
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.isUnit_natCast_of_not_dvd_resCharAt
import Submission.Work.SSGRoute.LiftImports
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

/-- **The place of a finite intermediate field cut out by a place of the algebraic closure.**

Let `k` be a number field with algebraic closure `Ω`, `K/k` a finite Galois intermediate field, and
`A` a valuation subring of `Ω` whose restriction to `k` is a *finite* place.  Write `B` for the
restriction of `A` to `K`.  Then `B` is the valuation ring `𝒪_{K,q}` of the prime `q` of `𝓞[K]`
whose elements are exactly those `x` with `A.valuation x < 1`.

The proof: `B` is a proper valuation subring of the number field `K` containing `𝓞[K]`, so
`exists_heightOneSpectrum_eq_valuationSubringAtPrime` produces a prime `p` with
`B = 𝒪_{K,p}`; the defining inequality `hAq` identifies the maximal ideal of `B` cut out on `𝓞[K]`
with `q`, so `p = q`. -/
theorem place_comap_valuationSubringAtPrime (k Ω : Type) [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] [NumberField K] (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hAq : ∀ x : NumberField.RingOfIntegers K, x ∈ q.asIdeal ↔ A.valuation (((x : K) : Ω)) < 1) :
    A.comap (algebraMap K Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K q := by
  -- The restriction `B = A.comap (algebraMap ↥K Ω)` of `A` to the number field `K`.
  set B : ValuationSubring ↥K := A.comap (algebraMap ↥K Ω) with hBdef
  -- `B` is proper: `B = ⊤` would put all of `k` inside `A`, contradicting `IsFinPlace`.
  have hB : B ≠ ⊤ := by
    intro htop
    apply hA
    refine top_unique ?_
    intro c _
    rw [ValuationSubring.mem_comap]
    rw [IsScalarTower.algebraMap_apply k ↥K Ω]
    have hc : algebraMap k ↥K c ∈ B := by rw [htop]; trivial
    rwa [hBdef, ValuationSubring.mem_comap] at hc
  -- The ring of integers of `K` lies in `B`.
  have hR : ∀ x : NumberField.RingOfIntegers ↥K,
      algebraMap (NumberField.RingOfIntegers ↥K) ↥K x ∈ B :=
    fun x => Commons.NumberTheory.NumberField.ringOfIntegers_le_of_valuationSubring B x
  -- The prime `p` of `𝓞[K]` whose valuation ring is `B`.
  obtain ⟨p, hp⟩ :=
    Commons.RingTheory.Valuation.exists_heightOneSpectrum_eq_valuationSubringAtPrime B hB hR
  -- `B` and the `p`-adic valuation subring agree, hence their valuations are equivalent.
  have hp' : B = (p.valuation ↥K).valuationSubring := by
    rw [hp, IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring]
  have hBp : B.valuation.IsEquiv (p.valuation ↥K) := by
    rw [Valuation.isEquiv_iff_valuationSubring, ValuationSubring.valuationSubring_valuation]
    exact hp'
  -- `B.valuation` is the pullback of `A.valuation` along `↥K → Ω`.
  have hBA : (A.valuation.comap (algebraMap ↥K Ω)).IsEquiv B.valuation := by
    rw [Valuation.isEquiv_iff_val_le_one]
    intro y
    rw [Valuation.comap_apply, ValuationSubring.valuation_le_one_iff,
      ValuationSubring.valuation_le_one_iff, hBdef, ValuationSubring.mem_comap]
  -- The prime `p` is exactly `q`, because the two are cut out by the same inequality.
  have key : ∀ x : NumberField.RingOfIntegers ↥K, x ∈ p.asIdeal ↔ x ∈ q.asIdeal := by
    intro x
    rw [← IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem (K := ↥K) p x]
    rw [← hBp.lt_one_iff_lt_one]
    rw [← hBA.lt_one_iff_lt_one]
    rw [Valuation.comap_apply]
    rw [IntermediateField.algebraMap_apply]
    rw [← hAq x]
  have hpq : p = q :=
    IsDedekindDomain.HeightOneSpectrum.asIdeal_injective (Ideal.ext (fun x => key x))
  rw [hp, hpq]

end Work.SSGRoute
