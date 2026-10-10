import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Submission.Commons.NumberTheory.NumberField.ringOfIntegers_le_of_ne_top
import Submission.Commons.RingTheory.Valuation.exists_heightOneSpectrum_eq_valuationSubringAtPrime
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.TatePoitouRoute.FinitenessHM

/-- **A proper valuation subring of a number field has a rational prime with value `< 1`.**

Proof route (the relevant lemmas live in this workspace, import them explicitly):
`Commons.RingTheory.Valuation.exists_heightOneSpectrum_eq_valuationSubringAtPrime` (file
`Submission/Commons/RingTheory/Valuation/exists_heightOneSpectrum_eq_valuationSubringAtPrime.lean`)
applied to `V` with the integrality hypothesis from
`Commons.NumberTheory.NumberField.ringOfIntegers_le_of_ne_top` writes
`V = IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime k P` for a nonzero prime `P` of
`𝓞 k`.  The nonzero integer `Ideal.absNorm P.asIdeal` lies in `P.asIdeal` (`Ideal.absNorm_mem`,
`Ideal.absNorm_eq_zero_iff`), so `P.asIdeal.under ℤ` is a nonzero prime ideal of `ℤ`; every ideal of
`ℤ` is principal (`Submodule.IsPrincipal`, `Ideal.span_singleton_generator`), so
`P.asIdeal.under ℤ = Ideal.span {g}` with `Prime g` (`Ideal.span_singleton_prime`,
`Int.prime_iff_natAbs_prime`), and `p := g.natAbs` satisfies `(p : 𝓞 k) ∈ P.asIdeal` (use
`Int.associated_natAbs` and that a prime ideal contains no units).  Finally, `x ∈ P.asIdeal`
implies `V.valuation (x : k) < 1` via `IsLocalization.AtPrime.to_map_mem_maximal_iff` together with
`ValuationSubring.valuation_lt_one_iff` (exactly the pattern of `Work.SSGRoute.primeOfLevel_mem_iff`
in `Submission/Work/SSGRoute/RamifiedPlacesAux.lean`), and
`algebraMap (𝓞 k) k (p : 𝓞 k) = (p : k)`. -/
theorem exists_prime_val_lt_one_of_ne_top {k : Type} [Field k] [NumberField k]
    (V : ValuationSubring k) (hV : V ≠ ⊤) :
    ∃ p : ℕ, p.Prime ∧ V.valuation (p : k) < 1 := by
  -- Write `V` as the valuation subring attached to a nonzero prime `P` of `𝓞 k`.
  obtain ⟨P, hPeq⟩ :=
    Commons.RingTheory.Valuation.exists_heightOneSpectrum_eq_valuationSubringAtPrime (L := k) V hV
      (Commons.NumberTheory.NumberField.ringOfIntegers_le_of_ne_top V hV)
  subst hPeq
  -- `P.asIdeal.under ℤ` is a nonzero prime ideal of `ℤ`.
  have hU : P.asIdeal.under ℤ ≠ ⊥ :=
    Ideal.under_ne_bot (A := ℤ) (P := P.asIdeal) P.ne_bot
  have hUprime : (P.asIdeal.under ℤ).IsPrime :=
    Ideal.comap_isPrime (algebraMap ℤ (NumberField.RingOfIntegers k)) P.asIdeal
  -- Every ideal of `ℤ` is principal, so `P.asIdeal.under ℤ = Ideal.span {g}`.
  obtain ⟨g, hg⟩ : ∃ g : ℤ, Ideal.span {g} = P.asIdeal.under ℤ :=
    ⟨Submodule.IsPrincipal.generator (P.asIdeal.under ℤ),
      Ideal.span_singleton_generator (P.asIdeal.under ℤ)⟩
  have hg0 : g ≠ 0 := by
    intro h0
    exact hU (by rw [← hg, h0, Ideal.span_singleton_eq_bot])
  have hgprime : Prime g :=
    (Ideal.span_singleton_prime hg0).mp (by rw [hg]; exact hUprime)
  -- `p := g.natAbs` is prime and lies in `P.asIdeal`.
  have hassoc : Associated g (g.natAbs : ℤ) := Int.associated_natAbs g
  have hspan : Ideal.span {g} = Ideal.span {(g.natAbs : ℤ)} :=
    Ideal.span_singleton_eq_span_singleton.mpr hassoc
  have hmem_int : (g.natAbs : ℤ) ∈ P.asIdeal.under ℤ := by
    rw [← hg, hspan]
    exact Ideal.mem_span_singleton_self _
  have hmap : algebraMap ℤ (NumberField.RingOfIntegers k) (g.natAbs : ℤ) =
      (g.natAbs : NumberField.RingOfIntegers k) := by simp
  have hmem : (g.natAbs : NumberField.RingOfIntegers k) ∈ P.asIdeal := by
    rw [← hmap]
    exact (Ideal.mem_under ℤ P.asIdeal).mp hmem_int
  refine ⟨g.natAbs, Int.prime_iff_natAbs_prime.mp hgprime, ?_⟩
  -- Membership in `P` is exactly the valuation inequality.
  have hiff : (g.natAbs : NumberField.RingOfIntegers k) ∈ P.asIdeal ↔
      (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime k P).valuation
        (algebraMap (NumberField.RingOfIntegers k) k
          (g.natAbs : NumberField.RingOfIntegers k)) < 1 := by
    rw [← IsLocalization.AtPrime.to_map_mem_maximal_iff
      (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime k P) P.asIdeal
      (g.natAbs : NumberField.RingOfIntegers k)]
    exact ValuationSubring.valuation_lt_one_iff _ _
  have hlt := hiff.mp hmem
  simpa only [map_natCast] using hlt

end Work.SSGRoute.TatePoitouRoute.FinitenessHM
