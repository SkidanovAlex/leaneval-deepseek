import Mathlib
import Submission.NK.GlobalCFTdeep.Herbrand.TUnitsRank
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.GlobalCFTdeep.Herbrand

open scoped NumberField nonZeroDivisors
open NumberField IsDedekindDomain

/-- For any finite place `q` of a number field `L` there is a nonzero `N` and a global unit
`a : Lˣ` whose `q`-adic valuation is exactly `N` and which is a local unit at every other
finite place: the class of `q` in the ideal class group is torsion (the class group is
finite), so a power `q ^ N` of `q` is principal, and any generator of it has the required
valuations. -/
theorem exists_expUnit_eq_single {L : Type} [Field L] [NumberField L]
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L)) :
    ∃ N : ℕ, 0 < N ∧ ∃ a : Lˣ, NK.GlobalCFTdeep.expUnit q a = N ∧
      ∀ q' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L),
        q' ≠ q → NK.GlobalCFTdeep.expUnit q' a = 0 := by
  classical
  set n : ℕ := Fintype.card (ClassGroup (𝓞 L)) with hn_def
  have hn_pos : 0 < n := by
    rw [hn_def]
    exact Fintype.card_pos_iff.mpr ⟨1⟩
  have hqmem : q.asIdeal ∈ nonZeroDivisors (Ideal (𝓞 L)) :=
    mem_nonZeroDivisors_iff_ne_zero.mpr q.ne_bot
  have hpow_mem : q.asIdeal ^ n ∈ nonZeroDivisors (Ideal (𝓞 L)) := pow_mem hqmem n
  -- `q ^ n` is principal, since the class group is finite.
  have hmk0 : ClassGroup.mk0 (⟨q.asIdeal ^ n, hpow_mem⟩ : nonZeroDivisors (Ideal (𝓞 L))) = 1 := by
    have hpow : (⟨q.asIdeal ^ n, hpow_mem⟩ : nonZeroDivisors (Ideal (𝓞 L)))
        = (⟨q.asIdeal, hqmem⟩ : nonZeroDivisors (Ideal (𝓞 L))) ^ n := by
      ext
      rw [SubmonoidClass.coe_pow]
    rw [hpow, map_pow, hn_def]
    exact pow_card_eq_one
  have hprincipal : (q.asIdeal ^ n).IsPrincipal :=
    (ClassGroup.mk0_eq_one_iff hpow_mem).mp hmk0
  obtain ⟨a₀, ha₀⟩ := (Submodule.isPrincipal_iff (q.asIdeal ^ n)).mp hprincipal
  have ha₀' : Ideal.span {a₀} = q.asIdeal ^ n := ha₀.symm
  have ha₀_ne : a₀ ≠ 0 := by
    intro h
    have hbot : q.asIdeal ^ n = ⊥ := by
      rw [← ha₀', h, Ideal.span_singleton_eq_bot.mpr rfl]
    have hne : q.asIdeal ^ n ≠ 0 := by
      simpa using (mem_nonZeroDivisors_iff_ne_zero.mp hpow_mem)
    exact hne hbot
  have hval_ne : algebraMap (𝓞 L) L a₀ ≠ 0 := by
    rw [← map_zero (algebraMap (𝓞 L) L)]
    exact fun h => ha₀_ne (IsFractionRing.injective (𝓞 L) L h)
  -- the count of `q` in the factorization of `(a₀) = q ^ n` is `n`
  have hcount : (Associates.mk q.asIdeal).count
      (Associates.mk (Ideal.span {a₀} : Ideal (𝓞 L))).factors = n := by
    rw [ha₀', Associates.mk_pow,
      Associates.count_pow (Associates.mk_ne_zero.mpr q.ne_bot) q.associates_irreducible n,
      Associates.count_self q.associates_irreducible, mul_one]
  refine ⟨n, hn_pos, Units.mk0 (algebraMap (𝓞 L) L a₀) hval_ne, ?_, ?_⟩
  · have hcoe : ((Units.mk0 (algebraMap (𝓞 L) L a₀) hval_ne : Lˣ) : L)
        = algebraMap (𝓞 L) L a₀ := Units.val_mk0 hval_ne
    rw [NK.GlobalCFTdeep.expUnit, hcoe, HeightOneSpectrum.valuation_of_algebraMap,
      HeightOneSpectrum.intValuation_if_neg _ ha₀_ne, hcount]
    simp
  · intro q' hq'
    have hcoe : ((Units.mk0 (algebraMap (𝓞 L) L a₀) hval_ne : Lˣ) : L)
        = algebraMap (𝓞 L) L a₀ := Units.val_mk0 hval_ne
    rw [NK.GlobalCFTdeep.expUnit_eq_zero_iff, hcoe,
      HeightOneSpectrum.valuation_eq_one_iff_notMem]
    intro hmem
    have hle : q.asIdeal ^ n ≤ q'.asIdeal := by
      rw [← ha₀']
      exact Ideal.span_le.mpr (by rintro x rfl; exact hmem)
    have hsup : q'.asIdeal ⊔ q.asIdeal ^ n = ⊤ := by
      have h := HeightOneSpectrum.isCoprime_pow_of_ne q' q hq' 1 n
      simpa using (Ideal.isCoprime_iff_sup_eq.mp h)
    have htop : q'.asIdeal = ⊤ := by
      rw [← hsup, sup_eq_left.mpr hle]
    exact q'.isPrime.ne_top htop

end NK.GlobalCFTdeep.Herbrand
