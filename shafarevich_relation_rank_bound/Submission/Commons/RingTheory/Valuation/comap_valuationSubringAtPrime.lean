import Mathlib.NumberTheory.RamificationInertia.Valuation

set_option linter.style.haveILetI false

namespace Commons.RingTheory.Valuation

/-- **The valuation ring of a place restricts to the valuation ring of the place below.**

If `w` is a finite place of a number field `L` lying over the finite place `q` of a number
field `K ⊆ L`, then the preimage in `K` of the valuation ring `𝒪_{L,w}` is the valuation
ring `𝒪_{K,q}`.

This is the statement that the `w`-adic valuation of `L`, restricted to `K`, defines the same
valuation subring as the `q`-adic valuation of `K`: the two valuations differ in general by
the ramification index `e = e(w/q)`, but since both take values in `ℤᵐ⁰` and `e > 0`,
an element of `K` has value `≤ 1` for one exactly when it has value `≤ 1` for the other. -/
theorem comap_valuationSubringAtPrime {K L : Type*} [Field K] [Field L] [NumberField K]
    [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (h : w.asIdeal.LiesOver q.asIdeal) :
    (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime L w).comap (algebraMap K L) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K q := by
  haveI := h
  ext x
  -- Both sides are valuation subrings; rewrite membership as a bound `≤ 1` on the adic
  -- valuation, and compare the valuations of `L` at `w` and of `K` at `q`.
  rw [ValuationSubring.mem_comap,
    IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring,
    IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring,
    Valuation.mem_valuationSubring_iff, Valuation.mem_valuationSubring_iff,
    ← IsDedekindDomain.HeightOneSpectrum.valuation_liesOver (L := L) q w x]
  -- `w.valuation L (algebraMap K L x) = q.valuation K x ^ e` where `e > 0` is the
  -- ramification index; raising to a positive power preserves the condition `≤ 1`.
  exact pow_le_one_iff_of_nonneg (a := q.valuation K x) zero_le
    (Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver w.asIdeal q.ne_bot)

end Commons.RingTheory.Valuation