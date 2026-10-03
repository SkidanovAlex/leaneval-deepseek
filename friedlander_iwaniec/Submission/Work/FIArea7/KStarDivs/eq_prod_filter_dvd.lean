import Mathlib
import Submission.Work.FIArea7.KStarDivs.PrimDefs

namespace Work.FIArea7.KStarDivs

open Classical
attribute [local instance] Classical.propDecidable

open Finset
open scoped BigOperators

/-!
# `e` is the product of the primary primes dividing it

Let `w` be primary (odd norm) and `e ∈ gaussPrimDivs w` squarefree.  Then `e` is exactly the product
of the primary prime divisors of `w` that divide `e`.

The proof is the standard "squarefree element of a UFD is the product of its (primary)
prime divisors": the product `P` of the primes in `primPrimeDivs w e` is primary, divides `e`,
and the quotient `e / P` has no irreducible factor — so it is a unit; both `e` and `P` being
primary and associated, they are equal.
-/
theorem eq_prod_filter_dvd (w e : GaussianInt) (hw : Work.FIPlan.IsPrimary w)
    (he : e ∈ gaussPrimDivs w) (hsq : Squarefree e) :
    e = ∏ p ∈ primPrimeDivs w e, p := by
  obtain ⟨hew, heprim⟩ := (mem_gaussPrimDivs hw).mp he
  set P := ∏ p ∈ primPrimeDivs w e, p with hPdef
  have hSsub : primPrimeDivs w e ⊆ primPrimes w := fun p hp => (mem_primPrimeDivs.mp hp).1
  have hPprim : Work.FIPlan.IsPrimary P := by
    rw [hPdef]; exact prod_primPrimes_isPrimary hSsub
  have hPdvd : P ∣ e := by
    rw [hPdef]
    exact (dvd_prod_primPrimes_iff hSsub).mpr (fun p hp => (mem_primPrimeDivs.mp hp).2)
  obtain ⟨c, hc⟩ := hPdvd
  have he0 : e ≠ 0 := isPrimary_ne_zero heprim
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hc
    exact he0 hc
  have hcunit : IsUnit c := by
    by_contra hcu
    obtain ⟨q, hqirr, hqd⟩ := WfDvdMonoid.exists_irreducible_factor hcu hc0
    -- `q` is an irreducible factor of the quotient `c`; it divides `e` and hence `w`
    have hqe : q ∣ e := hqd.trans ⟨P, by rw [hc, mul_comm]⟩
    have hqw : q ∣ w := hqe.trans hew
    have hq0 : q ≠ 0 := hqirr.ne_zero
    have hqodd : Odd (Work.FIPlan.gnorm q) := odd_gnorm_of_dvd_of_primary hw hqw
    -- the primary associate of `q` is a primary prime divisor of both `w` and `e`
    have hpS : primAssoc q ∈ primPrimes w := (mem_primPrimes hw).mpr
      ⟨(Associated.irreducible_iff (primAssoc_associated hq0 hqodd)).mpr hqirr,
        isPrimary_primAssoc hq0 hqodd, primAssoc_dvd hq0 hqodd hqw⟩
    have hpS' : primAssoc q ∈ primPrimeDivs w e := by
      rw [mem_primPrimeDivs]
      exact ⟨hpS, primAssoc_dvd hq0 hqodd hqe⟩
    -- hence `q` divides `P` as well as `c`, so `q ^ 2 ∣ e`, contradicting squarefreeness
    have hqP : q ∣ P := by
      rw [hPdef]
      exact (Associated.dvd_iff_dvd_left (primAssoc_associated hq0 hqodd)).mp
        (Finset.dvd_prod_of_mem (fun p => p) hpS')
    obtain ⟨a, ha⟩ := hqP
    obtain ⟨b, hb⟩ := hqd
    have hsq' : q * q ∣ e := ⟨a * b, by rw [hc, ha, hb]; ring⟩
    exact hqirr.not_isUnit (hsq q hsq')
  -- the quotient is a unit, so `P` and `e` are associated; both are primary
  obtain ⟨u, hu⟩ := hcunit
  have hassoc : Associated P e := ⟨u, by rw [hc, hu]⟩
  exact (isPrimary_associated_eq hPprim heprim hassoc).symm

end Work.FIArea7.KStarDivs
