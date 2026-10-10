import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import Submission.Work.SSGRoute.RamifiedPlacesAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The rational prime below a finite place of `ℚ̄`, from a valuation inequality

If a finite place `B` of `ℚ̄` satisfies `B.valuation p < 1` for a rational prime `p`, then the prime
of `ℤ` below `B` is `p`.  This is the "level `ℚ`" case of the description of the prime below a place
by a valuation inequality (`Work.SSGRoute.primeOfLevel_mem_iff`).

The first two lemmas are the two halves of the proof:

* `primesEquiv_eq_of_valuation_lt_one` is pure `ℚ`-adic valuation theory: for any height-one prime
  `v` of the ring of integers of `ℚ`, the value of `v.valuation` at `p` being `< 1` forces `v` to be
  the prime `(p)`.  It goes through `Rat.HeightOneSpectrum.primesEquiv` (whose value is
  `natGenerator v`), the equivalence of `v.valuation ℚ` with the `natGenerator v`-adic valuation,
  and `Int.padicValuation_lt_one_iff`.
* `primeOf_valuation_lt_one` is the transport of the hypothesis along the restriction
  `B ↦ B.comap (algebraMap ℚ ℚ̄)`: the prime below `B` is characterised by
  `B.comap (algebraMap ℚ ℚ̄) = valuationSubringAtPrime ℚ v`.
-/

set_option linter.style.haveILetI false

open SSGRoute

namespace Work.SSGRoute

/-- **A height-one prime of the ring of integers of `ℚ` is detected by its value at `p`.**
If `(v.valuation ℚ) (p : ℚ) < 1`, then `v` is the prime `(p)`. -/
theorem primesEquiv_eq_of_valuation_lt_one (p : ℕ) [Fact p.Prime]
    {R : Type*} [CommRing R] [Algebra R ℚ] [IsIntegralClosure R ℤ ℚ] [IsDedekindDomain R]
    [IsFractionRing R ℚ] (v : IsDedekindDomain.HeightOneSpectrum R)
    (h : v.valuation ℚ (p : ℚ) < 1) :
    Rat.HeightOneSpectrum.primesEquiv v = ⟨p, Fact.out⟩ := by
  haveI : Fact (Nat.Prime (Rat.HeightOneSpectrum.natGenerator v)) :=
    ⟨Rat.HeightOneSpectrum.prime_natGenerator v⟩
  refine (Nat.Primes.coe_nat_inj _ _).mp ?_
  show Rat.HeightOneSpectrum.natGenerator v = p
  -- `v.valuation ℚ` is equivalent to the `natGenerator v`-adic valuation
  have hv := Rat.HeightOneSpectrum.valuation_equiv_padicValuation v
  have hpad : Rat.padicValuation (Rat.HeightOneSpectrum.natGenerator v) (p : ℚ) < 1 :=
    (Valuation.IsEquiv.lt_one_iff_lt_one hv).mp h
  -- transport to `ℤ`, where `< 1` is divisibility by `p`
  have hz : Int.padicValuation (Rat.HeightOneSpectrum.natGenerator v) (p : ℤ) < 1 := by
    rw [← Rat.padicValuation_cast]
    simpa using hpad
  have hdvd : Rat.HeightOneSpectrum.natGenerator v ∣ p :=
    Int.natCast_dvd_natCast.mp (Int.padicValuation_lt_one_iff.mp hz)
  exact (Nat.prime_dvd_prime_iff_eq (Rat.HeightOneSpectrum.prime_natGenerator v) Fact.out).mp hdvd

/-- **The restriction of `B` to `ℚ` is the `p`-adic place** when `B.valuation p < 1`. -/
theorem primeOf_valuation_lt_one (p : ℕ) (B : ValuationSubring QBar) (hB : IsFinPlace ℚ B)
    (h : B.valuation (p : QBar) < 1) :
    (Submission.NeukirchUchida.primeOf B hB).valuation ℚ (p : ℚ) < 1 := by
  have hcomap : (B.comap (algebraMap ℚ QBar)).valuation (p : ℚ) < 1 :=
    (comap_valuation_lt_one_iff B (p : ℚ)).mpr (by simpa using h)
  rw [Submission.NeukirchUchida.primeOf_spec B hB] at hcomap
  -- the two valuations of `ℚ` have the same valuation subring
  have heq : ((IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ℚ
        (Submission.NeukirchUchida.primeOf B hB)).valuation).IsEquiv
      ((Submission.NeukirchUchida.primeOf B hB).valuation ℚ) :=
    (Valuation.isEquiv_iff_valuationSubring _ _).mpr (by
      rw [ValuationSubring.valuationSubring_valuation,
        ← IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring])
  exact (Valuation.IsEquiv.lt_one_iff_lt_one heq).mp hcomap

theorem placePrime_eq_of_val_lt_one (p : ℕ) [Fact p.Prime] (B : ValuationSubring SSGRoute.QBar)
    (hB : SSGRoute.IsFinPlace ℚ B) (h : B.valuation (p : SSGRoute.QBar) < 1) :
    Work.SSGRoute.placePrime B hB = ⟨p, Fact.out⟩ :=
  primesEquiv_eq_of_valuation_lt_one p (Submission.NeukirchUchida.primeOf B hB)
    (primeOf_valuation_lt_one p B hB h)

end Work.SSGRoute
