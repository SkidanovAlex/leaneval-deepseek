import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import Submission.Work.SSGRoute.local_lifting_setup
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The residue characteristic of a finite place of `ℚ̄` and divisibility

For a finite place `A` of `ℚ̄` (a valuation subring of `ℚ̄` whose restriction to `ℚ` is proper) the
*residue characteristic* `residueChar A` is the cardinality of the residue field of the prime of
`ℤ = 𝓞 ℚ` below `A`.  The purpose of this file is the elementary arithmetic fact used all over the
Shafarevich route:

> a natural number `N` is a unit of the valuation subring `A.1` as soon as `residueChar A ∤ N`.

The content is the classical description of the non-units of a valuation ring: if `v = A.1.valuation`
is the valuation of the place, then `x ∈ A.1` is a non-unit exactly when `v x < 1`
(`ValuationSubring.valuation_lt_one_iff`), and for a rational integer `N` this happens precisely
when the rational prime below `A` divides `N`
(`Int.padicValuation_lt_one_iff`, `Rat.HeightOneSpectrum.valuation_equiv_padicValuation`).

The two supporting lemmas are

* `residueChar_eq_natGenerator`: `residueChar A` is the natural generator of the height-one prime
  of `ℤ` below `A` (via `ℤ ⧸ (p) ≃+* ZMod p`);
* `residueChar_dvd_iff_valuation_lt_one`: `residueChar A ∣ N ↔ A.1.valuation (N : ℚ̄) < 1`.

## References

The lemma feeds `Work.SSGRoute.isInertia_of_mem_inertia` (and hence
`Work.SSGRoute.local_tame_lifting`), where the prime-to-`p` roots of unity have to be recognised as
units of the local ring `A.1`.
-/

namespace Work.SSGRoute

open _root_.SSGRoute

set_option linter.style.haveILetI false

/-- **Comparison of the `v x < 1` condition along a `comap`.**  For a valuation subring `B` of `L`
and `x : K`, the inequality for the comap of `B` along `algebraMap K L` is the inequality for `B` at
the image of `x`. -/
theorem comap_valuation_lt_one_iff' {K L : Type*} [Field K] [Field L] [Algebra K L]
    (B : ValuationSubring L) (x : K) :
    (B.comap (algebraMap K L)).valuation x < 1 ↔ B.valuation (algebraMap K L x) < 1 := by
  have hsub : (B.comap (algebraMap K L)).valuation.valuationSubring =
      (B.valuation.comap (algebraMap K L)).valuationSubring := by
    rw [ValuationSubring.valuationSubring_valuation]
    ext y
    simp only [ValuationSubring.mem_comap, Valuation.mem_valuationSubring_iff,
      ValuationSubring.valuation_le_one_iff, Valuation.comap_apply]
  have heq : (B.comap (algebraMap K L)).valuation.IsEquiv
      (B.valuation.comap (algebraMap K L)) :=
    (Valuation.isEquiv_iff_valuationSubring _ _).mpr hsub
  rw [Valuation.IsEquiv.lt_one_iff_lt_one heq]
  rfl

/-- **The residue characteristic of a finite place of `ℚ̄` is the rational prime below it.** -/
theorem residueChar_eq_natGenerator (A : NK.FrobeniusBridge.FinitePlaceOf ℚ SSGRoute.QBar) :
    residueChar A =
      Rat.HeightOneSpectrum.natGenerator (Submission.NeukirchUchida.primeOf A.1 A.2) := by
  set q := Submission.NeukirchUchida.primeOf A.1 A.2
  show Nat.card (NumberField.RingOfIntegers ℚ ⧸ q.asIdeal) = _
  have e : (NumberField.RingOfIntegers ℚ ⧸ q.asIdeal) ≃+*
      (ℤ ⧸ Ideal.span {(Rat.HeightOneSpectrum.natGenerator q : ℤ)}) :=
    Ideal.quotientEquiv q.asIdeal (Ideal.span {(Rat.HeightOneSpectrum.natGenerator q : ℤ)})
      (Rat.IsIntegralClosure.intEquiv (NumberField.RingOfIntegers ℚ))
      (Rat.HeightOneSpectrum.span_natGenerator q)
  rw [Nat.card_congr e.toEquiv]
  rw [Nat.card_congr (Int.quotientSpanNatEquivZMod (Rat.HeightOneSpectrum.natGenerator q)).toEquiv]
  exact Nat.card_zmod _

/-- **Divisibility by the residue characteristic, read off from the valuation.**  A natural number
`N` is divisible by `residueChar A` exactly when the valuation of the place `A` at `N` is `< 1`,
i.e. exactly when `N` is a non-unit of the valuation subring `A.1`. -/
theorem residueChar_dvd_iff_valuation_lt_one (A : NK.FrobeniusBridge.FinitePlaceOf ℚ SSGRoute.QBar)
    (N : ℕ) :
    residueChar A ∣ N ↔ A.1.valuation (N : SSGRoute.QBar) < 1 := by
  haveI : Fact (Nat.Prime (Rat.HeightOneSpectrum.natGenerator
      (Submission.NeukirchUchida.primeOf A.1 A.2))) :=
    ⟨Rat.HeightOneSpectrum.prime_natGenerator _⟩
  set q := Submission.NeukirchUchida.primeOf A.1 A.2
  rw [residueChar_eq_natGenerator A]
  have hB1 : A.1.valuation (N : SSGRoute.QBar) < 1 ↔
      (A.1.comap (algebraMap ℚ SSGRoute.QBar)).valuation (N : ℚ) < 1 := by
    rw [comap_valuation_lt_one_iff']
    simp
  have hB2 : (A.1.comap (algebraMap ℚ SSGRoute.QBar)).valuation (N : ℚ) < 1 ↔
      (q.valuation ℚ) (N : ℚ) < 1 := by
    have hsub : (A.1.comap (algebraMap ℚ SSGRoute.QBar)).valuation.valuationSubring =
        (q.valuation ℚ).valuationSubring := by
      rw [ValuationSubring.valuationSubring_valuation,
        Submission.NeukirchUchida.primeOf_spec A.1 A.2,
        IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring]
    exact Valuation.IsEquiv.lt_one_iff_lt_one
      ((Valuation.isEquiv_iff_valuationSubring _ _).mpr hsub)
  have hB3 : (q.valuation ℚ) (N : ℚ) < 1 ↔
      Rat.padicValuation (Rat.HeightOneSpectrum.natGenerator q) (N : ℚ) < 1 := by
    have heq := Rat.HeightOneSpectrum.valuation_equiv_padicValuation q
    exact Valuation.IsEquiv.lt_one_iff_lt_one heq
  have hB4 : Rat.padicValuation (Rat.HeightOneSpectrum.natGenerator q) (N : ℚ) < 1 ↔
      Int.padicValuation (Rat.HeightOneSpectrum.natGenerator q) (N : ℤ) < 1 := by
    have hcast : (N : ℚ) = ((N : ℤ) : ℚ) := by norm_cast
    rw [hcast, Rat.padicValuation_cast]
  have hB5 : Int.padicValuation (Rat.HeightOneSpectrum.natGenerator q) (N : ℤ) < 1 ↔
      Rat.HeightOneSpectrum.natGenerator q ∣ N := by
    rw [Int.padicValuation_lt_one_iff]
    exact Int.ofNat_dvd
  rw [hB1, hB2, hB3, hB4, hB5]

/-- **Integers coprime to the residue characteristic are units of the valuation ring.** -/
theorem residueUnit_clean
    (A : NK.FrobeniusBridge.FinitePlaceOf ℚ SSGRoute.QBar) (p : ℕ)
    (hp : p = Work.SSGRoute.residueChar A) {N : ℕ} (hN : ¬ p ∣ N) :
    IsUnit (N : ↥A.1) := by
  refine (ValuationSubring.valuation_eq_one_iff A.1 (N : ↥A.1)).mpr ?_
  rcases ValuationSubring.valuation_lt_one_or_eq_one A.1 (N : ↥A.1) with h | h
  · exfalso
    have hdvd : residueChar A ∣ N := by
      apply (residueChar_dvd_iff_valuation_lt_one A N).mpr
      rwa [show ((N : ↥A.1) : SSGRoute.QBar) = (N : SSGRoute.QBar) from rfl] at h
    rw [← hp] at hdvd
    exact hN hdvd
  · exact h

end Work.SSGRoute
