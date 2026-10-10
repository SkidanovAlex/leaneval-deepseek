import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import Submission.Work.SSGRoute.local_lifting_setup
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# An integer prime to the residue characteristic is a unit of the valuation ring

Let `A` be a finite place of `ℚ̄` (a valuation subring of `ℚ̄ = AlgebraicClosure ℚ` whose restriction
to `ℚ` is not the whole of `ℚ`), and let `p = Work.SSGRoute.residueChar A` be the residue
characteristic of `A`, i.e. the rational prime below `A`.  Then every natural number `N` which is
not divisible by `p` is a unit of the valuation ring `↥A.1`.

The proof has three ingredients, all proved below:

* `card_quot_primeOf_eq_natGenerator` — for a place `q` of `ℚ`, the residue field
  `𝓞 ℚ ⧸ q.asIdeal` has cardinality the rational prime `natGenerator q` attached to `q`;
* `mem_primeOf_iff_dvd_natGenerator` — an integer lies in `q.asIdeal` exactly when `natGenerator q`
  divides it;
* `valuation_lt_one_iff_mem_primeOf` — for a finite place `A` of `ℚ̄`, the prime of `𝓞 ℚ` below `A`
  is cut out by the valuation inequality `A.1.valuation x < 1`.

Since `N ∈ ℤ ⊆ A.1` the value `A.1.valuation N` is `≤ 1`, and the third (with the first two)
shows it is not `< 1`; hence `A.1.valuation N = 1`, which for a valuation subring says exactly
`IsUnit`.
-/

set_option linter.style.haveILetI false

namespace Work.SSGRoute

/-- Comparison of the `(-).valuation (·) < 1` condition along a `comap` (a local copy of
`Work.SSGRoute.comap_valuation_lt_one_iff`). -/
theorem comap_valuation_lt_one_iff_local {K L : Type*} [Field K] [Field L] [Algebra K L]
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

/-- **The residue field at a place `q` of `ℚ` has `natGenerator q` elements.** -/
theorem card_quot_primeOf_eq_natGenerator
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ)) :
    Nat.card (NumberField.RingOfIntegers ℚ ⧸ q.asIdeal) =
      Rat.HeightOneSpectrum.natGenerator q := by
  haveI : NeZero (Rat.HeightOneSpectrum.natGenerator q) :=
    ⟨(Rat.HeightOneSpectrum.prime_natGenerator q).ne_zero⟩
  calc Nat.card (NumberField.RingOfIntegers ℚ ⧸ q.asIdeal)
      = Nat.card (ℤ ⧸ Ideal.map
          (Rat.IsIntegralClosure.intEquiv (NumberField.RingOfIntegers ℚ)) q.asIdeal) :=
        Nat.card_congr (Ideal.quotientEquiv q.asIdeal _
          (Rat.IsIntegralClosure.intEquiv (NumberField.RingOfIntegers ℚ)) rfl).toEquiv
    _ = Nat.card (ℤ ⧸ Ideal.span {(Rat.HeightOneSpectrum.natGenerator q : ℤ)}) := by
        rw [Rat.HeightOneSpectrum.span_natGenerator]
    _ = Nat.card (ZMod (Rat.HeightOneSpectrum.natGenerator q)) :=
        Nat.card_congr (Int.quotientSpanNatEquivZMod _).toEquiv
    _ = Rat.HeightOneSpectrum.natGenerator q := by
        rw [Nat.card_eq_fintype_card, ZMod.card]

/-- **Membership in a place of `ℚ` is divisibility by its rational prime.** -/
theorem mem_primeOf_iff_dvd_natGenerator
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ)) (N : ℕ) :
    (N : NumberField.RingOfIntegers ℚ) ∈ q.asIdeal ↔
      Rat.HeightOneSpectrum.natGenerator q ∣ N := by
  have h := Ideal.apply_mem_of_equiv_iff (I := q.asIdeal)
    (f := Rat.IsIntegralClosure.intEquiv (NumberField.RingOfIntegers ℚ))
    (x := (N : NumberField.RingOfIntegers ℚ))
  simp only [map_natCast] at h
  rw [Rat.HeightOneSpectrum.natGenerator_dvd_iff]
  exact h.symm

/-- **The prime of `𝓞 ℚ` below a finite place `A` of `ℚ̄` is cut out by the valuation inequality
`A.1.valuation x < 1`** (this is `Work.SSGRoute.primeOfLevel_mem_iff` at the level field `ℚ`). -/
theorem valuation_lt_one_iff_mem_primeOf
    (A : NK.FrobeniusBridge.FinitePlaceOf ℚ SSGRoute.QBar)
    (x : NumberField.RingOfIntegers ℚ) :
    A.1.valuation (algebraMap (NumberField.RingOfIntegers ℚ) SSGRoute.QBar x) < 1 ↔
      x ∈ (Submission.NeukirchUchida.primeOf A.1 A.2).asIdeal := by
  set q := Submission.NeukirchUchida.primeOf A.1 A.2 with hq
  have hspec : A.1.comap (algebraMap ℚ SSGRoute.QBar) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ℚ q :=
    Submission.NeukirchUchida.primeOf_spec A.1 A.2
  have heq : ((A.1.comap (algebraMap ℚ SSGRoute.QBar)).valuation).IsEquiv
      (IsDedekindDomain.HeightOneSpectrum.valuation ℚ q) := by
    rw [Valuation.isEquiv_iff_valuationSubring, ValuationSubring.valuationSubring_valuation,
      hspec, IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring]
  rw [(IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem (K := ℚ) q x).symm]
  rw [← heq.lt_one_iff_lt_one]
  rw [comap_valuation_lt_one_iff_local A.1 (algebraMap (NumberField.RingOfIntegers ℚ) ℚ x)]
  rw [← IsScalarTower.algebraMap_apply (NumberField.RingOfIntegers ℚ) ℚ SSGRoute.QBar x]

theorem isUnit_natCast_of_not_dvd_residueChar
    (A : NK.FrobeniusBridge.FinitePlaceOf ℚ SSGRoute.QBar) (p : ℕ)
    (hp : p = Work.SSGRoute.residueChar A) {N : ℕ} (hN : ¬ p ∣ N) :
    IsUnit (N : ↥A.1) := by
  have hq : p = Rat.HeightOneSpectrum.natGenerator
      (Submission.NeukirchUchida.primeOf A.1 A.2) := by
    rw [hp]
    exact card_quot_primeOf_eq_natGenerator (Submission.NeukirchUchida.primeOf A.1 A.2)
  have hnotmem : (N : NumberField.RingOfIntegers ℚ) ∉
      (Submission.NeukirchUchida.primeOf A.1 A.2).asIdeal := by
    rw [mem_primeOf_iff_dvd_natGenerator]
    exact fun h => hN (by rw [hq]; exact h)
  have hmemN : (N : SSGRoute.QBar) ∈ A.1 := by
    have h1 := Commons.NumberTheory.NumberField.ringOfIntegers_le_of_ne_top
      (A.1.comap (algebraMap ℚ SSGRoute.QBar)) A.2 (N : NumberField.RingOfIntegers ℚ)
    rw [ValuationSubring.mem_comap] at h1
    simpa using h1
  have hle : A.1.valuation (N : SSGRoute.QBar) ≤ 1 :=
    (ValuationSubring.valuation_le_one_iff A.1 (N : SSGRoute.QBar)).mpr hmemN
  have hnotlt : ¬ A.1.valuation (N : SSGRoute.QBar) < 1 := by
    intro hlt
    exact hnotmem ((valuation_lt_one_iff_mem_primeOf A (N : NumberField.RingOfIntegers ℚ)).mp
      (by simpa using hlt))
  have hval1 : A.1.valuation (N : SSGRoute.QBar) = 1 :=
    le_antisymm hle (not_lt.mp hnotlt)
  exact (ValuationSubring.valuation_eq_one_iff A.1 (N : ↥A.1)).mpr (by simpa using hval1)

end Work.SSGRoute
