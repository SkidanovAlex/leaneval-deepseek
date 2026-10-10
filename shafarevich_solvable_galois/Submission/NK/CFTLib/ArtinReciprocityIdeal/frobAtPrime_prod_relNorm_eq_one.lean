import Mathlib.RingTheory.Frobenius
import Mathlib.RingTheory.Ideal.Norm.RelNorm
import Submission.NK.CFTLib.ArtinReciprocityIdeal.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The Artin symbol of the norm of an ideal is trivial

This file proves `NK.CFTLib.ArtinReciprocityIdeal.frobAtPrime_prod_relNorm_eq_one`: for an
abelian extension `L/K` of number fields, if the relative norm of an ideal `I` of `𝓞 L` factors as
`∏ p ∈ s, p ^ (e p)` with all the primes of `s` unramified in `L`, then the product of any choice of
Frobenius elements `σ p` at the `p ∈ s` satisfies `∏ p ∈ s, σ p ^ e p = 1`.

The proof is the classical "the Artin symbol kills norms": the Frobenius symbol extends
multiplicatively to ideals (`artinSymbol`), and `artinSymbol (N 𝔟) = 1` because for a prime `𝔓 | 𝔭`
of `𝓞 L` one has `N 𝔓 = 𝔭 ^ f(𝔓|𝔭)` (`Ideal.relNorm_eq_pow_of_isMaximal`) while the chosen
Frobenius at an *unramified* `𝔭` has order exactly the inertia degree `f(𝔓|𝔭)`
(`orderOf_frobAtPrime_eq_inertiaDeg`).  Ramified primes are simply ignored by the symbol.

The main results:

* `NK.CFTLib.ArtinReciprocityIdeal.orderOf_frobAtPrime_eq_inertiaDeg`;
* `NK.CFTLib.ArtinReciprocityIdeal.artinSymbol` and its multiplicativity
  (`artinSymbol_mul`, `artinSymbol_prime_pow`, `artinSymbol_finset_prod`);
* `NK.CFTLib.ArtinReciprocityIdeal.artinSymbol_relNorm_eq_one` — the symbol kills norms;
* `NK.CFTLib.ArtinReciprocityIdeal.frobAtPrime_prod_relNorm_eq_one` — the target.
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace NK.CFTLib.ArtinReciprocityIdeal

open NK.Chebotarev
open NumberField
open scoped NumberField BigOperators IsMulCommutative

section Helpers

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L] [IsMulCommutative (Gal(L/K))]

/-- `𝔭` is unramified in `L / K`: every prime of `𝓞 L` above `𝔭` has ramification index one. -/
def IsUnramified (𝔭 : PrimeIdeal K) : Prop :=
  ∀ P : PrimeIdeal L, P.asIdeal.LiesOver 𝔭.asIdeal →
    P.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) = 1

/-- **The order of the chosen Frobenius at an unramified prime is the inertia degree.** -/
theorem orderOf_frobAtPrime_eq_inertiaDeg
    (𝔭 : PrimeIdeal K) (P : PrimeIdeal L) (hP : P.asIdeal.LiesOver 𝔭.asIdeal)
    (hunr : IsUnramified (K := K) (L := L) 𝔭) :
    orderOf (frobAtPrime (K := K) (L := L) 𝔭)
      = P.asIdeal.inertiaDeg (NumberField.RingOfIntegers K) := by
  have hcomm : ∀ a b : Gal(L/K), a * b = b * a := fun a b => IsMulCommutative.is_comm.comm a b
  obtain ⟨σ, hσ⟩ := exists_isFrobAt (K := K) (L := L) 𝔭 P hP
  have hfp : frobAtPrime (K := K) (L := L) 𝔭 = σ :=
    (isFrobAtPrime_iff_frobAtPrime_eq hcomm 𝔭 hunr σ).mp ⟨P, hP, hσ⟩
  rw [hfp]
  have hstab : Ideal.map (galRestrict (NumberField.RingOfIntegers K) K L
      (NumberField.RingOfIntegers L) σ : NumberField.RingOfIntegers L →+*
        NumberField.RingOfIntegers L) P.asIdeal = P.asIdeal := by
    have h2 := Ideal.map_comap_eq_self_of_equiv (galRestrict (NumberField.RingOfIntegers K) K L
      (NumberField.RingOfIntegers L) σ) P.asIdeal
    rw [show Ideal.comap ((galRestrict (NumberField.RingOfIntegers K) K L
        (NumberField.RingOfIntegers L)) σ) P.asIdeal = P.asIdeal from hσ.comap_eq] at h2
    exact h2
  exact Commons.NumberTheory.NumberField.orderOf_frobenius_eq_inertiaDeg 𝔭 P hP (hunr P hP) σ
    hstab (fun x => hσ.mk_apply hP x)

/-- The Frobenius symbol at an ideal: the Frobenius at the (unique) unramified prime realising it,
and `1` if the ideal is not a prime, or the prime is ramified. -/
noncomputable def frobSymbol (𝔭 : Ideal (NumberField.RingOfIntegers K)) : Gal(L/K) := by
  classical
  exact
    if h : ∃ P : PrimeIdeal K, P.asIdeal = 𝔭 ∧ IsUnramified (K := K) (L := L) P then
      frobAtPrime (K := K) (L := L) h.choose
    else 1

/-- The Frobenius symbol at the prime ideal of an unramified prime is the chosen Frobenius. -/
theorem frobSymbol_eq (𝔭 : PrimeIdeal K) (hunr : IsUnramified (K := K) (L := L) 𝔭) :
    frobSymbol (K := K) (L := L) 𝔭.asIdeal = frobAtPrime (K := K) (L := L) 𝔭 := by
  have h : ∃ P : PrimeIdeal K, P.asIdeal = 𝔭.asIdeal ∧ IsUnramified (K := K) (L := L) P :=
    ⟨𝔭, rfl, hunr⟩
  rw [frobSymbol, dif_pos h]
  congr 1
  exact IsDedekindDomain.HeightOneSpectrum.ext h.choose_spec.1

/-- A power of a prime ideal is nonzero. -/
theorem primeIdeal_pow_ne_bot (p : PrimeIdeal K) (n : ℕ) : p.asIdeal ^ n ≠ ⊥ := by
  rcases Nat.eq_zero_or_pos n with h | h
  · rw [h, pow_zero, Ideal.one_eq_top]; exact top_ne_bot
  · exact fun hc => p.ne_bot ((Ideal.pow_eq_bot h.ne').mp hc)

/-- The Artin symbol of an ideal: the product of the Frobenius symbols over the prime factors. -/
noncomputable def artinSymbol (𝔞 : Ideal (NumberField.RingOfIntegers K)) : Gal(L/K) :=
  ((UniqueFactorizationMonoid.normalizedFactors 𝔞).map (frobSymbol (K := K) (L := L))).prod

/-- The symbol of the unit ideal is trivial. -/
theorem artinSymbol_one : artinSymbol (K := K) (L := L) (1 : Ideal (𝓞 K)) = 1 := by
  simp only [artinSymbol, UniqueFactorizationMonoid.normalizedFactors_one, Multiset.map_zero,
    Multiset.prod_zero]

/-- The symbol is multiplicative on nonzero ideals. -/
theorem artinSymbol_mul {𝔞 𝔟 : Ideal (𝓞 K)} (h𝔞 : 𝔞 ≠ ⊥) (h𝔟 : 𝔟 ≠ ⊥) :
    artinSymbol (K := K) (L := L) (𝔞 * 𝔟)
      = artinSymbol (K := K) (L := L) 𝔞 * artinSymbol (K := K) (L := L) 𝔟 := by
  simp only [artinSymbol]
  rw [UniqueFactorizationMonoid.normalizedFactors_mul
      (show 𝔞 ≠ 0 from fun h => h𝔞 (h.trans Ideal.zero_eq_bot))
      (show 𝔟 ≠ 0 from fun h => h𝔟 (h.trans Ideal.zero_eq_bot)),
    Multiset.map_add, Multiset.prod_add]

/-- The symbol of a power of a prime ideal is the power of the Frobenius symbol. -/
theorem artinSymbol_prime_pow (𝔭 : PrimeIdeal K) (n : ℕ) :
    artinSymbol (K := K) (L := L) (𝔭.asIdeal ^ n)
      = frobSymbol (K := K) (L := L) 𝔭.asIdeal ^ n := by
  simp only [artinSymbol]
  rw [𝔭.irreducible.normalizedFactors_pow, normalize_eq, Multiset.map_replicate,
    Multiset.prod_replicate]

/-- The symbol is multiplicative over a finite product of powers of prime ideals. -/
theorem artinSymbol_finset_prod (s : Finset (PrimeIdeal K)) (e : PrimeIdeal K → ℕ) :
    artinSymbol (K := K) (L := L) (∏ p ∈ s, p.asIdeal ^ e p)
      = ∏ p ∈ s, frobSymbol (K := K) (L := L) p.asIdeal ^ e p := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      rw [Finset.prod_empty, Finset.prod_empty]
      exact artinSymbol_one
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.prod_insert ha,
        artinSymbol_mul (primeIdeal_pow_ne_bot a (e a))
          (Finset.prod_ne_zero_iff.mpr fun p _ => primeIdeal_pow_ne_bot p (e p)),
        artinSymbol_prime_pow, ih]

/-- **The Frobenius symbol at a prime below a prime of `𝓞 L`, raised to the inertia degree, is
trivial.**  This is the local input: `N 𝔓 = 𝔭 ^ f(𝔓|𝔭)`, and the Frobenius at an unramified `𝔭` has
order exactly `f(𝔓|𝔭)`. -/
theorem frobSymbol_under_pow_inertiaDeg_eq_one
    (p : Ideal (𝓞 L)) (hp : p.IsPrime) (hp0 : p ≠ ⊥) :
    frobSymbol (K := K) (L := L) (p.under (𝓞 K)) ^ p.inertiaDeg (𝓞 K) = 1 := by
  haveI : p.IsPrime := hp
  have hqprime : (p.under (𝓞 K)).IsPrime := inferInstance
  have hqne : p.under (𝓞 K) ≠ ⊥ := Ideal.under_ne_bot (𝓞 K) hp0
  by_cases hu : IsUnramified (K := K) (L := L) ⟨p.under (𝓞 K), hqprime, hqne⟩
  · have hEq : frobSymbol (K := K) (L := L) (p.under (𝓞 K))
        = frobAtPrime (K := K) (L := L) ⟨p.under (𝓞 K), hqprime, hqne⟩ :=
      frobSymbol_eq (K := K) (L := L) ⟨p.under (𝓞 K), hqprime, hqne⟩ hu
    rw [hEq, ← orderOf_dvd_iff_pow_eq_one,
      orderOf_frobAtPrime_eq_inertiaDeg ⟨p.under (𝓞 K), hqprime, hqne⟩
        ⟨p, hp, hp0⟩ ⟨rfl⟩ hu]
  · have h1 : frobSymbol (K := K) (L := L) (p.under (𝓞 K)) = 1 := by
      unfold frobSymbol
      rw [dif_neg (by
        rintro ⟨P, hP, hPu⟩
        have hPeq : P = ⟨p.under (𝓞 K), hqprime, hqne⟩ :=
          IsDedekindDomain.HeightOneSpectrum.ext hP
        exact hu (hPeq ▸ hPu))]
    rw [h1, one_pow]

/-- **The Artin symbol kills norms of ideals.** -/
theorem artinSymbol_relNorm_eq_one (𝔟 : Ideal (𝓞 L)) :
    artinSymbol (K := K) (L := L) (Ideal.relNorm (𝓞 K) 𝔟) = 1 := by
  refine UniqueFactorizationMonoid.induction_on_prime
    (P := fun 𝔟 : Ideal (𝓞 L) =>
      artinSymbol (K := K) (L := L) (Ideal.relNorm (𝓞 K) 𝔟) = 1) 𝔟 ?_ ?_ ?_
  · rw [Ideal.zero_eq_bot, Ideal.relNorm_bot, artinSymbol, ← Ideal.zero_eq_bot,
      UniqueFactorizationMonoid.normalizedFactors_zero, Multiset.map_zero, Multiset.prod_zero]
  · intro x hx
    rw [Ideal.isUnit_iff.mp hx, Ideal.relNorm_top, artinSymbol, ← Ideal.one_eq_top,
      UniqueFactorizationMonoid.normalizedFactors_one, Multiset.map_zero, Multiset.prod_zero]
  · intro a p ha hpprime iha
    have ha' : a ≠ ⊥ := fun h => ha (h.trans Ideal.zero_eq_bot.symm)
    have hpbot : p ≠ ⊥ := fun h => hpprime.ne_zero (h.trans Ideal.zero_eq_bot.symm)
    have hpIsPrime : p.IsPrime := (Ideal.prime_iff_isPrime hpbot).mp hpprime
    have hna : Ideal.relNorm (𝓞 K) a ≠ ⊥ :=
      fun h => ha' ((Ideal.relNorm_eq_bot_iff).mp h)
    have hnp : Ideal.relNorm (𝓞 K) p ≠ ⊥ :=
      fun h => hpbot ((Ideal.relNorm_eq_bot_iff).mp h)
    have hsym : artinSymbol (K := K) (L := L) (Ideal.relNorm (𝓞 K) p) = 1 := by
      haveI : p.IsPrime := hpIsPrime
      haveI : p.IsMaximal := Ring.DimensionLEOne.maximalOfPrime hpbot hpIsPrime
      have hqprime : (p.under (𝓞 K)).IsPrime := inferInstance
      have hqne : p.under (𝓞 K) ≠ ⊥ := Ideal.under_ne_bot (𝓞 K) hpbot
      haveI : (p.under (𝓞 K)).IsMaximal :=
        Ring.DimensionLEOne.maximalOfPrime hqne hqprime
      haveI : p.LiesOver (p.under (𝓞 K)) := ⟨rfl⟩
      rw [Ideal.relNorm_eq_pow_of_isMaximal p (p.under (𝓞 K)),
        artinSymbol_prime_pow (K := K) (L := L) ⟨p.under (𝓞 K), hqprime, hqne⟩]
      exact frobSymbol_under_pow_inertiaDeg_eq_one p hpIsPrime hpbot
    rw [map_mul (Ideal.relNorm (𝓞 K)) p a, artinSymbol_mul hnp hna, iha, mul_one]
    exact hsym

/-- The product in the `List`-form of a `Finset` is the `Finset.prod`. -/
theorem toList_map_prod_eq_finset_prod {ι M : Type*} [CommMonoid M] (s : Finset ι) (f : ι → M) :
    (s.toList.map f).prod = ∏ x ∈ s, f x := by
  rw [Finset.prod_eq_multiset_prod, ← Multiset.prod_coe (s.toList.map f),
    ← Finset.coe_toList, ← Multiset.map_coe f s.toList]

end Helpers

theorem frobAtPrime_prod_relNorm_eq_one {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [IsMulCommutative (Gal(L/K))]
    (I : Ideal (NumberField.RingOfIntegers L)) (s : Finset (NK.Chebotarev.PrimeIdeal K))
    (e : NK.Chebotarev.PrimeIdeal K → ℕ)
    (σ : NK.Chebotarev.PrimeIdeal K → Gal(L/K))
    (hunr : ∀ p ∈ s, ∀ P : NK.Chebotarev.PrimeIdeal L, P.asIdeal.LiesOver p.asIdeal →
      P.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) = 1)
    (hσ : ∀ p ∈ s, NK.Chebotarev.IsFrobAtPrime (K := K) (L := L) p (σ p))
    (hfac : Ideal.relNorm (NumberField.RingOfIntegers K) I = ∏ p ∈ s, p.asIdeal ^ e p) :
    (s.toList.map (fun p => σ p ^ e p)).prod = 1 := by
  classical
  have hcomm : ∀ a b : Gal(L/K), a * b = b * a := fun a b => IsMulCommutative.is_comm.comm a b
  rw [frobAtPrime_prod_irrel hcomm s e σ hunr hσ, toList_map_prod_eq_finset_prod]
  have h₁ : ∏ p ∈ s, (frobAtPrime (K := K) (L := L) p) ^ e p
      = ∏ p ∈ s, frobSymbol (K := K) (L := L) p.asIdeal ^ e p :=
    Finset.prod_congr rfl fun p hp => by rw [frobSymbol_eq (K := K) (L := L) p (hunr p hp)]
  rw [h₁, ← artinSymbol_finset_prod, ← hfac]
  exact artinSymbol_relNorm_eq_one I

end NK.CFTLib.ArtinReciprocityIdeal
