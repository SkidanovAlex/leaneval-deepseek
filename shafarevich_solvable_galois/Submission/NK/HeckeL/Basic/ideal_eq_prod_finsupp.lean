import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.DedekindDomain.Factorization
import Submission.NK.HeckeL.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open NumberField IsDedekindDomain
open scoped BigOperators Classical nonZeroDivisors

namespace NK.HeckeL.Basic

/-!
# Unique factorisation of ideals, away from a finite set of primes

Let `K` be a number field and let `S` be a finite set of primes of `𝓞 K`.  An ideal `I ≠ 0` which
is coprime to every prime of `S` factors uniquely as `∏ 𝔭 ∈ t, 𝔭 ^ n 𝔭` with `t` a finite set of
primes *outside* `S`.

The mathematical content is the unique factorisation of ideals in a Dedekind domain; the work here
is to phrase it on the subtype of primes avoiding `S`, which is what the Euler product of a Hecke
`L`-series needs (the factors at primes of `S` are omitted from the product).
-/

namespace IdealProdFinsupp

variable {K : Type*} [Field K] [NumberField K]

/-- The coercion `Ideal R → FractionalIdeal R⁰ L` is multiplicative over finite products. -/
lemma coeIdeal_finset_prod {R : Type*} [CommRing R] {L : Type*} [Field L] [Algebra R L]
    [IsFractionRing R L] {ι : Type*} (s : Finset ι) (g : ι → Ideal R) :
    ((∏ i ∈ s, g i : Ideal R) : FractionalIdeal R⁰ L)
      = ∏ i ∈ s, (g i : FractionalIdeal R⁰ L) := by
  induction s using Finset.induction with
  | empty => simp [FractionalIdeal.coeIdeal_top]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, FractionalIdeal.coeIdeal_mul, ih]

/-- A prime `v` occurs in the factorisation of the nonzero ideal `I` iff it divides `I`. -/
lemma count_coe_ne_zero_iff_dvd {I : Ideal (𝓞 K)} (hI : I ≠ 0) (v : PrimeIdeal K) :
    FractionalIdeal.count K v (I : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 ↔ v.asIdeal ∣ I := by
  rw [FractionalIdeal.count_coe K v hI]
  rw [show (↑((Associates.mk v.asIdeal).count (Associates.mk I).factors) : ℤ) ≠ 0 ↔
      (Associates.mk v.asIdeal).count (Associates.mk I).factors ≠ 0 by simp]
  exact Associates.count_ne_zero_iff_dvd hI v.irreducible

/-- The `v`-adic valuation of a product `∏ 𝔭 ∈ t, 𝔭 ^ (c 𝔭)` of powers of pairwise distinct
primes indexed by `t = c.support` is the value of `c` at `v`, provided `v` itself lies outside the
exceptional finite set `S` (and `0` otherwise). -/
lemma count_prod_finsupp_eq (S : Finset (PrimeIdeal K))
    (c : {𝔭 : PrimeIdeal K // 𝔭 ∉ S} →₀ ℕ) (v : PrimeIdeal K) :
    FractionalIdeal.count K v
      ((∏ 𝔭 ∈ c.support, 𝔭.1.asIdeal ^ c 𝔭 : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)
      = if hv : v ∉ S then (c ⟨v, hv⟩ : ℤ) else 0 := by
  rw [coeIdeal_finset_prod]
  simp only [FractionalIdeal.coeIdeal_pow]
  rw [FractionalIdeal.count_prod K v c.support
    (fun 𝔭 : {𝔭 : PrimeIdeal K // 𝔭 ∉ S} =>
      (𝔭.1.asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^ c 𝔭)
    (fun 𝔭 _ => pow_ne_zero (c 𝔭) (FractionalIdeal.coeIdeal_ne_zero.mpr 𝔭.1.ne_bot))]
  have hsum : (∑ 𝔭 ∈ c.support,
        FractionalIdeal.count K v ((𝔭.1.asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^ c 𝔭))
      = ∑ 𝔭 ∈ c.support, (c 𝔭 : ℤ) * (if 𝔭.1 = v then 1 else 0) := by
    refine Finset.sum_congr rfl fun 𝔭 _ => ?_
    rw [FractionalIdeal.count_pow, FractionalIdeal.count_maximal]
  rw [hsum]
  by_cases hvS : v ∉ S
  · rw [dif_pos hvS]
    have hcongr : ∀ 𝔭 ∈ c.support,
        (c 𝔭 : ℤ) * (if 𝔭.1 = v then 1 else 0)
          = (if 𝔭 = ⟨v, hvS⟩ then (c 𝔭 : ℤ) else 0) := by
      intro 𝔭 _
      have hiff : 𝔭.1 = v ↔ 𝔭 = ⟨v, hvS⟩ := by
        constructor
        · intro h; exact Subtype.ext h
        · intro h; rw [h]
      rw [hiff]
      by_cases h : 𝔭 = ⟨v, hvS⟩ <;> simp [h]
    rw [Finset.sum_congr rfl hcongr, Finset.sum_ite_eq']
    by_cases hmem : (⟨v, hvS⟩ : {𝔭 : PrimeIdeal K // 𝔭 ∉ S}) ∈ c.support
    · rw [if_pos hmem]
    · rw [if_neg hmem]
      rw [Finsupp.mem_support_iff, not_not] at hmem
      simp [hmem]
  · rw [dif_neg hvS]
    refine Finset.sum_eq_zero fun 𝔭 _ => ?_
    have hne : ¬ (𝔭.1 = v) := fun h => hvS (h ▸ 𝔭.2)
    rw [if_neg hne, mul_zero]

/-- A nonzero ideal is determined by the multiplicities of the primes in its factorisation. -/
lemma ideal_eq_of_count_eq {I J : Ideal (𝓞 K)} (hI : I ≠ 0) (hJ : J ≠ 0)
    (h : ∀ v : PrimeIdeal K,
      FractionalIdeal.count K v (I : FractionalIdeal (𝓞 K)⁰ K)
        = FractionalIdeal.count K v (J : FractionalIdeal (𝓞 K)⁰ K)) : I = J := by
  have h1 : ∏ᶠ v : PrimeIdeal K,
      (v.asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^ FractionalIdeal.count K v
        (I : FractionalIdeal (𝓞 K)⁰ K) = (I : FractionalIdeal (𝓞 K)⁰ K) :=
    FractionalIdeal.finprod_heightOneSpectrum_factorization' K
      (I := (I : FractionalIdeal (𝓞 K)⁰ K)) (FractionalIdeal.coeIdeal_ne_zero.mpr hI)
  have h2 : ∏ᶠ v : PrimeIdeal K,
      (v.asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^ FractionalIdeal.count K v
        (J : FractionalIdeal (𝓞 K)⁰ K) = (J : FractionalIdeal (𝓞 K)⁰ K) :=
    FractionalIdeal.finprod_heightOneSpectrum_factorization' K
      (I := (J : FractionalIdeal (𝓞 K)⁰ K)) (FractionalIdeal.coeIdeal_ne_zero.mpr hJ)
  have h3 : (I : FractionalIdeal (𝓞 K)⁰ K) = (J : FractionalIdeal (𝓞 K)⁰ K) := by
    rw [← h1, ← h2]
    exact finprod_congr fun v => by rw [h v]
  exact FractionalIdeal.coeIdeal_injective h3

end IdealProdFinsupp

theorem ideal_eq_prod_finsupp {K : Type*} [Field K] [NumberField K]
    (S : Finset (NK.HeckeL.PrimeIdeal K)) (I : Ideal (NumberField.RingOfIntegers K))
    (hI : I ≠ 0) (hcop : ∀ 𝔭 ∈ S, ¬ 𝔭.asIdeal ∣ I) :
    ∃! c : {𝔭 : NK.HeckeL.PrimeIdeal K // 𝔭 ∉ S} →₀ ℕ,
      (∏ 𝔭 ∈ c.support, (𝔭.1.asIdeal) ^ (c 𝔭)) = I := by
  classical
  set f : {𝔭 : PrimeIdeal K // 𝔭 ∉ S} → ℕ :=
    fun 𝔭 => (FractionalIdeal.count K 𝔭.1 (I : FractionalIdeal (𝓞 K)⁰ K)).toNat with hf
  have hfin : (Function.support f).Finite := by
    have hinj : Set.InjOn (fun 𝔭 : {𝔭 : PrimeIdeal K // 𝔭 ∉ S} => 𝔭.1)
        ((fun 𝔭 : {𝔭 : PrimeIdeal K // 𝔭 ∉ S} => 𝔭.1) ⁻¹'
          {p : PrimeIdeal K | p.asIdeal ∣ I}) :=
      fun a _ b _ h => Subtype.ext h
    refine (Set.Finite.preimage hinj (Ideal.finite_factors hI)).subset ?_
    intro 𝔭 h𝔭
    simp only [Function.mem_support] at h𝔭
    have h0 : FractionalIdeal.count K 𝔭.1 (I : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 := by
      intro hz
      exact h𝔭 (by simp [hf, hz])
    exact (IdealProdFinsupp.count_coe_ne_zero_iff_dvd hI 𝔭.1).mp h0
  let c : {𝔭 : PrimeIdeal K // 𝔭 ∉ S} →₀ ℕ := Finsupp.ofSupportFinite f hfin
  have hc : ∀ 𝔭, c 𝔭 = f 𝔭 := fun 𝔭 => congrFun Finsupp.ofSupportFinite_coe 𝔭
  have hcval : ∀ (v : PrimeIdeal K) (hv : v ∉ S),
      (c ⟨v, hv⟩ : ℤ) = FractionalIdeal.count K v (I : FractionalIdeal (𝓞 K)⁰ K) := by
    intro v hv
    rw [hc, hf]
    exact Int.toNat_of_nonneg (FractionalIdeal.count_coe_nonneg K v I)
  have hcounts : ∀ v : PrimeIdeal K,
      FractionalIdeal.count K v
        ((∏ 𝔭 ∈ c.support, 𝔭.1.asIdeal ^ c 𝔭 : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)
        = FractionalIdeal.count K v (I : FractionalIdeal (𝓞 K)⁰ K) := by
    intro v
    rw [IdealProdFinsupp.count_prod_finsupp_eq S c v]
    by_cases hv : v ∉ S
    · rw [dif_pos hv]; exact hcval v hv
    · rw [dif_neg hv]
      have hvS : v ∈ S := by
        by_contra h
        exact hv h
      have h0 : FractionalIdeal.count K v (I : FractionalIdeal (𝓞 K)⁰ K) = 0 := by
        by_contra hne
        exact hcop v hvS ((IdealProdFinsupp.count_coe_ne_zero_iff_dvd hI v).mp hne)
      exact h0.symm
  have hPne : (∏ 𝔭 ∈ c.support, 𝔭.1.asIdeal ^ c 𝔭 : Ideal (𝓞 K)) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro 𝔭 _
    exact pow_ne_zero _ (by simpa using HeightOneSpectrum.ne_bot 𝔭.1)
  have hP : (∏ 𝔭 ∈ c.support, (𝔭.1.asIdeal) ^ (c 𝔭)) = I :=
    IdealProdFinsupp.ideal_eq_of_count_eq hPne hI hcounts
  refine ⟨c, hP, ?_⟩
  intro c' hc'
  ext 𝔭
  have h1 := IdealProdFinsupp.count_prod_finsupp_eq S c' 𝔭.1
  rw [dif_pos 𝔭.2] at h1
  rw [hc'] at h1
  have h3 : (c' 𝔭 : ℤ) = (c 𝔭 : ℤ) := by
    rw [h1.symm, ← hcval 𝔭.1 𝔭.2]
  exact Nat.cast_injective h3

end NK.HeckeL.Basic
