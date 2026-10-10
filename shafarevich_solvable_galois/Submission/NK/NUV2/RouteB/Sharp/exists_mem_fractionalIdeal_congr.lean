import Mathlib.RingTheory.Henselian
import Mathlib.Tactic.Have
import Mathlib.Data.Int.Star
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Order.Ring.Star
import Submission.NK.NUV2.RouteB.Sharp.ModData
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false

open NumberField IsDedekindDomain
open scoped NumberField nonZeroDivisors BigOperators

namespace NK.NUV2.RouteB.Sharp

variable {K : Type*} [Field K] [NumberField K]

/-! ## Two lemmas on `count`s

The main input for the whole file is the following elementary order-theoretic fact about
`FractionalIdeal.count`: a nonzero fractional ideal whose counts are all `≤ 0` contains the ring
of integers.  We prove it by way of the corresponding statement for integral ideals. -/

/-- The `q`-adic `count` of an integral ideal is the multiplicity of `q` in its factorisation. -/
lemma count_coe_eq_count_normalizedFactors {I : Ideal (𝓞 K)} (hI : I ≠ 0)
    (v : HeightOneSpectrum (𝓞 K)) :
    FractionalIdeal.count K v (I : FractionalIdeal (𝓞 K)⁰ K)
      = (Multiset.count v.asIdeal (UniqueFactorizationMonoid.normalizedFactors I) : ℤ) := by
  rw [FractionalIdeal.count_coe K v hI,
    Ideal.count_associates_factors_eq hI v.isPrime v.ne_bot]

/-- An integral ideal is contained in another one as soon as its `count`s are at least as large. -/
lemma ideal_le_of_count_le {I J : Ideal (𝓞 K)} (hI : I ≠ 0) (hJ : J ≠ 0)
    (h : ∀ v : HeightOneSpectrum (𝓞 K),
      FractionalIdeal.count K v (J : FractionalIdeal (𝓞 K)⁰ K)
        ≤ FractionalIdeal.count K v (I : FractionalIdeal (𝓞 K)⁰ K)) :
    I ≤ J := by
  rw [← Ideal.dvd_iff_le,
    UniqueFactorizationMonoid.dvd_iff_normalizedFactors_le_normalizedFactors hJ hI,
    Multiset.le_iff_count]
  intro q
  by_cases hq : q ∈ UniqueFactorizationMonoid.normalizedFactors J
  · have hqprime : Prime q := UniqueFactorizationMonoid.prime_of_normalized_factor q hq
    have hqne : q ≠ ⊥ := by
      simpa only [Ideal.zero_eq_bot] using hqprime.ne_zero
    have hv := h ⟨q, Ideal.isPrime_of_prime hqprime, hqne⟩
    rw [count_coe_eq_count_normalizedFactors hJ ⟨q, Ideal.isPrime_of_prime hqprime, hqne⟩,
      count_coe_eq_count_normalizedFactors hI ⟨q, Ideal.isPrime_of_prime hqprime, hqne⟩] at hv
    exact_mod_cast hv
  · rw [Multiset.count_eq_zero_of_notMem hq]
    exact Nat.zero_le _

/-- A nonzero fractional ideal all of whose `count`s are non-positive contains the ring of
integers. -/
lemma one_le_of_count_nonpos {M : FractionalIdeal (𝓞 K)⁰ K} (hM : M ≠ 0)
    (h : ∀ q : HeightOneSpectrum (𝓞 K), FractionalIdeal.count K q M ≤ 0) :
    (1 : FractionalIdeal (𝓞 K)⁰ K) ≤ M := by
  classical
  have hden_ne : ((M.den : 𝓞 K)) ≠ 0 := nonZeroDivisors.coe_ne_zero M.den
  have hmap_ne : algebraMap (𝓞 K) K (M.den : 𝓞 K) ≠ 0 := by simpa using hden_ne
  have hnum_ne : M.num ≠ 0 := fun hz => hM (FractionalIdeal.num_eq_zero_iff.mp hz)
  have hspan_ne : (Ideal.span {(M.den : 𝓞 K)} : Ideal (𝓞 K)) ≠ 0 := by
    simpa [Ideal.span_singleton_eq_bot] using hden_ne
  have hcount : ∀ v : HeightOneSpectrum (𝓞 K),
      FractionalIdeal.count K v (M.num : FractionalIdeal (𝓞 K)⁰ K)
        ≤ FractionalIdeal.count K v ((Ideal.span {(M.den : 𝓞 K)} : Ideal (𝓞 K)) :
            FractionalIdeal (𝓞 K)⁰ K) := by
    intro v
    have h1 : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K))
        (algebraMap (𝓞 K) K (M.den : 𝓞 K)) ≠ 0 :=
      FractionalIdeal.spanSingleton_ne_zero_iff.mpr hmap_ne
    calc FractionalIdeal.count K v (M.num : FractionalIdeal (𝓞 K)⁰ K)
        = FractionalIdeal.count K v (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K))
            (algebraMap (𝓞 K) K (M.den : 𝓞 K)) * M) := by
          rw [FractionalIdeal.den_mul_self_eq_num']
      _ = FractionalIdeal.count K v (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K))
            (algebraMap (𝓞 K) K (M.den : 𝓞 K))) + FractionalIdeal.count K v M :=
          FractionalIdeal.count_mul K v h1 hM
      _ ≤ FractionalIdeal.count K v (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K))
            (algebraMap (𝓞 K) K (M.den : 𝓞 K))) := by
          have := h v
          linarith
      _ = FractionalIdeal.count K v ((Ideal.span {(M.den : 𝓞 K)} : Ideal (𝓞 K)) :
            FractionalIdeal (𝓞 K)⁰ K) := by
          rw [FractionalIdeal.coeIdeal_span_singleton]
  have hle_ideal : Ideal.span {(M.den : 𝓞 K)} ≤ M.num :=
    ideal_le_of_count_le hspan_ne hnum_ne hcount
  have hcoe : ((Ideal.span {(M.den : 𝓞 K)} : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)
      ≤ (M.num : FractionalIdeal (𝓞 K)⁰ K) :=
    (FractionalIdeal.coeIdeal_le_coeIdeal (K := K)).mpr hle_ideal
  have hle : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K))
        (algebraMap (𝓞 K) K (M.den : 𝓞 K))
      ≤ FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K))
        (algebraMap (𝓞 K) K (M.den : 𝓞 K)) * M := by
    calc FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K))
          (algebraMap (𝓞 K) K (M.den : 𝓞 K))
        = ((Ideal.span {(M.den : 𝓞 K)} : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) := by
          rw [FractionalIdeal.coeIdeal_span_singleton]
      _ ≤ (M.num : FractionalIdeal (𝓞 K)⁰ K) := hcoe
      _ = FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K))
            (algebraMap (𝓞 K) K (M.den : 𝓞 K)) * M :=
          (FractionalIdeal.den_mul_self_eq_num' (nonZeroDivisors (𝓞 K)) K M).symm
  set A : FractionalIdeal (𝓞 K)⁰ K := FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K))
    (algebraMap (𝓞 K) K (M.den : 𝓞 K)) with hA
  have hle' : A ≤ A * M := by
    rw [hA]; exact hle
  have h2 : (A * M) * A⁻¹ = M := by
    rw [mul_comm (A * M) A⁻¹, ← mul_assoc]
    rw [show A⁻¹ * A = 1 from by
      rw [hA]; exact FractionalIdeal.spanSingleton_inv_mul (K := K) hmap_ne]
    rw [one_mul]
  calc (1 : FractionalIdeal (𝓞 K)⁰ K) = A * A⁻¹ := by
        rw [hA]; exact (FractionalIdeal.spanSingleton_mul_inv (K := K) hmap_ne).symm
    _ ≤ (A * M) * A⁻¹ := mul_le_mul_left hle' A⁻¹
    _ = M := h2

/-! ## The ideal of a modulus and its counts -/

/-- The coercion `Ideal R → FractionalIdeal R⁰ L` is multiplicative over finite products. -/
lemma coeIdeal_finset_prod {ι : Type*} (s : Finset ι) (f : ι → Ideal (𝓞 K)) :
    ((∏ i ∈ s, f i : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)
      = ∏ i ∈ s, (f i : FractionalIdeal (𝓞 K)⁰ K) := by
  classical
  induction s using Finset.induction with
  | empty => simp [FractionalIdeal.coeIdeal_top]
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.prod_insert ha, FractionalIdeal.coeIdeal_mul, ih]

/-- Every factor appears in the product of the powers of the primes of a finite set. -/
lemma finset_prod_le_pow_of_mem (m : HeightOneSpectrum (𝓞 K) → ℕ)
    (S : Finset (HeightOneSpectrum (𝓞 K))) {q : HeightOneSpectrum (𝓞 K)} (hq : q ∈ S) :
    (∏ q' ∈ S, q'.asIdeal ^ (m q') : Ideal (𝓞 K)) ≤ q.asIdeal ^ (m q) := by
  classical
  rw [← Finset.insert_erase hq, Finset.prod_insert (Finset.notMem_erase q S)]
  exact Ideal.mul_le_left

/-! ## The main lemma -/

theorem exists_mem_fractionalIdeal_congr (K : Type) [Field K] [NumberField K]
    (m : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) → ℕ)
    (hm : NK.NUV2.RouteB.Sharp.HasFiniteSupport K m)
    (𝔡 : FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K) (h𝔡 : 𝔡 ≠ 0)
    (hcop : ∀ q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      m q ≠ 0 → FractionalIdeal.count K q 𝔡 = 0)
    (β : NumberField.RingOfIntegers K) :
    ∃ δ : K, δ ∈ (𝔡 : Set K) ∧
      ∀ q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
        m q ≠ 0 → Valued.v (algebraMap K (q.adicCompletion K) (δ - (β : K)))
          ≤ WithZero.exp (-(m q : ℤ)) := by
  classical
  set S : Finset (HeightOneSpectrum (𝓞 K)) := (Filter.eventually_cofinite.mp hm).toFinset with hS
  have hSmem : ∀ q : HeightOneSpectrum (𝓞 K), q ∈ S ↔ m q ≠ 0 := by
    intro q
    rw [hS, Set.Finite.mem_toFinset]
    rfl
  set J : Ideal (𝓞 K) := ∏ q ∈ S, q.asIdeal ^ (m q) with hJ
  have hJ_ne : J ≠ 0 := by
    rw [hJ, Finset.prod_ne_zero_iff]
    intro q _
    exact pow_ne_zero _ q.ne_bot
  have hJneF : ((J : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.mpr hJ_ne
  -- the `count`s of `J` vanish away from `S`
  have hJcount : ∀ q : HeightOneSpectrum (𝓞 K), q ∉ S →
      FractionalIdeal.count K q ((J : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) = 0 := by
    intro q hq
    rw [hJ, coeIdeal_finset_prod]
    simp only [FractionalIdeal.coeIdeal_pow]
    rw [FractionalIdeal.count_prod K q S
      (fun q' : HeightOneSpectrum (𝓞 K) =>
        (q'.asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^ (m q')) _]
    · refine Finset.sum_eq_zero fun q' hq' => ?_
      rw [FractionalIdeal.count_pow, FractionalIdeal.count_maximal,
        if_neg (fun h : q' = q => hq (h ▸ hq')), mul_zero]
    · intro q' _
      exact pow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.mpr q'.ne_bot)
  -- the sum `𝔡 ⊔ J` has non-positive counts
  have hM_ne : 𝔡 ⊔ (J : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 := by
    intro hzero
    refine h𝔡 (le_antisymm ?_ zero_le)
    rw [← hzero]
    exact le_sup_left
  have hMcount : ∀ q : HeightOneSpectrum (𝓞 K),
      FractionalIdeal.count K q (𝔡 ⊔ (J : FractionalIdeal (𝓞 K)⁰ K)) ≤ 0 := by
    intro q
    have h1 : FractionalIdeal.count K q (𝔡 ⊔ (J : FractionalIdeal (𝓞 K)⁰ K))
        ≤ FractionalIdeal.count K q 𝔡 :=
      FractionalIdeal.count_mono K q h𝔡 le_sup_left
    have h2 : FractionalIdeal.count K q (𝔡 ⊔ (J : FractionalIdeal (𝓞 K)⁰ K))
        ≤ FractionalIdeal.count K q ((J : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) :=
      FractionalIdeal.count_mono K q hJneF le_sup_right
    by_cases hq : q ∈ S
    · have hzero : FractionalIdeal.count K q 𝔡 = 0 := hcop q ((hSmem q).mp hq)
      linarith
    · have hzero : FractionalIdeal.count K q
          ((J : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) = 0 := hJcount q hq
      linarith
  have hone : (1 : FractionalIdeal (𝓞 K)⁰ K) ≤ 𝔡 ⊔ (J : FractionalIdeal (𝓞 K)⁰ K) :=
    one_le_of_count_nonpos hM_ne hMcount
  have hβmem : (β : K) ∈ 𝔡 ⊔ (J : FractionalIdeal (𝓞 K)⁰ K) :=
    hone ((FractionalIdeal.mem_one_iff _).mpr ⟨β, rfl⟩)
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp hβmem
  obtain ⟨j, hj, hjz⟩ := (FractionalIdeal.mem_coeIdeal (nonZeroDivisors (𝓞 K))).mp hz
  refine ⟨y, hy, fun q hq => ?_⟩
  have hqS : q ∈ S := (hSmem q).mpr hq
  have hjmem : j ∈ q.asIdeal ^ (m q) := (finset_prod_le_pow_of_mem m S hqS)
    (by rw [← hJ]; exact hj)
  have hdiff : y - (β : K) = -(j : K) := by
    rw [← hyz, ← hjz]
    ring
  rw [hdiff, Commons.NumberTheory.NumberField.val_algebraMap_adicCompletion_eq,
    Valuation.map_neg, IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
  exact (IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_mem q j (m q)).mpr hjmem

end NK.NUV2.RouteB.Sharp
