import Mathlib.Computability.Reduce
import Mathlib.RingTheory.Henselian
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Order.Star.Real
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
import Submission.NK.CFTLib.ARL.artinReciprocity_cyclotomic
import Submission.NK.CFTLib.Arl.artinSym_spanSingleton_eq_one_of_mem_congruence
import Submission.NK.CFTLib.ArtinReciprocityIdeal.Conductor
import Submission.NK.CFTLib.ArtinReciprocityIdeal.normRayLeKer
import Submission.Work.SSGRoute.ZDataMup.ArtinReciprocity.IdealModulus.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The principal ray of an ideal modulus is killed by the Artin symbol of a cyclotomic extension

`Work.SSGRoute.ZDataMup.ArtinReciprocity.IdealModulus.cycloPrincipalId`: for a cyclotomic
extension `Ω = k(ζ_n)` and an ideal modulus `𝔪` whose support contains all the primes dividing
`(n)` and whose level at those primes is at least that of `(n)`, the ideal-theoretic Artin symbol
kills the principal ray `P(𝔪) = principalRayId 𝔪`.

The mathematical content is the classical cyclotomic reciprocity law: the Artin symbol of a
principal ideal `(a)` with `a ≡ 1 mod* 𝔪` and `a` totally positive acts on `ζ_n` by the
`N_{k/ℚ}(a)`-th power, and `a ≡ 1 mod (n)` forces `N_{k/ℚ}(a) ≡ 1 mod n`; hence the symbol is
trivial on the generator `(ζ_n)` of `Ω/k`, so it is trivial altogether.

The formal development below runs the same route as `NK.CFTLib.ArtinReciprocityIdeal`'s
`cyclotomicKernelLe` for a natural-number modulus, but with the ramification hypothesis deleted
(the congruence of `CongrOneId 𝔪` at the primes `𝔭 | (n)` already forces the primes occurring in
`(a)` to be coprime to `(n)`, which is all that the Frobenius computation needs):

* `frobAtPrime_isFrobAtPrime`: the chosen `frobAtPrime p` is *unconditionally* a Frobenius element
  at `p` (the existing `NK.Chebotarev.isFrobAtPrime_frobAtPrime` needs unramifiedness of `p`);
* `artinSym_spanSingleton_integral_noRam`: `NK.CFTLib.Arl.artinSym_spanSingleton_integral` with the
  ramification hypothesis deleted;
* `artinSym_spanSingleton_congr_pos_noRam`: `NK.CFTLib.Arl.artinSym_spanSingleton_eq_one_of_congr_pos`
  with the ramification hypothesis deleted;
* `artinKillsPrincipal_cyclotomic`: the product form of the cyclotomic reciprocity law
  (`NK.CFTLib.ARL.artinReciprocity_cyclotomic`) at the modulus `n`;
* and then the reduction: a generator `(a)` of `principalRayId 𝔪` satisfies the congruence
  condition of `principalRay k n` because for `𝔭 | (n)` one has `𝔭 | 𝔪` (`hsupp`) and
  `exp (-(count 𝔭 𝔪)) ≤ v ((n:ℕ))` (`hlev`), so `le_trans` gives the `P(n)`-congruence; the
  Artin symbol is a homomorphism of the group of fractional ideals, so it suffices to kill
  generators.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open scoped NumberField nonZeroDivisors IsMulCommutative
open NumberField IsDedekindDomain
open NK.CFTLib.Arl
open NK.CFTLib.ArtinReciprocityIdeal

noncomputable section

namespace Work.SSGRoute.ZDataMup.ArtinReciprocity.IdealModulus

/-- **The chosen Frobenius element at a prime of the base field is a Frobenius element**, with no
unramifiedness hypothesis: `NK.Chebotarev.frobAtPrime p` is by definition the chosen element of the
always nonempty set of Frobenius elements at `p` (`NK.Chebotarev.exists_isFrobAtPrime`).

(The existing `NK.Chebotarev.isFrobAtPrime_frobAtPrime` is stated with the hypothesis that `p` is
unramified, which is not needed for this statement.) -/
lemma frobAtPrime_isFrobAtPrime {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L] (p : NK.Chebotarev.PrimeIdeal K) :
    NK.Chebotarev.IsFrobAtPrime (K := K) (L := L) p
      (NK.Chebotarev.frobAtPrime (K := K) (L := L) p) := by
  have h : ∃ σ : Gal(L/K), NK.Chebotarev.IsFrobAtPrime (K := K) (L := L) p σ :=
    NK.Chebotarev.exists_isFrobAtPrime (K := K) (L := L) p
  rw [NK.Chebotarev.frobAtPrime, dif_pos h]
  exact h.choose_spec

/-- The product of a list obtained by applying `f` to a `Finset` is the `Finset` product. -/
private lemma list_prod_map_eq_finset_prod {α β : Type*} [CommMonoid β] (s : Finset α)
    (f : α → β) : (s.toList.map f).prod = ∏ x ∈ s, f x := by
  rw [← Multiset.prod_coe, ← Multiset.map_coe, Finset.coe_toList, Finset.prod_eq_multiset_prod]

/-- **The Artin symbol of an integral principal ideal `(a)` with `a ≡ 1 mod (m)` and `a` totally
positive is trivial**, given the product form `hprinc` of the reciprocity law at the modulus `m`.

This is `NK.CFTLib.Arl.artinSym_spanSingleton_integral` with the ramification hypothesis deleted:
the only place where that hypothesis is used there is the deduction of
`IsFrobAtPrime p (frobAtPrime p)`, which holds unconditionally
(`frobAtPrime_isFrobAtPrime`).  The primes occurring in `(a)` are coprime to `(m)` because
`a ≡ 1 mod (m)` (`hmem`), which is a purely algebraic consequence of the congruence. -/
theorem artinSym_spanSingleton_integral_noRam {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (hcomm : ∀ a b : Gal(L/K), a * b = b * a) (m : ℕ) (hm : 0 < m)
    (hprinc : NK.CFTLib.artinKillsPrincipal K L m)
    (a : NumberField.RingOfIntegers K) (ha : a ≠ 0)
    (hcong : a - 1 ∈ Ideal.span {(m : NumberField.RingOfIntegers K)})
    (hpos : ∀ φ : K →+* ℝ, 0 < φ ((a : K))) :
    NK.CFTLib.Arl.artinSym (K := K) (L := L) hcomm
      (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers K)) (a : K)) = 1 := by
  classical
  have hR : (a : K) ≠ 0 := by
    intro h
    exact ha (RingOfIntegers.coe_injective (by simpa [RingOfIntegers.coe_eq_algebraMap] using h))
  set A : FractionalIdeal (nonZeroDivisors (𝓞 K)) K :=
    FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) (a : K) with hA
  have hAne : A ≠ 0 := by rw [hA, FractionalIdeal.spanSingleton_ne_zero_iff]; exact hR
  have hAcoe : A = (Ideal.span {a} : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) := by
    rw [hA, FractionalIdeal.coeIdeal_span_singleton, RingOfIntegers.coe_eq_algebraMap]
  have hI : Ideal.span {a} ≠ 0 := fun h => ha (Ideal.span_singleton_eq_bot.mp h)
  -- work with the commutative-monoid structure of `Gal(L/K)` used in `artinSym`
  letI galC : CommMonoid Gal(L/K) := galCommMonoid hcomm
  -- the exponent vector of the fractional ideal `(a)`, and its support
  set Z : HeightOneSpectrum (𝓞 K) →₀ ℤ := exps A with hZ
  have hZc : ∀ v, Z v = FractionalIdeal.count K v A := by intro v; rw [hZ, exps_apply]
  have hZnn : ∀ v, 0 ≤ Z v := by
    intro v
    rw [hZc v, hAcoe]
    exact FractionalIdeal.count_coe_nonneg K v (Ideal.span {a})
  -- `A` is the product of the primes in the support, to the powers `Z`
  have hfin : A = ∏ᶠ v : HeightOneSpectrum (𝓞 K),
      (v.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ^ (Z v) := by
    rw [← FractionalIdeal.finprod_heightOneSpectrum_factorization' (K := K) hAne]
    apply finprod_congr
    intro v
    rw [hZc]
  have hfins : ∏ᶠ v : HeightOneSpectrum (𝓞 K),
      (v.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ^ (Z v)
      = ∏ v ∈ Z.support, (v.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ^ (Z v) := by
    rw [finprod_eq_finsetProd_of_mulSupport_subset (s := Z.support)]
    intro v hv
    rw [Finset.mem_coe, Finsupp.mem_support_iff]
    intro hZ0
    rw [Function.mem_mulSupport] at hv
    exact hv (by rw [hZ0]; exact zpow_zero _)
  -- pass to ideals, with the natural-number exponents `(Z v).toNat`
  have hcoe : ∏ v ∈ Z.support, (v.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ^ (Z v)
      = ((∏ v ∈ Z.support, v.asIdeal ^ (Z v).toNat : Ideal (𝓞 K)) :
          FractionalIdeal (nonZeroDivisors (𝓞 K)) K) := by
    rw [← FractionalIdeal.coeIdealHom_apply (nonZeroDivisors (𝓞 K)) K
          (∏ v ∈ Z.support, v.asIdeal ^ (Z v).toNat),
        map_prod (FractionalIdeal.coeIdealHom (nonZeroDivisors (𝓞 K)) K)
          (fun v => v.asIdeal ^ (Z v).toNat) Z.support]
    apply Finset.prod_congr rfl
    intro v _
    rw [FractionalIdeal.coeIdealHom_apply, FractionalIdeal.coeIdeal_pow]
    conv_lhs => rw [← Int.toNat_of_nonneg (hZnn v)]
    rw [zpow_natCast]
  have hA' : A = ((∏ v ∈ Z.support, v.asIdeal ^ (Z v).toNat : Ideal (𝓞 K)) :
      FractionalIdeal (nonZeroDivisors (𝓞 K)) K) := by rw [hfin, hfins, hcoe]
  -- hence the ideal-theoretic factorisation of `(a)`
  have hideal : Ideal.span {a} = ∏ v ∈ Z.support, v.asIdeal ^ (Z v).toNat := by
    refine FractionalIdeal.coeIdeal_injective (K := K) ?_
    show (Ideal.span {a} : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) =
      ((∏ v ∈ Z.support, v.asIdeal ^ (Z v).toNat : Ideal (𝓞 K)) :
        FractionalIdeal (nonZeroDivisors (𝓞 K)) K)
    rw [← hAcoe, hA']
  -- no prime dividing `(a)` divides `(m)`
  have hmem : ∀ p ∈ Z.support, (m : 𝓞 K) ∉ p.asIdeal := by
    intro p hp hm_mem
    have hZne : Z p ≠ 0 := Finsupp.mem_support_iff.mp hp
    have hcnt : FractionalIdeal.count K p A ≠ 0 := by rw [← hZc p]; exact hZne
    rw [hAcoe] at hcnt
    have hcnt' : (Associates.mk p.asIdeal).count (Associates.mk (Ideal.span {a})).factors ≠ 0 := by
      have h2 := FractionalIdeal.count_coe K p hI
      rw [h2] at hcnt
      exact_mod_cast hcnt
    have hdvd : p.asIdeal ∣ Ideal.span {a} :=
      (Associates.count_ne_zero_iff_dvd (a := Ideal.span {a}) hI p.irreducible).mp hcnt'
    have hsub : a - 1 ∈ p.asIdeal :=
      (Ideal.span_singleton_le_iff_mem p.asIdeal).mpr hm_mem hcong
    have hone : (1 : 𝓞 K) ∈ p.asIdeal := by
      have := sub_mem ((Ideal.le_of_dvd hdvd) (Ideal.mem_span_singleton_self a)) hsub
      simpa using this
    exact p.isPrime.ne_top (Ideal.eq_top_iff_one p.asIdeal |>.mpr hone)
  -- the chosen Frobenius elements at these primes are genuine Frobenius elements
  have hfrob : ∀ p ∈ Z.support,
      NK.Chebotarev.IsFrobAtPrime (K := K) (L := L) p
        (NK.Chebotarev.frobAtPrime (K := K) (L := L) p) :=
    fun p _ => frobAtPrime_isFrobAtPrime (K := K) (L := L) p
  -- the reciprocity law applied to the factorisation of `(a)`
  have hprin : (Z.support.toList.map (fun p =>
      NK.Chebotarev.frobAtPrime (K := K) (L := L) p ^ (Z p).toNat)).prod = 1 :=
    hprinc a hcong hpos Z.support (fun p => (Z p).toNat)
      (fun p => NK.Chebotarev.frobAtPrime (K := K) (L := L) p) hmem hideal hfrob
  -- translate the Artin symbol into the same product
  have hmain : Z.prod (fun 𝔭 e => NK.Chebotarev.frobAtPrime (K := K) (L := L) 𝔭 ^ e) = 1 := by
    rw [Finsupp.prod_of_support_subset (f := Z) (s := Z.support) (le_refl _)
      (fun 𝔭 e => NK.Chebotarev.frobAtPrime (K := K) (L := L) 𝔭 ^ e)
      (fun i _ => zpow_zero _)]
    have heq : ∏ x ∈ Z.support, NK.Chebotarev.frobAtPrime (K := K) (L := L) x ^ Z x
        = ∏ x ∈ Z.support, NK.Chebotarev.frobAtPrime (K := K) (L := L) x ^ (Z x).toNat := by
      apply Finset.prod_congr rfl
      intro p _
      conv_lhs => rw [← Int.toNat_of_nonneg (hZnn p)]
      rw [zpow_natCast]
    rw [heq, ← list_prod_map_eq_finset_prod (Z.support)
      (fun p => NK.Chebotarev.frobAtPrime (K := K) (L := L) p ^ (Z p).toNat)]
    exact hprin
  rw [artinSym]
  exact hmain

/-- **The Artin symbol of the fractional principal ideal `(b)` with `b ≡ 1 mod* m` and `b` totally
positive is trivial**, given the product form `hprinc` of the reciprocity law at the modulus `m`.

This is `NK.CFTLib.Arl.artinSym_spanSingleton_eq_one_of_congr_pos` with the ramification hypothesis
deleted (see `artinSym_spanSingleton_integral_noRam`): the fractional case is reduced to the
integral case by the denominator trick
(`NK.CFTLib.Arl.exists_integral_denominator_of_congr`), which produces `n ≠ 0` and the integral
`c = b n²`, both `≡ 1 mod (m)` and totally positive, and uses the multiplicativity of `artinSym`. -/
theorem artinSym_spanSingleton_congr_pos_noRam {K L : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (hcomm : ∀ a b : Gal(L/K), a * b = b * a) (m : ℕ) (hm : 0 < m)
    (hprinc : NK.CFTLib.artinKillsPrincipal K L m)
    (b : Kˣ)
    (hcong : ∀ 𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      (m : NumberField.RingOfIntegers K) ∈ 𝔭.asIdeal →
        Valued.v (algebraMap K (𝔭.adicCompletion K) (b : K) - 1)
          ≤ Valued.v ((m : ℕ) : 𝔭.adicCompletion K))
    (hpos : ∀ (w : NumberField.InfinitePlace K) (hw : w.IsReal),
      0 < (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hw)
            (algebraMap K w.Completion (b : K))) :
    NK.CFTLib.Arl.artinSym (K := K) (L := L) hcomm
      (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers K)) (b : K)) = 1 := by
  classical
  obtain ⟨n, hn0, hn1, c, hc, hc1⟩ := exists_integral_denominator_of_congr (K := K) m hm b hcong
  have hnK : (n : K) ≠ 0 := fun h => hn0 (IsFractionRing.injective (𝓞 K) K (by simpa using h))
  have hbpos : ∀ φ : K →+* ℝ, 0 < φ ((b : K)) :=
    forall_ringHom_pos_of_forall_realPlace_pos (K := K) (b : K) hpos
  have hsq : ∀ φ : K →+* ℝ, 0 < φ ((n : K)) ^ 2 := fun φ =>
    sq_pos_of_ne_zero (fun h => hnK ((map_eq_zero φ).mp h))
  -- the two integral elements
  have hn2K : (((n ^ 2 : 𝓞 K)) : K) = (n : K) ^ 2 := by push_cast; ring
  have hn2ne : (n ^ 2 : 𝓞 K) ≠ 0 := pow_ne_zero 2 hn0
  have hn2cong : n ^ 2 - 1 ∈ Ideal.span {(m : 𝓞 K)} := by
    rw [show n ^ 2 - 1 = (n - 1) * (n + 1) by ring]
    exact Ideal.mul_mem_right (n + 1) (Ideal.span {(m : 𝓞 K)}) hn1
  have hn2pos : ∀ φ : K →+* ℝ, 0 < φ (((n ^ 2 : 𝓞 K)) : K) := by
    intro φ; rw [hn2K, map_pow]; exact hsq φ
  have hcne : c ≠ 0 := by
    intro h0
    have h1 : (c : K) = 0 := by rw [h0]; simp
    rw [hc] at h1
    exact mul_ne_zero (Units.ne_zero b) (pow_ne_zero 2 hnK) h1
  have hcpos : ∀ φ : K →+* ℝ, 0 < φ ((c : 𝓞 K) : K) := by
    intro φ; rw [hc, map_mul, map_pow]; exact mul_pos (hbpos φ) (hsq φ)
  -- the integral case for both
  have hI1 := artinSym_spanSingleton_integral_noRam (K := K) (L := L) hcomm m hm hprinc
    c hcne hc1 hcpos
  have hI2 := artinSym_spanSingleton_integral_noRam (K := K) (L := L) hcomm m hm hprinc
    (n ^ 2) hn2ne hn2cong hn2pos
  -- multiplicativity settles `(b) = (c)/(n²)`
  have hAne : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) ((b : K)) ≠ 0 :=
    FractionalIdeal.spanSingleton_ne_zero_iff.mpr (Units.ne_zero b)
  have hBne : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) (((n ^ 2 : 𝓞 K) : K)) ≠ 0 :=
    FractionalIdeal.spanSingleton_ne_zero_iff.mpr (by rw [hn2K]; exact pow_ne_zero 2 hnK)
  have hkey : artinSym (K := K) (L := L) hcomm
        (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) (b : K))
      * artinSym (K := K) (L := L) hcomm
        (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) (((n ^ 2 : 𝓞 K) : K))) = 1 := by
    rw [← artinSym_mul (K := K) (L := L) hcomm hAne hBne,
      FractionalIdeal.spanSingleton_mul_spanSingleton, hn2K, ← hc, hI1]
  rw [hI2, mul_one] at hkey
  exact hkey

/-- **The product form of the cyclotomic reciprocity law** at the modulus `n`: for the cyclotomic
extension `Ω = k(ζ_n)`, the Artin symbol kills every principal ideal `(a)` with `a ∈ 𝓞 k`,
`a ≡ 1 mod (n)` and `a` totally positive, for any choice of Frobenius elements.

This is `NK.CFTLib.ARL.artinReciprocity_cyclotomic` (the elementary base case: the symbol acts on
`ζ_n` by the `N_{k/ℚ}(a)`-th power, and `N_{k/ℚ}(a) ≡ 1 mod n`), unpacked as
`NK.CFTLib.artinKillsPrincipal`. -/
theorem artinKillsPrincipal_cyclotomic (k Ω : Type) [Field k] [NumberField k] [Field Ω]
    [NumberField Ω] [Algebra k Ω] [FiniteDimensional k Ω] [IsGalois k Ω] (n : ℕ) [NeZero n]
    [IsCyclotomicExtension {n} k Ω] : NK.CFTLib.artinKillsPrincipal k Ω n :=
  fun a ha hpos s e σ hs hfac hfrob =>
    NK.CFTLib.ARL.artinReciprocity_cyclotomic k Ω n a ha hpos s e σ hs hfac hfrob

theorem cycloPrincipalId (k Ω : Type) [Field k] [NumberField k] [Field Ω] [NumberField Ω]
    [Algebra k Ω] [FiniteDimensional k Ω] [IsGalois k Ω] [IsMulCommutative (Ω ≃ₐ[k] Ω)]
    (n : ℕ) [NeZero n] [IsCyclotomicExtension {n} k Ω]
    (𝔪 : Ideal (NumberField.RingOfIntegers k)) (h𝔪 : 𝔪 ≠ ⊥)
    (hsupp : ∀ 𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k),
      (n : NumberField.RingOfIntegers k) ∈ 𝔭.asIdeal →
        NK.CFTLib.ArtinReciprocityIdeal.DvdPrime 𝔪 𝔭)
    (hlev : ∀ 𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k),
      (n : NumberField.RingOfIntegers k) ∈ 𝔭.asIdeal →
      WithZero.exp
          (-(FractionalIdeal.count k 𝔭 (𝔪 : FractionalIdeal (nonZeroDivisors
            (NumberField.RingOfIntegers k)) k) : ℤ))
        ≤ Valued.v (R := 𝔭.adicCompletion k) (Γ₀ := WithZero (Multiplicative ℤ))
            (((n : ℕ) : 𝔭.adicCompletion k))) :
    ∀ A : NK.CFTLib.ArtinReciprocityIdeal.Frac k,
      A ∈ NK.CFTLib.ArtinReciprocityIdeal.principalRayId 𝔪 →
      NK.CFTLib.Arl.artinSym (K := k) (L := Ω)
        (fun a b : Ω ≃ₐ[k] Ω => IsMulCommutative.is_comm.comm a b) A = 1 := by
  intro A hA
  have hcomm : ∀ a b : Ω ≃ₐ[k] Ω, a * b = b * a :=
    fun a b => IsMulCommutative.is_comm.comm a b
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hprinc : NK.CFTLib.artinKillsPrincipal k Ω n := artinKillsPrincipal_cyclotomic k Ω n
  -- it suffices to kill the generators `(a)` with `a ≡ 1 mod* 𝔪`
  have hle : NK.CFTLib.ArtinReciprocityIdeal.principalRayId 𝔪 ≤
      (artinSymFracHom (K := k) (L := Ω) hcomm).ker := by
    rw [NK.CFTLib.ArtinReciprocityIdeal.principalRayId, Subgroup.closure_le]
    rintro A ⟨a, ha, rfl⟩
    show artinSymFracHom (K := k) (L := Ω) hcomm (spanUnit a) = 1
    rw [artinSymFracHom_apply, coe_spanUnit]
    -- the `𝔪`-congruence implies the `(n)`-congruence
    refine artinSym_spanSingleton_congr_pos_noRam (K := k) (L := Ω) hcomm n hn hprinc a
      (fun 𝔭 h𝔭 => le_trans (ha.1 𝔭 (hsupp 𝔭 h𝔭)) (hlev 𝔭 h𝔭)) ha.2
  have hmem : artinSymFracHom (K := k) (L := Ω) hcomm A = 1 := hle hA
  rwa [artinSymFracHom_apply] at hmem

end Work.SSGRoute.ZDataMup.ArtinReciprocity.IdealModulus
