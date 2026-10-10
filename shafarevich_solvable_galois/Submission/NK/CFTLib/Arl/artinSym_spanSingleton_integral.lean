import Mathlib.Computability.Reduce
import Mathlib.RingTheory.Henselian
import Mathlib.Basic.Real.Basic
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.NK.CFTLib.Arl.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The Artin symbol of a principal ideal `(a)` with `a ≡ 1 mod m` and `a` totally positive

Let `L/K` be a finite abelian Galois extension of number fields, `m > 0` an integer whose
prime divisors are unramified in `L`, and suppose the ideal-theoretic reciprocity law
`hprinc` holds: for an algebraic integer `a ∈ 𝓞 K` with `a ≡ 1 mod (m)` and `a` positive at
every real place, and for any factorisation `(a) = ∏_{p ∈ s} p^{e p}` of the principal ideal
into primes `p` not dividing `(m)`, the product `∏_{p ∈ s} Frob_p^{e p}` of Frobenius elements
is trivial.

We deduce the corresponding statement for the Artin symbol of the *fractional* ideal
`(a) = spanSingleton (𝓞 K)⁰ (a : K)`:

`artinSym hcomm (spanSingleton (𝓞 K)⁰ (a : K)) = 1`.

The proof is a translation: the exponent of a prime `p` in `(a)` is the multiplicity of `p`,
i.e. `count K p (a)`, and this is exactly the value of the exponent vector `exps` used in the
definition of `artinSym`.  Since `a ≡ 1 mod (m)`, no prime `p | (a)` divides `(m)`, so the
hypothesis of `hprinc` applies to every prime in the support.

## Main result

* `NK.CFTLib.Arl.artinSym_spanSingleton_integral`
-/

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open scoped NumberField nonZeroDivisors
open NumberField IsDedekindDomain

noncomputable section

namespace NK.CFTLib.Arl

/-- The product of a list obtained by applying `f` to a `Finset` is the `Finset` product. -/
private lemma list_prod_map_eq_finset_prod {α β : Type*} [CommMonoid β] (s : Finset α)
    (f : α → β) : (s.toList.map f).prod = ∏ x ∈ s, f x := by
  rw [← Multiset.prod_coe, ← Multiset.map_coe, Finset.coe_toList, Finset.prod_eq_multiset_prod]

theorem artinSym_spanSingleton_integral {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (hcomm : ∀ a b : Gal(L/K), a * b = b * a) (m : ℕ) (hm : 0 < m)
    (hram : ∀ 𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      (m : NumberField.RingOfIntegers K) ∉ 𝔭.asIdeal →
      Ideal.ramificationIdxIn 𝔭.asIdeal (NumberField.RingOfIntegers L) = 1)
    (hprinc : ∀ (a : NumberField.RingOfIntegers K),
      a - 1 ∈ Ideal.span {(m : NumberField.RingOfIntegers K)} →
      (∀ φ : K →+* ℝ, 0 < φ ((a : K))) →
      ∀ (s : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
        (e : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) → ℕ)
        (σ : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) → Gal(L/K)),
        (∀ p ∈ s, (m : NumberField.RingOfIntegers K) ∉ p.asIdeal) →
        Ideal.span {a} = ∏ p ∈ s, p.asIdeal ^ e p →
        (∀ p ∈ s, NK.Chebotarev.IsFrobAtPrime (L := L) p (σ p)) →
        (s.toList.map (fun p => σ p ^ e p)).prod = 1)
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
        (NK.Chebotarev.frobAtPrime (K := K) (L := L) p) := by
    intro p hp
    refine NK.Chebotarev.isFrobAtPrime_frobAtPrime hcomm p (fun P hP => ?_)
    have h1 : Ideal.ramificationIdxIn p.asIdeal (𝓞 L) = 1 := hram p (hmem p hp)
    haveI : P.asIdeal.IsPrime := P.isPrime
    haveI : P.asIdeal.LiesOver p.asIdeal := hP
    rw [← Ideal.ramificationIdxIn_eq_ramificationIdx (A := 𝓞 K) (B := 𝓞 L) p.asIdeal P.asIdeal
      (Gal(L/K))]
    exact h1
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

end NK.CFTLib.Arl
