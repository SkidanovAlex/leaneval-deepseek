import Mathlib.Computability.Reduce
import Mathlib.RingTheory.Henselian
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.NK.CFTLib.Arl.artinSym_spanSingleton_integral_of_hprinc
import Submission.NK.CFTLib.ArtinReciprocityIdeal.LangDefs
import Submission.NK.CFTLib.ArtinReciprocityIdeal.frobAtPrime_prod_relNorm_eq_one
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The ideal-theoretic and the fractional-ideal Artin symbols agree on principal ideals

For an abelian extension `L / K` of number fields, `m : ℕ` a modulus such that every ramified
prime divides `(m)`, and `a : 𝓞 K` with `a ≡ 1 mod (m)`, the ideal-theoretic Artin symbol of the
principal ideal `(a)` coincides with the fractional-ideal Artin symbol
`artinSym (spanSingleton 𝓞⁰ (a : K))` of `NK.CFTLib.Arl.Defs`.

The point is that `a ≡ 1 mod (m)` forces every prime occurring in `(a)` to be unramified, so the
"ignoring of ramified primes" in the ideal-theoretic symbol (`frobSymbol`) is immaterial, and both
symbols compute the same product `∏_{𝔭 | (a)} Frob_𝔭 ^ (count 𝔭 (a))`.
-/

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open scoped NumberField nonZeroDivisors IsMulCommutative
open NumberField IsDedekindDomain

noncomputable section

namespace NK.CFTLib.ArtinReciprocityIdeal

theorem artinSymbol_span_eq_artinSym_spanSingleton {K L : Type} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [IsMulCommutative (Gal(L/K))]
    (hcomm : ∀ a b : Gal(L/K), a * b = b * a) (m : ℕ)
    (hram : ∀ p : NK.Chebotarev.PrimeIdeal K,
      ¬ NK.CFTLib.ArtinReciprocityIdeal.IsUnramified (K := K) (L := L) p →
      (m : NumberField.RingOfIntegers K) ∈ p.asIdeal)
    (a : NumberField.RingOfIntegers K)
    (ha : a - 1 ∈ Ideal.span {(m : NumberField.RingOfIntegers K)}) :
    NK.CFTLib.ArtinReciprocityIdeal.artinSymbol (K := K) (L := L) (Ideal.span {a})
      = NK.CFTLib.Arl.artinSym (K := K) (L := L) hcomm
          (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers K)) (a : K)) := by
  classical
  by_cases ha0 : a = 0
  · -- degenerate case: `a = 0`; both symbols are trivial
    subst ha0
    have hL : artinSymbol (K := K) (L := L) (Ideal.span {(0 : 𝓞 K)}) = 1 := by
      rw [Ideal.span_singleton_eq_bot.mpr rfl]
      unfold artinSymbol
      rw [show UniqueFactorizationMonoid.normalizedFactors (⊥ : Ideal (𝓞 K)) = 0 from
        UniqueFactorizationMonoid.normalizedFactors_zero, Multiset.map_zero,
        Multiset.prod_zero]
    have hR : NK.CFTLib.Arl.artinSym (K := K) (L := L) hcomm
        (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) ((0 : 𝓞 K) : K)) = 1 := by
      rw [FractionalIdeal.spanSingleton_eq_zero_iff.mpr (by simp)]
      exact NK.CFTLib.Arl.artinSym_zero hcomm
    rw [hL, hR]
  · have hR : (a : K) ≠ 0 := by
      intro h
      exact ha0 (RingOfIntegers.coe_injective
        (by simpa [RingOfIntegers.coe_eq_algebraMap] using h))
    have hI : Ideal.span {a} ≠ 0 := fun h => ha0 (Ideal.span_singleton_eq_bot.mp h)
    set A : FractionalIdeal (nonZeroDivisors (𝓞 K)) K :=
      FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) (a : K) with hA
    have hAne : A ≠ 0 := by
      rw [hA, FractionalIdeal.spanSingleton_ne_zero_iff]; exact hR
    have hAcoe : A = (Ideal.span {a} : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) := by
      rw [hA, FractionalIdeal.coeIdeal_span_singleton, RingOfIntegers.coe_eq_algebraMap]
    -- work with the commutative-monoid structure of `Gal(L/K)` used in `artinSym`
    letI galC : CommMonoid Gal(L/K) := NK.CFTLib.Arl.galCommMonoid hcomm
    -- the exponent vector of `A` and its support
    set Z : HeightOneSpectrum (𝓞 K) →₀ ℤ := NK.CFTLib.Arl.exps A with hZ
    have hZc : ∀ v, Z v = FractionalIdeal.count K v A := by
      intro v; rw [hZ, NK.CFTLib.Arl.exps_apply]
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
    have hcoe : ∏ v ∈ Z.support,
          (v.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ^ (Z v)
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
        FractionalIdeal (nonZeroDivisors (𝓞 K)) K) := by
      rw [hfin, hfins, hcoe]
    -- hence the ideal-theoretic factorisation of `(a)`
    have hideal : Ideal.span {a} = ∏ v ∈ Z.support, v.asIdeal ^ (Z v).toNat := by
      refine FractionalIdeal.coeIdeal_injective (K := K) ?_
      show (Ideal.span {a} : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) =
        ((∏ v ∈ Z.support, v.asIdeal ^ (Z v).toNat : Ideal (𝓞 K)) :
          FractionalIdeal (nonZeroDivisors (𝓞 K)) K)
      rw [← hAcoe, hA']
    -- no prime dividing `(a)` divides `(m)`, because `a ≡ 1 mod (m)`
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
        (Ideal.span_singleton_le_iff_mem p.asIdeal).mpr hm_mem ha
      have hone : (1 : 𝓞 K) ∈ p.asIdeal := by
        have := sub_mem ((Ideal.le_of_dvd hdvd) (Ideal.mem_span_singleton_self a)) hsub
        simpa using this
      exact p.isPrime.ne_top (Ideal.eq_top_iff_one p.asIdeal |>.mpr hone)
    -- all these primes are unramified
    have hunr : ∀ p ∈ Z.support, IsUnramified (K := K) (L := L) p := by
      intro p hp
      by_contra h
      exact hmem p hp (hram p h)
    -- the ideal-theoretic symbol, computed on the factorisation of `(a)`
    have hLHS : artinSymbol (K := K) (L := L) (Ideal.span {a})
        = ∏ p ∈ Z.support, frobSymbol (K := K) (L := L) p.asIdeal ^ (Z p).toNat := by
      rw [hideal]
      exact artinSymbol_finset_prod Z.support (fun p => (Z p).toNat)
    -- the fractional-ideal symbol, computed on the same factorisation
    have hRHS : NK.CFTLib.Arl.artinSym (K := K) (L := L) hcomm A
        = ∏ p ∈ Z.support, frobSymbol (K := K) (L := L) p.asIdeal ^ (Z p).toNat := by
      rw [NK.CFTLib.Arl.artinSym]
      rw [Finsupp.prod_of_support_subset (f := Z) (s := Z.support) (le_refl _)
        (fun 𝔭 (e : ℤ) => NK.Chebotarev.frobAtPrime (K := K) (L := L) 𝔭 ^ e)
        (fun i _ => zpow_zero _)]
      have heq : ∏ x ∈ Z.support, NK.Chebotarev.frobAtPrime (K := K) (L := L) x ^ Z x
          = ∏ x ∈ Z.support,
              NK.Chebotarev.frobAtPrime (K := K) (L := L) x ^ (Z x).toNat := by
        apply Finset.prod_congr rfl
        intro p _
        conv_lhs => rw [← Int.toNat_of_nonneg (hZnn p)]
        rw [zpow_natCast]
      rw [heq]
      apply Finset.prod_congr rfl
      intro p hp
      rw [frobSymbol_eq (K := K) (L := L) p (hunr p hp)]
    rw [hLHS, hRHS]

end NK.CFTLib.ArtinReciprocityIdeal
