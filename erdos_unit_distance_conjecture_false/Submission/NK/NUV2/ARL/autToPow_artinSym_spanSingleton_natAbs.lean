import Mathlib
import Submission.NK.CFTLib.Arl.Defs
import Submission.NK.CFTLib.Arl.exists_monoidHom_ideleArtin
import Submission.NK.CFTLib.ARL.isFrobAtPrime_zeta
import Submission.NK.CFTLib.ARL.autToPow_eq_of_pow_eq
import Submission.NK.NUV2.ARL.Gap.isUnramified_cyclotomicExtension

/-!
# The cyclotomic character of the Artin symbol of a principal ideal

Let `L = K(ζ_q)` be the `q`-th cyclotomic extension of the number field `K` (`q` a rational
prime) and let `c ∈ 𝓞 K` be a nonzero algebraic integer whose prime divisors all avoid `(q)`,
i.e. all the primes occurring in the factorisation of the principal ideal `(c)` are unramified
in `L/K`.

The cyclotomic character `χ : Gal(L/K) → (ZMod q)ˣ`, `χ(σ) = a` where `σ(ζ_q) = ζ_q ^ a`, is
the `q`-adic component of the reciprocity map of `K`.  For the Artin symbol of the principal
fractional ideal `(c)` it is given by the absolute norm of `c`:

`χ (artinSym (c)) = |N_{K/ℚ} c|  (mod q)`.

This is the norm compatibility of the Artin symbol with the cyclotomic character: the Artin
symbol of a prime `𝔭` not dividing `q` raises `ζ_q` to the `N𝔭`-th power, and the product of
the `N𝔭` over the factorisation of `(c)` is exactly `|N_{K/ℚ} c|`.

## Main result

* `NK.NUV2.ARL.autToPow_artinSym_spanSingleton_natAbs`
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open NumberField IsDedekindDomain
open scoped NumberField nonZeroDivisors

noncomputable section

namespace NK.NUV2.ARL

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

/-- **A Frobenius at an unramified prime raises `ζ_q` to the `N𝔭`-th power.**  Formulated for the
chosen Frobenius element `NK.Chebotarev.frobAtPrime 𝔭` and read in the cyclotomic character
`autToPow`. -/
lemma autToPow_frobAtPrime_eq_absNorm_zmod (q : ℕ) [Fact q.Prime]
    [IsCyclotomicExtension {q} K L] (𝔭 : NK.Chebotarev.PrimeIdeal K)
    (hs : (q : 𝓞 K) ∉ 𝔭.asIdeal) :
    ((IsPrimitiveRoot.autToPow K (IsCyclotomicExtension.zeta_spec q K L)
      (NK.Chebotarev.frobAtPrime (K := K) (L := L) 𝔭) : (ZMod q)ˣ) : ZMod q)
      = (Ideal.absNorm 𝔭.asIdeal : ZMod q) := by
  classical
  have hfrob : NK.Chebotarev.IsFrobAtPrime (K := K) (L := L) 𝔭
      (NK.Chebotarev.frobAtPrime (K := K) (L := L) 𝔭) := by
    rw [NK.Chebotarev.frobAtPrime,
      dif_pos (NK.Chebotarev.exists_isFrobAtPrime (K := K) (L := L) 𝔭)]
    exact (NK.Chebotarev.exists_isFrobAtPrime (K := K) (L := L) 𝔭).choose_spec
  have hpow := NK.CFTLib.ARL.isFrobAtPrime_zeta (K := K) (L := L) q 𝔭
    (NK.Chebotarev.frobAtPrime (K := K) (L := L) 𝔭) hs hfrob
  have h := NK.CFTLib.ARL.autToPow_eq_of_pow_eq (K := K) (IsCyclotomicExtension.zeta_spec q K L)
    (NK.Chebotarev.frobAtPrime (K := K) (L := L) 𝔭) (Nat.card (𝓞 K ⧸ 𝔭.asIdeal)) hpow
  rw [h, Ideal.absNorm_apply, Submodule.cardQuot_apply]

/-- **The product of the norms of the prime divisors of `(c)` is `|N_{K/ℚ} c|`.**  The exponents
are the multiplicities of the primes in the fractional ideal `(c) = spanSingleton 𝓞⁰ (c : K)`,
i.e. the exponent vector `exps` used in the definition of `artinSym`. -/
lemma prod_absNorm_exps_eq_natAbs_zmod (q : ℕ) [Fact q.Prime]
    (c : 𝓞 K) (hc : c ≠ 0) :
    ∏ 𝔭 ∈ (NK.CFTLib.Arl.exps (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K))
      (c : K))).support,
        (Ideal.absNorm 𝔭.asIdeal : ZMod q) ^
          ((NK.CFTLib.Arl.exps (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K))
            (c : K))) 𝔭)
      = ((Algebra.norm ℤ c).natAbs : ZMod q) := by
  classical
  set A : FractionalIdeal (nonZeroDivisors (𝓞 K)) K :=
    FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) (c : K) with hA
  set Z : HeightOneSpectrum (𝓞 K) →₀ ℤ := NK.CFTLib.Arl.exps A with hZ
  have hR : (c : K) ≠ 0 := fun h => hc (RingOfIntegers.coe_injective (by
    simpa [RingOfIntegers.coe_eq_algebraMap] using h))
  have hAne : A ≠ 0 := by rw [hA, FractionalIdeal.spanSingleton_ne_zero_iff]; exact hR
  have hAcoe : A = (Ideal.span {c} : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) := by
    rw [hA, FractionalIdeal.coeIdeal_span_singleton, RingOfIntegers.coe_eq_algebraMap]
  have hI : Ideal.span {c} ≠ 0 := fun h => hc (Ideal.span_singleton_eq_bot.mp h)
  have hZc : ∀ v, Z v = FractionalIdeal.count K v A := by
    intro v; rw [hZ, NK.CFTLib.Arl.exps_apply]
  have hZnn : ∀ v, 0 ≤ Z v := by
    intro v
    rw [hZc v, hAcoe]
    exact FractionalIdeal.count_coe_nonneg K v (Ideal.span {c})
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
  have hideal : Ideal.span {c} = ∏ v ∈ Z.support, v.asIdeal ^ (Z v).toNat := by
    refine FractionalIdeal.coeIdeal_injective (K := K) ?_
    show (Ideal.span {c} : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) =
      ((∏ v ∈ Z.support, v.asIdeal ^ (Z v).toNat : Ideal (𝓞 K)) :
        FractionalIdeal (nonZeroDivisors (𝓞 K)) K)
    rw [← hAcoe, hA']
  have habs : ∏ v ∈ Z.support, (Ideal.absNorm v.asIdeal) ^ (Z v).toNat
      = (Algebra.norm ℤ c).natAbs := by
    rw [← Ideal.absNorm_span_singleton c, hideal, map_prod]
    apply Finset.prod_congr rfl
    intro v hv
    rw [map_pow]
  calc ∏ 𝔭 ∈ Z.support, (Ideal.absNorm 𝔭.asIdeal : ZMod q) ^ (Z 𝔭)
      = ∏ 𝔭 ∈ Z.support, (((Ideal.absNorm 𝔭.asIdeal) ^ (Z 𝔭).toNat : ℕ) : ZMod q) := by
        apply Finset.prod_congr rfl
        intro 𝔭 h𝔭
        rw [← Int.toNat_of_nonneg (hZnn 𝔭), zpow_natCast]
        exact (Nat.cast_pow _ _).symm
    _ = ((∏ 𝔭 ∈ Z.support, (Ideal.absNorm 𝔭.asIdeal) ^ (Z 𝔭).toNat : ℕ) : ZMod q) := by
        rw [Nat.cast_prod]
    _ = ((Algebra.norm ℤ c).natAbs : ZMod q) := by rw [habs]

theorem autToPow_artinSym_spanSingleton_natAbs {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L] (q : ℕ) [Fact q.Prime] [IsCyclotomicExtension {q} K L] (hcomm : ∀ a b : Gal(L/K), a * b = b * a) (c : NumberField.RingOfIntegers K) (hc : c ≠ 0) (hcop : ∀ p : NK.Chebotarev.PrimeIdeal K, p.asIdeal ∣ Ideal.span {c} → (q : NumberField.RingOfIntegers K) ∉ p.asIdeal) : ((IsPrimitiveRoot.autToPow K (IsCyclotomicExtension.zeta_spec q K L) (NK.CFTLib.Arl.artinSym hcomm (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers K)) (c : K))) : (ZMod q)ˣ) : ZMod q) = ((Algebra.norm ℤ c).natAbs : ZMod q) := by
  classical
  set A : FractionalIdeal (nonZeroDivisors (𝓞 K)) K :=
    FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) (c : K) with hA
  set Z : HeightOneSpectrum (𝓞 K) →₀ ℤ := NK.CFTLib.Arl.exps A with hZ
  have hR : (c : K) ≠ 0 := fun h => hc (RingOfIntegers.coe_injective (by
    simpa [RingOfIntegers.coe_eq_algebraMap] using h))
  have hAcoe : A = (Ideal.span {c} : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) := by
    rw [hA, FractionalIdeal.coeIdeal_span_singleton, RingOfIntegers.coe_eq_algebraMap]
  have hI : Ideal.span {c} ≠ 0 := fun h => hc (Ideal.span_singleton_eq_bot.mp h)
  have hZc : ∀ v, Z v = FractionalIdeal.count K v A := by
    intro v; rw [hZ, NK.CFTLib.Arl.exps_apply]
  have hdiv : ∀ 𝔭 ∈ Z.support, 𝔭.asIdeal ∣ Ideal.span {c} := by
    intro 𝔭 h𝔭
    have hZne : Z 𝔭 ≠ 0 := Finsupp.mem_support_iff.mp h𝔭
    have hcnt : FractionalIdeal.count K 𝔭 A ≠ 0 := by rw [← hZc 𝔭]; exact hZne
    rw [hAcoe] at hcnt
    have hcnt' : (Associates.mk 𝔭.asIdeal).count
        (Associates.mk (Ideal.span {c})).factors ≠ 0 := by
      have h2 := FractionalIdeal.count_coe K 𝔭 hI
      rw [h2] at hcnt
      exact_mod_cast hcnt
    exact (Associates.count_ne_zero_iff_dvd (a := Ideal.span {c}) hI 𝔭.irreducible).mp hcnt'
  have hprime : ∀ 𝔭 ∈ Z.support, (q : 𝓞 K) ∉ 𝔭.asIdeal := fun 𝔭 h𝔭 => hcop 𝔭 (hdiv 𝔭 h𝔭)
  let galC : CommMonoid Gal(L/K) := NK.CFTLib.Arl.galCommMonoid hcomm
  let φ : Gal(L/K) →* ZMod q := (Units.coeHom (ZMod q)).comp
    (IsPrimitiveRoot.autToPow K (IsCyclotomicExtension.zeta_spec q K L))
  have hchar : ∀ 𝔭 ∈ Z.support, φ (NK.Chebotarev.frobAtPrime (K := K) (L := L) 𝔭)
      = (Ideal.absNorm 𝔭.asIdeal : ZMod q) := by
    intro 𝔭 h𝔭
    exact autToPow_frobAtPrime_eq_absNorm_zmod (K := K) (L := L) q 𝔭 (hprime 𝔭 h𝔭)
  have hstep : φ (NK.CFTLib.Arl.artinSym hcomm A)
      = ∏ 𝔭 ∈ Z.support, (Ideal.absNorm 𝔭.asIdeal : ZMod q) ^ (Z 𝔭) := by
    rw [NK.CFTLib.Arl.artinSym]
    rw [Finsupp.prod_of_support_subset (f := Z) (s := Z.support) (le_refl _)
      (g := fun 𝔭 e => (NK.Chebotarev.frobAtPrime (K := K) (L := L) 𝔭) ^ e)
      (fun i _ => zpow_zero _)]
    rw [map_prod]
    apply Finset.prod_congr rfl
    intro 𝔭 h𝔭
    rw [map_zpow, hchar 𝔭 h𝔭]
  change φ (NK.CFTLib.Arl.artinSym hcomm A) = ((Algebra.norm ℤ c).natAbs : ZMod q)
  rw [hstep]
  simpa only [hZ, hA] using prod_absNorm_exps_eq_natAbs_zmod (K := K) q c hc

end NK.NUV2.ARL
