import Mathlib
import Submission.NK.CFTLib.ArtinIdeal
import Submission.NK.CFTLib.ARL.norm_pos_of_totallyPositive
import Submission.NK.CFTLib.ARL.norm_sub_one_mem_span
import Submission.NK.CFTLib.ARL.isFrobAtPrime_zeta
import Submission.NK.CFTLib.ARL.autToPow_eq_of_pow_eq

/-! Guidance from the project lead (the requester):

# Guidance: Artin reciprocity for cyclotomic extensions (the elementary base case of `NK.CFTLib.ArtinReciprocityIdeal`)
L = K(ζ_n). For a prime p ∤ n of K, Frob_p acts on μ_n by ζ ↦ ζ^{N p} (N p = #(𝓞_K/p)): from `isFrobAt_def`
(σ x ≡ x^{N p} mod P) applied to x = ζ, and injectivity of μ_n → (𝓞_L/P)^× for P ∤ n. Galois elements are determined
by their action on ζ (`IsCyclotomicExtension` API: `autEquivPow`/`fromZetaAut`). So the product ∏ σ_p^{e_p} acts by
ζ ↦ ζ^{∏ N(p)^{e_p}} = ζ^{N((a))}, and N((a)) = |N_{K/ℚ}(a)| = N_{K/ℚ}(a) (totally positive ⇒ norm positive), and
a ≡ 1 mod n ⇒ N_{K/ℚ}(a) ≡ 1 mod n (norm is a product of conjugates, each ≡ 1 mod n in 𝓞 of the Galois closure; or
use `Algebra.norm` compatibility with the quotient ring). Mathlib: `Ideal.absNorm`, `Ideal.absNorm_span_singleton`,
`Algebra.norm_apply`, `IsPrimitiveRoot`. Statement check: K = ℚ, n = 5, a = 11.
-/

namespace NK.CFTLib.ARL

open NK.Chebotarev

/-- **Artin reciprocity for cyclotomic extensions, in the form needed by the ideal-theoretic
reciprocity law.**  Let `L = K(ζ_n)` be the `n`-th cyclotomic extension of a number field `K`
(`n ≥ 1`), let `a ∈ 𝓞 K` be totally positive and `≡ 1 mod n`, and let `(a) = ∏_{p ∈ s} p^{e p}` be
the prime ideal factorisation of its principal ideal, all `p ∈ s` being prime to `n`.  If `σ p` is
a Frobenius element at `p` for every `p ∈ s`, then `∏_{p ∈ s} σ p ^ (e p) = 1`.

This is the "trivial modulus" case of the reciprocity law for the cyclotomic character: the
Artin symbol of the principal ideal `(a)` acts on `ζ_n` by the `N_{K/ℚ}(a)`-th power, and
`N_{K/ℚ}(a) ≡ 1 mod n` because `a ≡ 1 mod n` and `a` is totally positive (so that the norm is
positive and hence equal to the absolute norm `#(𝓞 K ⧸ (a))`). -/
theorem artinReciprocity_cyclotomic (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L] (n : ℕ) [NeZero n] [IsCyclotomicExtension {n} K L]
    (a : NumberField.RingOfIntegers K) (ha : a - 1 ∈ Ideal.span {(n : NumberField.RingOfIntegers K)})
    (hpos : ∀ φ : K →+* ℝ, 0 < φ (a : K))
    (s : Finset (NK.Chebotarev.PrimeIdeal K)) (e : NK.Chebotarev.PrimeIdeal K → ℕ)
    (σ : NK.Chebotarev.PrimeIdeal K → (L ≃ₐ[K] L))
    (hs : ∀ p ∈ s, (n : NumberField.RingOfIntegers K) ∉ p.asIdeal)
    (hfac : Ideal.span {a} = ∏ p ∈ s, p.asIdeal ^ e p)
    (hfrob : ∀ p ∈ s, NK.Chebotarev.IsFrobAtPrime (L := L) p (σ p)) :
    (s.toList.map (fun p => σ p ^ e p)).prod = 1 := by
  classical
  -- ===== the cyclotomic character
  have hζ : IsPrimitiveRoot (IsCyclotomicExtension.zeta n K L) n :=
    IsCyclotomicExtension.zeta_spec n K L
  -- `χ` is the "power" character `ζ ↦ ζ ^ (χ σ)`; it is injective.
  let χ : Gal(L/K) →* (ZMod n)ˣ := hζ.autToPow K
  have hχinj : Function.Injective χ := IsPrimitiveRoot.autToPow_injective K hζ
  -- `ψ` is `χ` followed by the (injective on the level of the group) coercion into `ZMod n`;
  -- working with `ψ` makes the multiplicative bookkeeping a computation in the ring `ZMod n`.
  let ψ : Gal(L/K) →* ZMod n := (Units.coeHom (ZMod n)).comp χ
  have hψ : ∀ g, ψ g = ↑(χ g) := fun g => rfl
  -- ===== `a ≠ 0`
  have ha0 : a ≠ 0 := by
    intro h0
    have hprod : (∏ p ∈ s, p.asIdeal ^ e p) ≠ (⊥ : Ideal (NumberField.RingOfIntegers K)) := by
      rw [show (⊥ : Ideal (NumberField.RingOfIntegers K)) = 0 from rfl, Finset.prod_ne_zero_iff]
      intro p _
      exact pow_ne_zero _ p.ne_bot
    rw [h0, Set.singleton_zero, Ideal.span_zero] at hfac
    exact hprod hfac.symm
  -- ===== the norm of `a` is positive (total positivity) and `≡ 1 mod n`
  have hnormpos : 0 < Algebra.norm ℤ a := by
    have h1 : 0 < Algebra.norm ℚ (a : K) :=
      norm_pos_of_totallyPositive (a : K) (by exact_mod_cast ha0) hpos
    rw [← Algebra.coe_norm_int a] at h1
    exact_mod_cast h1
  have hnormmod : ((Algebra.norm ℤ a : ℤ) : ZMod n) = 1 := by
    have hdvd : (n : ℤ) ∣ Algebra.norm ℤ a - 1 :=
      Ideal.mem_span_singleton.mp (norm_sub_one_mem_span n a ha)
    have hmodeq : Algebra.norm ℤ a ≡ 1 [ZMOD (n : ℤ)] := by
      rw [Int.modEq_iff_dvd, ← neg_sub]
      exact dvd_neg.mpr hdvd
    rw [← Int.cast_one, ZMod.intCast_eq_intCast_iff]
    exact hmodeq
  -- ===== the exponent `Λ := ∏ p ∈ s, N(p) ^ e p` equals the (positive) norm of `a`
  have hcard : ∀ p : PrimeIdeal K,
      Nat.card (NumberField.RingOfIntegers K ⧸ p.asIdeal) = Ideal.absNorm p.asIdeal := by
    intro p
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have hΛZ : ((∏ p ∈ s, Nat.card (NumberField.RingOfIntegers K ⧸ p.asIdeal) ^ e p : ℕ) : ℤ)
      = Algebra.norm ℤ a := by
    have h1 : (∏ p ∈ s, Nat.card (NumberField.RingOfIntegers K ⧸ p.asIdeal) ^ e p : ℕ)
        = (Algebra.norm ℤ a).natAbs := by
      rw [← Ideal.absNorm_span_singleton a, hfac, map_prod]
      refine Finset.prod_congr rfl (fun p _ => ?_)
      rw [map_pow, hcard p]
    rw [h1, Int.natAbs_of_nonneg (le_of_lt hnormpos)]
  -- ===== the Frobenius at `p` acts on `ζ` by the `N(p)`-th power
  have hψσ : ∀ p ∈ s, ψ (σ p) = (Nat.card (NumberField.RingOfIntegers K ⧸ p.asIdeal) : ZMod n) := by
    intro p hp
    rw [hψ]
    exact autToPow_eq_of_pow_eq hζ (σ p) _
      (isFrobAtPrime_zeta n p (σ p) (hs p hp) (hfrob p hp))
  -- ===== consequently the product acts on `ζ` by the `Λ`-th power, and `Λ ≡ 1 mod n`
  have hψprod : ψ ((s.toList.map (fun p => σ p ^ e p)).prod)
      = ∏ p ∈ s, (Nat.card (NumberField.RingOfIntegers K ⧸ p.asIdeal) : ZMod n) ^ e p := by
    rw [map_list_prod]
    rw [show (List.map (⇑ψ) (List.map (fun p => σ p ^ e p) s.toList)).prod
        = ∏ p ∈ s, (⇑ψ ∘ fun p => σ p ^ e p) p from by simp]
    exact Finset.prod_congr rfl (fun p hp => by rw [Function.comp_apply, map_pow, hψσ p hp])
  have hcast : (∏ p ∈ s, (Nat.card (NumberField.RingOfIntegers K ⧸ p.asIdeal) : ZMod n) ^ e p)
      = ((∏ p ∈ s, Nat.card (NumberField.RingOfIntegers K ⧸ p.asIdeal) ^ e p : ℕ) : ZMod n) := by
    rw [Nat.cast_prod]
    exact Finset.prod_congr rfl (fun _ _ => by rw [Nat.cast_pow])
  have hχprod : χ ((s.toList.map (fun p => σ p ^ e p)).prod) = 1 := by
    apply Units.ext
    show (↑(χ ((s.toList.map (fun p => σ p ^ e p)).prod)) : ZMod n) = 1
    rw [← hψ, hψprod, hcast, ← Int.cast_natCast, hΛZ]
    exact hnormmod
  -- ===== the character is injective, so the product is trivial
  exact hχinj (by rw [hχprod, map_one])

end NK.CFTLib.ARL
