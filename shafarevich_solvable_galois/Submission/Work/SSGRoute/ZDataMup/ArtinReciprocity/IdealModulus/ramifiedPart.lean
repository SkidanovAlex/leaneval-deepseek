import Mathlib
import Submission.Work.SSGRoute.ZDataMup.ArtinReciprocity.IdealModulus.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The ramified part of a principal ideal modulus

For a finite Galois extension `L / K` of number fields and an integer `M > 1` such that every prime
of `K` not dividing `(M)` is unramified in `L`, this file produces an **ideal modulus**

  `𝔪 = ∏_{𝔭 ramified in L/K} 𝔭^{v_𝔭(M)}`

whose prime support is *exactly* the set of primes ramified in `L / K`, and whose `𝔭`-adic
valuations agree with those of the principal modulus `(M)` at every prime dividing it.

This is the ideal (as opposed to rational) modulus supported on the ramified primes that the Lang
conductor machinery for ideal moduli (`Submission/Work/.../IdealModulus/Defs.lean`) consumes; note
that `(M)` itself is in general *not* admissible as such a modulus, because an unramified prime may
still divide `(M)`.

## Main result

* `Work.SSGRoute.ZDataMup.ArtinReciprocity.IdealModulus.ramifiedPart`

## Implementation notes

The modulus is built as a `Finset.prod` over the (finite, by `Ideal.finite_factors`) set of ramified
primes of `𝔭.asIdeal ^ v_𝔭`, where `v_𝔭 = count K 𝔭 ((M) : FractionalIdeal _ K)`. The two counting
lemmas `ideal_le_iff_count_pos` and `count_finsetProd_prime_pow` reduce the support and valuation
statements to the bookkeeping of `FractionalIdeal.count` on prime powers.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped NumberField nonZeroDivisors
open IsDedekindDomain NumberField

namespace Work.SSGRoute.ZDataMup.ArtinReciprocity.IdealModulus

/-! ## Counting lemmas for prime powers of ideals -/

/-- For a nonzero ideal `𝔪` of a Dedekind domain and a height one prime `𝔭`, the ideal `𝔪` is
contained in `𝔭` if and only if the `𝔭`-adic multiplicity of `𝔪` is positive. -/
theorem ideal_le_iff_count_pos {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K]
    [Algebra R K] [IsFractionRing R K] {𝔪 : Ideal R} (h𝔪 : 𝔪 ≠ ⊥)
    (𝔭 : HeightOneSpectrum R) :
    𝔪 ≤ 𝔭.asIdeal ↔ 0 < FractionalIdeal.count K 𝔭 (𝔪 : FractionalIdeal (nonZeroDivisors R) K) := by
  classical
  constructor
  · intro h
    have h1 : FractionalIdeal.count K 𝔭 ((𝔭.asIdeal : Ideal R) : FractionalIdeal (nonZeroDivisors R) K) ≤
        FractionalIdeal.count K 𝔭 (𝔪 : FractionalIdeal (nonZeroDivisors R) K) :=
      FractionalIdeal.count_mono K 𝔭 (FractionalIdeal.coeIdeal_ne_zero.mpr h𝔪)
        ((FractionalIdeal.coeIdeal_le_coeIdeal K).mpr h)
    rw [FractionalIdeal.count_self] at h1
    exact lt_of_lt_of_le zero_lt_one h1
  · intro h
    rw [FractionalIdeal.count_coe K 𝔭 h𝔪] at h
    have hc : (Associates.mk 𝔭.asIdeal).count (Associates.mk 𝔪).factors ≠ 0 := by simpa using h.ne'
    have := (Associates.count_ne_zero_iff_dvd h𝔪 𝔭.irreducible).mp hc
    rwa [Ideal.dvd_iff_le] at this

/-- The `𝔭`-adic multiplicity of a finite product of powers of height one primes is the exponent of
`𝔭` itself, whenever `𝔭` occurs in the family, and `0` otherwise. -/
theorem count_finsetProd_prime_pow {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K]
    [Algebra R K] [IsFractionRing R K] [DecidableEq (HeightOneSpectrum R)]
    (s : Finset (HeightOneSpectrum R)) (e : HeightOneSpectrum R → ℕ) (𝔭 : HeightOneSpectrum R) :
    FractionalIdeal.count K 𝔭
        (∏ 𝔮 ∈ s, ((𝔮.asIdeal : Ideal R) : FractionalIdeal (nonZeroDivisors R) K) ^ (e 𝔮))
      = ((if 𝔭 ∈ s then e 𝔭 else 0 : ℕ) : ℤ) := by
  classical
  rw [FractionalIdeal.count_prod K 𝔭 s _
    (fun 𝔮 _ => pow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.mpr 𝔮.ne_bot))]
  simp only [FractionalIdeal.count_pow, FractionalIdeal.count_maximal]
  have h : ∀ i : HeightOneSpectrum R, (e i : ℤ) * (if i = 𝔭 then 1 else 0) =
      (if i = 𝔭 then (e i : ℤ) else 0) := by
    intro i; split <;> simp
  simp only [h, Finset.sum_ite_eq']
  split <;> simp

/-! ## The ramified part of `(M)` -/

theorem ramifiedPart
    {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (M : ℕ) (hM : 1 < M)
    (hramM : ∀ 𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      (M : NumberField.RingOfIntegers K) ∉ 𝔭.asIdeal →
      Ideal.ramificationIdxIn 𝔭.asIdeal (NumberField.RingOfIntegers L) = 1) :
    ∃ 𝔪 : Ideal (NumberField.RingOfIntegers K), 𝔪 ≠ ⊥ ∧
      (∀ 𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
        NK.CFTLib.ArtinReciprocityIdeal.DvdPrime 𝔪 𝔭 ↔
          Ideal.ramificationIdxIn 𝔭.asIdeal (NumberField.RingOfIntegers L) ≠ 1) ∧
      (∀ 𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
        NK.CFTLib.ArtinReciprocityIdeal.DvdPrime 𝔪 𝔭 →
          FractionalIdeal.count K 𝔭 (𝔪 : FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K)
            = FractionalIdeal.count K 𝔭
                ((Ideal.span {(M : NumberField.RingOfIntegers K)}) :
                  FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K)) ∧
      NK.CFTLib.ArtinReciprocityIdeal.ContainsRamified (K := K) (L := L) 𝔪 := by
  classical
  -- `(M)` is a nonzero ideal.
  have hM0 : (M : 𝓞 K) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hspan0 : Ideal.span {(M : 𝓞 K)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]; exact hM0
  -- The exponent of the modulus at a prime `𝔭`: `v_𝔭(M)`.
  let e : HeightOneSpectrum (𝓞 K) → ℕ :=
    fun 𝔭 => (FractionalIdeal.count K 𝔭 ((Ideal.span {(M : 𝓞 K)}) : FractionalIdeal (𝓞 K)⁰ K)).toNat
  -- Only finitely many primes are ramified: they all divide `(M)`.
  have hfin : {𝔭 : HeightOneSpectrum (𝓞 K) | Ideal.ramificationIdxIn 𝔭.asIdeal (𝓞 L) ≠ 1}.Finite := by
    refine (Ideal.finite_factors hspan0).subset ?_
    intro 𝔭 h𝔭
    show 𝔭.asIdeal ∣ Ideal.span {(M : 𝓞 K)}
    rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
    by_contra hmem
    exact h𝔭 (hramM 𝔭 hmem)
  let s : Finset (HeightOneSpectrum (𝓞 K)) := hfin.toFinset
  have hmem_s : ∀ 𝔭 : HeightOneSpectrum (𝓞 K),
      𝔭 ∈ s ↔ Ideal.ramificationIdxIn 𝔭.asIdeal (𝓞 L) ≠ 1 := fun 𝔭 => hfin.mem_toFinset
  -- Every ramified prime divides `(M)`, whence the corresponding exponent is positive.
  have he : ∀ 𝔭 ∈ s, 1 ≤ e 𝔭 := by
    intro 𝔭 h𝔭
    have hram : Ideal.ramificationIdxIn 𝔭.asIdeal (𝓞 L) ≠ 1 := (hmem_s 𝔭).mp h𝔭
    have hmem : (M : 𝓞 K) ∈ 𝔭.asIdeal := by
      by_contra h
      exact hram (hramM 𝔭 h)
    have hle' : Ideal.span {(M : 𝓞 K)} ≤ 𝔭.asIdeal :=
      (Ideal.span_singleton_le_iff_mem 𝔭.asIdeal).mpr hmem
    have hc : FractionalIdeal.count K 𝔭 ((𝔭.asIdeal : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) ≤
        FractionalIdeal.count K 𝔭 ((Ideal.span {(M : 𝓞 K)}) : FractionalIdeal (𝓞 K)⁰ K) :=
      FractionalIdeal.count_mono K 𝔭 (FractionalIdeal.coeIdeal_ne_zero.mpr hspan0)
        ((FractionalIdeal.coeIdeal_le_coeIdeal K).mpr hle')
    rw [FractionalIdeal.count_self] at hc
    have h0 : (0 : ℤ) ≤
        FractionalIdeal.count K 𝔭 ((Ideal.span {(M : 𝓞 K)}) : FractionalIdeal (𝓞 K)⁰ K) :=
      le_trans (by norm_num) hc
    exact (Int.le_toNat h0).mpr hc
  -- Coercing the ideal product to a fractional ideal commutes with the product.
  have hcoe : ∀ t : Finset (HeightOneSpectrum (𝓞 K)),
      ((∏ 𝔮 ∈ t, 𝔮.asIdeal ^ e 𝔮 : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)
        = ∏ 𝔮 ∈ t, ((𝔮.asIdeal : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) ^ e 𝔮 := by
    intro t
    induction t using Finset.cons_induction with
    | empty => simp
    | cons a t ha ih =>
      rw [Finset.prod_cons ha, Finset.prod_cons ha, FractionalIdeal.coeIdeal_mul,
        FractionalIdeal.coeIdeal_pow, ih]
  -- The modulus is nonzero.
  have hprod0 : (∏ 𝔮 ∈ s, 𝔮.asIdeal ^ e 𝔮 : Ideal (𝓞 K)) ≠ ⊥ := by
    induction s using Finset.cons_induction with
    | empty => simp
    | cons a t ha ih =>
      rw [Finset.prod_cons ha, Ne, Ideal.mul_eq_bot, not_or]
      exact ⟨pow_ne_zero _ a.ne_bot, ih⟩
  -- Its `𝔭`-adic multiplicity.
  have hcount : ∀ 𝔭 : HeightOneSpectrum (𝓞 K),
      FractionalIdeal.count K 𝔭 ((∏ 𝔮 ∈ s, 𝔮.asIdeal ^ e 𝔮 : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)
        = ((if 𝔭 ∈ s then e 𝔭 else 0 : ℕ) : ℤ) := by
    intro 𝔭
    rw [hcoe s]
    exact count_finsetProd_prime_pow s e 𝔭
  -- Its support is exactly the set of ramified primes.
  have hle : ∀ 𝔭 : HeightOneSpectrum (𝓞 K),
      NK.CFTLib.ArtinReciprocityIdeal.DvdPrime (∏ 𝔮 ∈ s, 𝔮.asIdeal ^ e 𝔮 : Ideal (𝓞 K)) 𝔭 ↔ 𝔭 ∈ s := by
    intro 𝔭
    rw [NK.CFTLib.ArtinReciprocityIdeal.DvdPrime,
      ideal_le_iff_count_pos (R := 𝓞 K) (K := K) hprod0 𝔭, hcount 𝔭]
    constructor
    · intro h
      by_contra h𝔭
      simp [h𝔭] at h
    · intro h𝔭
      simp only [h𝔭, reduceIte]
      have h1 : 0 < e 𝔭 := Nat.lt_of_lt_of_le Nat.zero_lt_one (he 𝔭 h𝔭)
      exact_mod_cast h1
  refine ⟨∏ 𝔮 ∈ s, 𝔮.asIdeal ^ e 𝔮, hprod0, ?_, ?_, ?_⟩
  · intro 𝔭
    exact (hle 𝔭).trans (hmem_s 𝔭)
  · intro 𝔭 h𝔭
    have h𝔭s : 𝔭 ∈ s := (hle 𝔭).mp h𝔭
    have hc := hcount 𝔭
    simp only [h𝔭s, reduceIte] at hc
    rw [hc]
    exact Int.toNat_of_nonneg (FractionalIdeal.count_coe_nonneg K 𝔭 (Ideal.span {(M : 𝓞 K)}))
  · intro 𝔭 h𝔭
    exact (hle 𝔭).mpr ((hmem_s 𝔭).mpr h𝔭)

end Work.SSGRoute.ZDataMup.ArtinReciprocity.IdealModulus
