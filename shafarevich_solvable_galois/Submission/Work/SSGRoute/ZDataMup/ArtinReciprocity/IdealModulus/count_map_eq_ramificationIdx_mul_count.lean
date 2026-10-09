import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The `𝔮`-adic exponent of `𝔪·𝓞 L` is the ramification index times the `𝔭`-adic exponent

For a finite extension `L / K` of number fields, a nonzero prime `𝔭` of `𝓞 K`, a prime `𝔮` of `𝓞 L`
lying over `𝔭`, and a nonzero ideal `𝔪` of `𝓞 K`:

`count L 𝔮 (𝔪·𝓞 L) = e(𝔮 | 𝔭) · count K 𝔭 𝔪`.

The proof factors `𝔪 = ∏_𝔭' 𝔭'^{v_{𝔭'}(𝔪)}`, applies `𝔪 ↦ 𝔪·𝓞 L` (a ring homomorphism of the
monoids of ideals) and computes each `𝔭'`-contribution with `Ideal.map_algebraMap_eq_finsetProd_pow`
together with `FractionalIdeal.count` of a mapped prime (which is `e(𝔮|𝔭')` if `𝔮` lies over `𝔭'`,
and `0` otherwise).  As `𝔮` lies over a unique prime of `𝓞 K`, only `𝔭' = 𝔭` survives.
-/

set_option maxHeartbeats 4000000

noncomputable section

namespace Work.SSGRoute.ZDataMup.ArtinReciprocity.IdealModulus

open NumberField IsDedekindDomain Classical

open scoped nonZeroDivisors

/-- The coercion of a finite product of powers of ideals to fractional ideals: it is the product
of the powers of the coerced ideals. -/
lemma coeIdeal_finsetProd_pow {R : Type*} [CommRing R] [IsDedekindDomain R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K] {ι : Type*}
    (s : Finset ι) (P : ι → Ideal R) (e : ι → ℕ) :
    ((∏ i ∈ s, P i ^ e i : Ideal R) : FractionalIdeal (nonZeroDivisors R) K)
      = ∏ i ∈ s, (P i : FractionalIdeal (nonZeroDivisors R) K) ^ (e i : ℤ) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.prod_insert ha, FractionalIdeal.coeIdeal_mul,
        FractionalIdeal.coeIdeal_pow, ih, zpow_natCast]

/-- The `v`-adic exponent of a nonzero prime ideal `P` (regarded as a fractional ideal) is `1` if
`P = v.asIdeal` and `0` otherwise. -/
lemma count_coe_prime {R : Type*} [CommRing R] [IsDedekindDomain R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    (v : IsDedekindDomain.HeightOneSpectrum R) {P : Ideal R} (hP : P.IsPrime) (hP0 : P ≠ ⊥) :
    FractionalIdeal.count K v (P : FractionalIdeal (nonZeroDivisors R) K)
      = if P = v.asIdeal then 1 else 0 := by
  classical
  let Q : IsDedekindDomain.HeightOneSpectrum R := ⟨P, hP, hP0⟩
  have h : (P : FractionalIdeal (nonZeroDivisors R) K)
      = (Q.asIdeal : FractionalIdeal (nonZeroDivisors R) K) := rfl
  rw [h, FractionalIdeal.count_maximal]
  congr 1
  exact propext (HeightOneSpectrum.ext_iff)

/-- The `𝔮`-adic exponent of the base change of a prime `𝔭` is the ramification index `e(𝔮|𝔭)` if
`𝔮` lies over `𝔭`, and `0` otherwise. -/
lemma count_map_prime {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L)) :
    FractionalIdeal.count L 𝔮 ((Ideal.map (algebraMap (NumberField.RingOfIntegers K)
        (NumberField.RingOfIntegers L)) 𝔭.asIdeal : Ideal (NumberField.RingOfIntegers L)) :
      FractionalIdeal (NumberField.RingOfIntegers L)⁰ L)
      = if 𝔮.asIdeal.LiesOver 𝔭.asIdeal then
          (𝔮.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) : ℤ) else 0 := by
  classical
  have h𝔭 : 𝔭.asIdeal ≠ 0 := 𝔭.ne_bot
  haveI : 𝔭.asIdeal.IsMaximal := 𝔭.isPrime.isMaximal 𝔭.ne_bot
  rw [Ideal.map_algebraMap_eq_finsetProd_pow (p := 𝔭.asIdeal) h𝔭]
  rw [coeIdeal_finsetProd_pow (K := L)]
  have hcount : ∀ P ∈ (𝔭.asIdeal.primesOver (NumberField.RingOfIntegers L)).toFinset,
      FractionalIdeal.count L 𝔮 ((P : Ideal (NumberField.RingOfIntegers L)) :
        FractionalIdeal (NumberField.RingOfIntegers L)⁰ L)
        = if P = 𝔮.asIdeal then 1 else 0 := by
    intro P hP
    rw [Set.mem_toFinset] at hP
    exact count_coe_prime 𝔮 hP.1 (Ideal.ne_bot_of_mem_primesOver 𝔭.ne_bot hP)
  rw [FractionalIdeal.count_prod]
  · rw [Finset.sum_congr rfl (fun P hP => by
      rw [FractionalIdeal.count_zpow, hcount P hP, mul_ite, mul_one, mul_zero])]
    rw [Finset.sum_ite_eq']
    by_cases hL : 𝔮.asIdeal.LiesOver 𝔭.asIdeal
    · have hm : 𝔮.asIdeal ∈ (𝔭.asIdeal.primesOver (NumberField.RingOfIntegers L)).toFinset := by
        rw [Set.mem_toFinset]; exact ⟨𝔮.isPrime, hL⟩
      rw [if_pos hL, if_pos hm]
    · have hm : 𝔮.asIdeal ∉ (𝔭.asIdeal.primesOver (NumberField.RingOfIntegers L)).toFinset := by
        rw [Set.mem_toFinset]; exact fun h => hL h.2
      rw [if_neg hL, if_neg hm]
  · intro P hP
    rw [Set.mem_toFinset] at hP
    exact zpow_ne_zero _
      (FractionalIdeal.coeIdeal_ne_zero.mpr (Ideal.ne_bot_of_mem_primesOver 𝔭.ne_bot hP))

theorem count_map_eq_ramificationIdx_mul_count
    {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (h𝔮 : 𝔮.asIdeal.LiesOver 𝔭.asIdeal) (𝔪 : Ideal (NumberField.RingOfIntegers K))
    (h𝔪 : 𝔪 ≠ ⊥) :
    FractionalIdeal.count L 𝔮 (Ideal.map (algebraMap (NumberField.RingOfIntegers K)
        (NumberField.RingOfIntegers L)) 𝔪)
      = (𝔮.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) : ℤ) *
        FractionalIdeal.count K 𝔭 𝔪 := by
  classical
  set s : Finset (HeightOneSpectrum (NumberField.RingOfIntegers K)) :=
    (Ideal.finite_factors h𝔪).toFinset with hs
  have hsmem : ∀ v : HeightOneSpectrum (NumberField.RingOfIntegers K), v ∈ s ↔ v.asIdeal ∣ 𝔪 := by
    intro v
    rw [hs, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
  -- (1) factorization of `𝔪` over the primes dividing it
  have hsub : Function.mulSupport
      (fun v : HeightOneSpectrum (NumberField.RingOfIntegers K) => v.maxPowDividing 𝔪) ⊆ ↑s := by
    intro v hv
    rw [Finset.mem_coe, hsmem]
    by_contra hcon
    have hn : (Associates.mk v.asIdeal).count (Associates.mk 𝔪).factors = 0 := by
      rw [← not_ne_iff]
      exact fun h => hcon ((Associates.count_ne_zero_iff_dvd h𝔪 v.irreducible).mp h)
    exact hv (by change v.maxPowDividing 𝔪 = 1
                 rw [show v.maxPowDividing 𝔪 = v.asIdeal ^
                       (Associates.mk v.asIdeal).count (Associates.mk 𝔪).factors from rfl,
                   hn, pow_zero])
  have hfac1 : ∏ v ∈ s, v.maxPowDividing 𝔪 = 𝔪 := by
    rw [← finprod_eq_finsetProd_of_mulSupport_subset
      (fun v : HeightOneSpectrum (NumberField.RingOfIntegers K) => v.maxPowDividing 𝔪) hsub,
      Ideal.finprod_heightOneSpectrum_factorization h𝔪]
  have hfacR : 𝔪 = ∏ v ∈ s,
      v.asIdeal ^ (Associates.mk v.asIdeal).count (Associates.mk 𝔪).factors := by
    conv_lhs => rw [← hfac1]
    apply Finset.prod_congr rfl
    intro v _
    rw [show v.maxPowDividing 𝔪 = v.asIdeal ^
      (Associates.mk v.asIdeal).count (Associates.mk 𝔪).factors from rfl]
  -- (2) base change of the factorization
  have hmap_prod : ∀ (t : Finset (HeightOneSpectrum (NumberField.RingOfIntegers K))),
      Ideal.map (algebraMap (NumberField.RingOfIntegers K)
          (NumberField.RingOfIntegers L))
          (∏ v ∈ t, v.asIdeal ^ (Associates.mk v.asIdeal).count (Associates.mk 𝔪).factors)
        = ∏ v ∈ t, (Ideal.map (algebraMap (NumberField.RingOfIntegers K)
            (NumberField.RingOfIntegers L)) v.asIdeal) ^
            (Associates.mk v.asIdeal).count (Associates.mk 𝔪).factors := by
    intro t
    induction t using Finset.induction with
    | empty => simp [Ideal.map_top]
    | insert a t ha ih =>
        rw [Finset.prod_insert ha, Finset.prod_insert ha, Ideal.map_mul, ih, Ideal.map_pow]
  have hmap : Ideal.map (algebraMap (NumberField.RingOfIntegers K)
        (NumberField.RingOfIntegers L)) 𝔪
      = ∏ v ∈ s, (Ideal.map (algebraMap (NumberField.RingOfIntegers K)
          (NumberField.RingOfIntegers L)) v.asIdeal) ^
          (Associates.mk v.asIdeal).count (Associates.mk 𝔪).factors := by
    conv_lhs => rw [hfacR]
    exact hmap_prod s
  -- (3) coercion to fractional ideals
  have hmapF : ((Ideal.map (algebraMap (NumberField.RingOfIntegers K)
        (NumberField.RingOfIntegers L)) 𝔪 : Ideal (NumberField.RingOfIntegers L)) :
        FractionalIdeal (NumberField.RingOfIntegers L)⁰ L)
      = ∏ v ∈ s, ((Ideal.map (algebraMap (NumberField.RingOfIntegers K)
          (NumberField.RingOfIntegers L)) v.asIdeal : Ideal (NumberField.RingOfIntegers L)) :
          FractionalIdeal (NumberField.RingOfIntegers L)⁰ L) ^
          ((Associates.mk v.asIdeal).count (Associates.mk 𝔪).factors : ℤ) := by
    rw [hmap, coeIdeal_finsetProd_pow (K := L)]
  -- (4) additivity of the exponent
  have hcountprod : FractionalIdeal.count L 𝔮 ((Ideal.map (algebraMap
        (NumberField.RingOfIntegers K) (NumberField.RingOfIntegers L)) 𝔪 :
        Ideal (NumberField.RingOfIntegers L)) : FractionalIdeal (NumberField.RingOfIntegers L)⁰ L)
      = ∑ v ∈ s, ((Associates.mk v.asIdeal).count (Associates.mk 𝔪).factors : ℤ) *
          FractionalIdeal.count L 𝔮 ((Ideal.map (algebraMap (NumberField.RingOfIntegers K)
            (NumberField.RingOfIntegers L)) v.asIdeal : Ideal (NumberField.RingOfIntegers L)) :
            FractionalIdeal (NumberField.RingOfIntegers L)⁰ L) := by
    rw [hmapF, FractionalIdeal.count_prod]
    · apply Finset.sum_congr rfl
      intro v _
      rw [FractionalIdeal.count_zpow]
    · intro v _
      apply zpow_ne_zero
      rw [FractionalIdeal.coeIdeal_ne_zero]
      exact Ideal.map_ne_bot_of_ne_bot v.ne_bot
  rw [hcountprod]
  -- (5) each prime contributes its ramification index, only `𝔭` survives
  have hterm : ∀ v : HeightOneSpectrum (NumberField.RingOfIntegers K),
      FractionalIdeal.count L 𝔮 ((Ideal.map (algebraMap (NumberField.RingOfIntegers K)
        (NumberField.RingOfIntegers L)) v.asIdeal : Ideal (NumberField.RingOfIntegers L)) :
        FractionalIdeal (NumberField.RingOfIntegers L)⁰ L)
      = if v = 𝔭 then (𝔮.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) : ℤ) else 0 := by
    intro v
    have hiff : 𝔮.asIdeal.LiesOver v.asIdeal ↔ v = 𝔭 := by
      rw [Ideal.liesOver_iff, ← h𝔮.over]
      exact (HeightOneSpectrum.ext_iff (x := v) (y := 𝔭)).symm
    rw [count_map_prime v 𝔮]
    by_cases hv : v = 𝔭
    · rw [if_pos (hiff.mpr hv), if_pos hv]
    · rw [if_neg (fun h => hv (hiff.mp h)), if_neg hv]
  rw [Finset.sum_congr rfl (fun v _ => by rw [hterm v])]
  rw [show (∑ v ∈ s, ((Associates.mk v.asIdeal).count (Associates.mk 𝔪).factors : ℤ) *
        (if v = 𝔭 then (𝔮.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) : ℤ) else 0))
      = ∑ v ∈ s, (if v = 𝔭 then
          ((Associates.mk v.asIdeal).count (Associates.mk 𝔪).factors : ℤ) *
            (𝔮.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) : ℤ) else 0) from by
    apply Finset.sum_congr rfl
    intro v _
    by_cases h : v = 𝔭 <;> simp [h]]
  rw [Finset.sum_ite_eq']
  have hcount𝔭 : FractionalIdeal.count K 𝔭 𝔪
      = ((Associates.mk 𝔭.asIdeal).count (Associates.mk 𝔪).factors : ℤ) :=
    FractionalIdeal.count_coe K 𝔭 h𝔪
  rw [hcount𝔭]
  by_cases h𝔭s : 𝔭 ∈ s
  · rw [if_pos h𝔭s]; ring
  · rw [if_neg h𝔭s]
    have hn0 : (Associates.mk 𝔭.asIdeal).count (Associates.mk 𝔪).factors = 0 := by
      rw [← not_ne_iff]
      exact fun h => h𝔭s ((hsmem 𝔭).mpr ((Associates.count_ne_zero_iff_dvd h𝔪 𝔭.irreducible).mp h))
    rw [hn0]; ring

end Work.SSGRoute.ZDataMup.ArtinReciprocity.IdealModulus
