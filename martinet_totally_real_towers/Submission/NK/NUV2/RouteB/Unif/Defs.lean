/-
Helper material for `NK.NUV2.RouteB.uniform_of_sharp_rayClassCount`.

For two finite sets of primes `S ⊆ S'`, every ideal `𝔞 ≠ 0` coprime to `S` factors as
`partAt (S'∖S) 𝔞 * partAway S' 𝔞`, where the first factor is supported on `S'∖S` and the second is
coprime to `S'`.  Summing the sharp ray-class count for `S'` over the finitely many possibilities
for the first factor turns the sharp bound (exponent `1 - 1/[K:ℚ]`) into a uniform bound (some
exponent `< 1`) for `S`.  This file contains the definitions and their elementary counting
properties; the count identity and the analytic summation live in
`NK.NUV2.RouteB.uniform_of_sharp_rayClassCount`.
-/
import Mathlib
import Submission.NK.HeckeL.Basic
import Submission.NK.HeckeL.Basic.classOfIdeal_mul
import Submission.NK.HeckeL.Basic.ideal_eq_prod_finsupp

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped nonZeroDivisors Classical BigOperators

namespace NK.NUV2.RouteB

variable {K : Type*} [Field K] [NumberField K]

/-! ## The counting functions -/

/-- The nonzero ideals of `𝓞 K` of norm `≤ N`, coprime to `S`, whose class in the ray class group
`𝕀 K ⧸ (Kˣ·U)` is `c`. -/
noncomputable def rayFinset (U : Subgroup (NK.GlobalCFT.Idele K))
    (S : Finset (NK.HeckeL.PrimeIdeal K))
    (c : NK.GlobalCFT.IdeleClassGroup.rayClassGroup K U) (N : ℕ) : Finset (Ideal (𝓞 K)) :=
  ((Ideal.finite_setOfPred_absNorm_le (S := 𝓞 K) N).toFinset).filter
    (fun 𝔞 => 𝔞 ≠ 0 ∧ (∀ 𝔭 ∈ S, ¬ 𝔭.asIdeal ∣ 𝔞) ∧
      NK.HeckeL.classOfIdeal K U 𝔞 = c ∧ Ideal.absNorm 𝔞 ≤ N)

/-- The number of nonzero ideals of `𝓞 K` of norm `≤ N` coprime to `S` in the ray class `c`. -/
noncomputable def rayCnt (U : Subgroup (NK.GlobalCFT.Idele K))
    (S : Finset (NK.HeckeL.PrimeIdeal K))
    (c : NK.GlobalCFT.IdeleClassGroup.rayClassGroup K U) (N : ℕ) : ℕ :=
  (rayFinset U S c N).card

/-- The ideals supported on `S'∖S` of norm `≤ N`: the possible "extra Euler factors" in the
passage from the modulus `S'` to the set `S`. -/
noncomputable def extraSupports (S' S : Finset (NK.HeckeL.PrimeIdeal K)) (N : ℕ) :
    Finset (Ideal (𝓞 K)) :=
  ((Ideal.finite_setOfPred_absNorm_le (S := 𝓞 K) N).toFinset).filter
    (fun 𝔟 => 𝔟 ≠ 0 ∧ (∀ 𝔭 : NK.HeckeL.PrimeIdeal K, 𝔭.asIdeal ∣ 𝔟 → 𝔭 ∈ S' \ S) ∧
      Ideal.absNorm 𝔟 ≤ N)

/-! ## The splitting of an ideal carried by a finite set of primes -/

/-- The part of an ideal carried by the finite set `E` of primes: the product of the prime powers
with the multiplicities of the primes of `E` in the factorisation of `𝔞`. -/
noncomputable def partAt (E : Finset (NK.HeckeL.PrimeIdeal K)) (𝔞 : Ideal (𝓞 K)) : Ideal (𝓞 K) :=
  ∏ 𝔭 ∈ E, 𝔭.asIdeal ^ (FractionalIdeal.count K 𝔭 (𝔞 : FractionalIdeal (𝓞 K)⁰ K)).toNat

/-- The multiplicities of the primes outside `S'` in the factorisation of `𝔞`, as a finitely
supported function. -/
noncomputable def awayExps (S' : Finset (NK.HeckeL.PrimeIdeal K)) (𝔞 : Ideal (𝓞 K)) :
    {𝔭 : NK.HeckeL.PrimeIdeal K // 𝔭 ∉ S'} →₀ ℕ :=
  Finsupp.ofSupportFinite
    (fun 𝔭 => (FractionalIdeal.count K 𝔭.1 (𝔞 : FractionalIdeal (𝓞 K)⁰ K)).toNat)
    (by
      have hfin : {v : NK.HeckeL.PrimeIdeal K |
          FractionalIdeal.count K v (𝔞 : FractionalIdeal (𝓞 K)⁰ K) ≠ 0}.Finite :=
        Filter.eventually_cofinite.mp
          (FractionalIdeal.finite_factors (K := K) (I := (𝔞 : FractionalIdeal (𝓞 K)⁰ K)))
      refine (Set.Finite.preimage (f := fun 𝔭 : {𝔭 : NK.HeckeL.PrimeIdeal K // 𝔭 ∉ S'} => 𝔭.1)
        (fun a _ b _ h => Subtype.ext h) hfin).subset ?_
      intro 𝔭 h𝔭
      simp only [Function.mem_support, Set.mem_preimage, Set.mem_ofPred_eq] at h𝔭 ⊢
      intro hc
      exact h𝔭 (by rw [hc]; rfl))

/-- The part of an ideal carried by the primes outside `S'`. -/
noncomputable def partAway (S' : Finset (NK.HeckeL.PrimeIdeal K)) (𝔞 : Ideal (𝓞 K)) :
    Ideal (𝓞 K) :=
  (awayExps S' 𝔞).prod (fun 𝔭 e => 𝔭.1.asIdeal ^ e)

/-! ## The `𝔭`-adic valuation of the two parts -/

/-- The coercion `Ideal → FractionalIdeal` commutes with finite products of prime powers. -/
lemma coeIdeal_finset_prod_pow (E : Finset (NK.HeckeL.PrimeIdeal K))
    (k : NK.HeckeL.PrimeIdeal K → ℕ) :
    ((∏ 𝔭 ∈ E, (𝔭.asIdeal : Ideal (𝓞 K)) ^ k 𝔭 : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)
      = ∏ 𝔭 ∈ E, ((𝔭.asIdeal : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) ^ k 𝔭 := by
  induction E using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.prod_insert ha, FractionalIdeal.coeIdeal_mul, ih,
        FractionalIdeal.coeIdeal_pow]

/-- The `v`-adic valuation of a finite product of powers of primes: only the factor at `v`
contributes. -/
lemma count_finset_prod_pow (E : Finset (NK.HeckeL.PrimeIdeal K))
    (k : NK.HeckeL.PrimeIdeal K → ℕ) (v : NK.HeckeL.PrimeIdeal K) :
    FractionalIdeal.count K v
        ((∏ 𝔭 ∈ E, (𝔭.asIdeal : Ideal (𝓞 K)) ^ k 𝔭 : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)
      = if v ∈ E then (k v : ℤ) else 0 := by
  classical
  rw [coeIdeal_finset_prod_pow]
  rw [FractionalIdeal.count_prod K v E
    (fun 𝔭 => ((𝔭.asIdeal : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) ^ k 𝔭)
    (fun 𝔭 _ => pow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.mpr 𝔭.ne_bot))]
  rw [Finset.sum_congr rfl (fun 𝔭 _ => by
    rw [FractionalIdeal.count_pow, FractionalIdeal.count_maximal, mul_ite, mul_one, mul_zero])]
  rw [Finset.sum_ite_eq' E v (fun 𝔭 => (k 𝔭 : ℤ))]

/-- The `v`-adic valuation of `partAt E 𝔞` is the valuation of `𝔞` for `v ∈ E` and vanishes
otherwise. -/
lemma count_partAt (E : Finset (NK.HeckeL.PrimeIdeal K)) (𝔞 : Ideal (𝓞 K))
    (v : NK.HeckeL.PrimeIdeal K) :
    FractionalIdeal.count K v (partAt E 𝔞 : FractionalIdeal (𝓞 K)⁰ K)
      = if v ∈ E then FractionalIdeal.count K v (𝔞 : FractionalIdeal (𝓞 K)⁰ K) else 0 := by
  classical
  rw [partAt, count_finset_prod_pow]
  by_cases hv : v ∈ E
  · rw [if_pos hv, if_pos hv, Int.toNat_of_nonneg (FractionalIdeal.count_coe_nonneg K v 𝔞)]
  · rw [if_neg hv, if_neg hv]

/-- The `v`-adic valuation of `partAway S' 𝔞` is the valuation of `𝔞` for `v ∉ S'` and vanishes
otherwise. -/
lemma count_partAway (S' : Finset (NK.HeckeL.PrimeIdeal K)) (𝔞 : Ideal (𝓞 K))
    (v : NK.HeckeL.PrimeIdeal K) :
    FractionalIdeal.count K v (partAway S' 𝔞 : FractionalIdeal (𝓞 K)⁰ K)
      = if v ∉ S' then FractionalIdeal.count K v (𝔞 : FractionalIdeal (𝓞 K)⁰ K) else 0 := by
  classical
  rw [partAway, Finsupp.prod]
  rw [NK.HeckeL.Basic.IdealProdFinsupp.count_prod_finsupp_eq]
  by_cases hv : v ∉ S'
  · rw [dif_pos hv, if_pos hv]
    simp only [awayExps, Finsupp.ofSupportFinite_coe]
    exact Int.toNat_of_nonneg (FractionalIdeal.count_coe_nonneg K v 𝔞)
  · rw [dif_neg hv, if_neg hv]

/-- Both parts of an ideal are nonzero. -/
lemma partAt_ne_zero (E : Finset (NK.HeckeL.PrimeIdeal K)) (𝔞 : Ideal (𝓞 K)) :
    partAt E 𝔞 ≠ 0 := by
  rw [partAt, Finset.prod_ne_zero_iff]
  intro 𝔭 _
  exact pow_ne_zero _ (by simpa using 𝔭.ne_bot)

lemma partAway_ne_zero (S' : Finset (NK.HeckeL.PrimeIdeal K)) (𝔞 : Ideal (𝓞 K)) :
    partAway S' 𝔞 ≠ 0 := by
  rw [partAway, Finsupp.prod, Finset.prod_ne_zero_iff]
  intro 𝔭 _
  exact pow_ne_zero _ (by simpa using 𝔭.1.ne_bot)

/-! ## Divisibility bookkeeping -/

/-- A prime which does not divide an ideal has vanishing valuation there. -/
lemma count_eq_zero_of_not_dvd {𝔞 : Ideal (𝓞 K)} (h : 𝔞 ≠ 0) {𝔭 : NK.HeckeL.PrimeIdeal K}
    (hpd : ¬ 𝔭.asIdeal ∣ 𝔞) :
    FractionalIdeal.count K 𝔭 (𝔞 : FractionalIdeal (𝓞 K)⁰ K) = 0 :=
  not_not.mp fun hc =>
    hpd ((NK.HeckeL.Basic.IdealProdFinsupp.count_coe_ne_zero_iff_dvd h 𝔭).mp hc)

/-- Conversely, a prime with vanishing valuation does not divide the ideal. -/
lemma not_dvd_of_count_eq_zero {𝔞 : Ideal (𝓞 K)} (h : 𝔞 ≠ 0) {𝔭 : NK.HeckeL.PrimeIdeal K}
    (h0 : FractionalIdeal.count K 𝔭 (𝔞 : FractionalIdeal (𝓞 K)⁰ K) = 0) : ¬ 𝔭.asIdeal ∣ 𝔞 :=
  fun hd => by
    have hne := (NK.HeckeL.Basic.IdealProdFinsupp.count_coe_ne_zero_iff_dvd h 𝔭).mpr hd
    rw [h0] at hne
    exact hne rfl

/-- A prime not dividing either factor does not divide the product. -/
lemma not_dvd_mul {𝔟 𝔞 : Ideal (𝓞 K)} (h𝔟 : 𝔟 ≠ 0) (h𝔞 : 𝔞 ≠ 0) {𝔭 : NK.HeckeL.PrimeIdeal K}
    (hb : ¬ 𝔭.asIdeal ∣ 𝔟) (ha : ¬ 𝔭.asIdeal ∣ 𝔞) : ¬ 𝔭.asIdeal ∣ 𝔟 * 𝔞 := by
  intro hd
  have hne := (NK.HeckeL.Basic.IdealProdFinsupp.count_coe_ne_zero_iff_dvd
    (mul_ne_zero h𝔟 h𝔞) 𝔭).mpr hd
  rw [FractionalIdeal.coeIdeal_mul,
    FractionalIdeal.count_mul K 𝔭 (by simpa using h𝔟) (by simpa using h𝔞),
    count_eq_zero_of_not_dvd h𝔟 hb, count_eq_zero_of_not_dvd h𝔞 ha, add_zero] at hne
  exact hne rfl

/-! ## The splitting of an ideal coprime to `S` along `S ⊆ S'` -/

/-- `partAt E 𝔞` is supported on `E`. -/
lemma partAt_supported (E : Finset (NK.HeckeL.PrimeIdeal K)) (𝔞 : Ideal (𝓞 K))
    {𝔭 : NK.HeckeL.PrimeIdeal K} (h : 𝔭.asIdeal ∣ partAt E 𝔞) : 𝔭 ∈ E := by
  by_contra h𝔭
  have hz : FractionalIdeal.count K 𝔭 (partAt E 𝔞 : FractionalIdeal (𝓞 K)⁰ K) = 0 := by
    rw [count_partAt, if_neg h𝔭]
  have hne := (NK.HeckeL.Basic.IdealProdFinsupp.count_coe_ne_zero_iff_dvd
    (partAt_ne_zero E 𝔞) 𝔭).mpr h
  rw [hz] at hne
  exact hne rfl

/-- `partAway S' 𝔞` is coprime to `S'`. -/
lemma partAway_coprime (S' : Finset (NK.HeckeL.PrimeIdeal K)) (𝔞 : Ideal (𝓞 K))
    {𝔭 : NK.HeckeL.PrimeIdeal K} (h𝔭 : 𝔭 ∈ S') : ¬ 𝔭.asIdeal ∣ partAway S' 𝔞 := by
  intro h
  have hne := (NK.HeckeL.Basic.IdealProdFinsupp.count_coe_ne_zero_iff_dvd
    (partAway_ne_zero S' 𝔞) 𝔭).mpr h
  rw [count_partAway, if_neg (fun h' : 𝔭 ∉ S' => h' h𝔭)] at hne
  exact hne rfl

/-- `partAt (S'∖S) 𝔞` is coprime to `S`. -/
lemma partAt_coprime {S S' : Finset (NK.HeckeL.PrimeIdeal K)} (𝔞 : Ideal (𝓞 K))
    {𝔭 : NK.HeckeL.PrimeIdeal K} (h𝔭 : 𝔭 ∈ S) : ¬ 𝔭.asIdeal ∣ partAt (S' \ S) 𝔞 := by
  intro h
  have hne := (NK.HeckeL.Basic.IdealProdFinsupp.count_coe_ne_zero_iff_dvd
    (partAt_ne_zero _ 𝔞) 𝔭).mpr h
  rw [count_partAt, if_neg (fun h' : 𝔭 ∈ S' \ S => (Finset.mem_sdiff.mp h').2 h𝔭)] at hne
  exact hne rfl

/-- An ideal divisible by `𝔟` has norm divisible by the norm of `𝔟`, hence the norm of `𝔟` is at
most the norm of the ideal. -/
lemma absNorm_le_of_dvd {𝔟 𝔞 : Ideal (𝓞 K)} (h : 𝔟 ∣ 𝔞) (h𝔞 : 𝔞 ≠ 0) :
    Ideal.absNorm 𝔟 ≤ Ideal.absNorm 𝔞 := by
  obtain ⟨𝔠, rfl⟩ := h
  have hc : 𝔠 ≠ 0 := fun h0 => h𝔞 (by rw [h0, mul_zero])
  rw [map_mul]
  exact Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero fun h0 =>
    hc (Ideal.absNorm_eq_zero_iff.mp h0))

/-- **The splitting of an ideal coprime to `S` along `S ⊆ S'`**: an ideal `𝔞 ≠ 0` coprime to `S`
is the product of its part supported on `S'∖S` and its part supported away from `S'`. -/
lemma partAt_mul_partAway {S S' : Finset (NK.HeckeL.PrimeIdeal K)} (hSS : S ⊆ S')
    {𝔞 : Ideal (𝓞 K)} (h𝔞 : 𝔞 ≠ 0) (hcop : ∀ 𝔭 ∈ S, ¬ 𝔭.asIdeal ∣ 𝔞) :
    partAt (S' \ S) 𝔞 * partAway S' 𝔞 = 𝔞 := by
  refine NK.HeckeL.Basic.IdealProdFinsupp.ideal_eq_of_count_eq
    (mul_ne_zero (partAt_ne_zero _ _) (partAway_ne_zero _ _)) h𝔞 ?_
  intro v
  rw [FractionalIdeal.coeIdeal_mul,
    FractionalIdeal.count_mul K v (by simpa using partAt_ne_zero (S' \ S) 𝔞)
      (by simpa using partAway_ne_zero S' 𝔞),
    count_partAt, count_partAway]
  by_cases hvS : v ∈ S
  · have h1 : ¬ (v ∈ S' \ S) := fun h => (Finset.mem_sdiff.mp h).2 hvS
    have h2 : ¬ (v ∉ S') := fun h => h (hSS hvS)
    rw [if_neg h1, if_neg h2, add_zero]
    have hz : FractionalIdeal.count K v (𝔞 : FractionalIdeal (𝓞 K)⁰ K) = 0 :=
      count_eq_zero_of_not_dvd h𝔞 (hcop v hvS)
    simp [hz]
  · by_cases hvS' : v ∈ S'
    · have h1 : v ∈ S' \ S := Finset.mem_sdiff.mpr ⟨hvS', hvS⟩
      rw [if_pos h1, if_neg (fun h : v ∉ S' => h hvS'), add_zero]
    · have h1 : ¬ (v ∈ S' \ S) := fun h => hvS' (Finset.mem_sdiff.mp h).1
      rw [if_neg h1, if_pos hvS', zero_add]

/-- **Reconstruction of the first factor**: for `𝔟` supported on `S'∖S` and `𝔞` coprime to `S'`,
`partAt (S'∖S) (𝔟·𝔞) = 𝔟`. -/
lemma partAt_mul_eq {S S' : Finset (NK.HeckeL.PrimeIdeal K)} {𝔟 𝔞 : Ideal (𝓞 K)} (h𝔟 : 𝔟 ≠ 0)
    (hsupp : ∀ 𝔭 : NK.HeckeL.PrimeIdeal K, 𝔭.asIdeal ∣ 𝔟 → 𝔭 ∈ S' \ S) (h𝔞 : 𝔞 ≠ 0)
    (hcop : ∀ 𝔭 ∈ S', ¬ 𝔭.asIdeal ∣ 𝔞) :
    partAt (S' \ S) (𝔟 * 𝔞) = 𝔟 := by
  refine NK.HeckeL.Basic.IdealProdFinsupp.ideal_eq_of_count_eq (partAt_ne_zero _ _) h𝔟 ?_
  intro v
  rw [count_partAt, FractionalIdeal.coeIdeal_mul,
    FractionalIdeal.count_mul K v (by simpa using h𝔟) (by simpa using h𝔞)]
  by_cases hv : v ∈ S' \ S
  · rw [if_pos hv]
    have hz : FractionalIdeal.count K v (𝔞 : FractionalIdeal (𝓞 K)⁰ K) = 0 :=
      count_eq_zero_of_not_dvd h𝔞 (hcop v (Finset.mem_sdiff.mp hv).1)
    simp [hz]
  · rw [if_neg hv]
    have hz : FractionalIdeal.count K v (𝔟 : FractionalIdeal (𝓞 K)⁰ K) = 0 :=
      count_eq_zero_of_not_dvd h𝔟 (fun hd => hv (hsupp v hd))
    simp [hz]

/-- **Reconstruction of the second factor**: for `𝔟` supported on `S'∖S` and `𝔞` coprime to `S'`,
`partAway S' (𝔟·𝔞) = 𝔞`. -/
lemma partAway_mul_eq {S S' : Finset (NK.HeckeL.PrimeIdeal K)} {𝔟 𝔞 : Ideal (𝓞 K)} (h𝔟 : 𝔟 ≠ 0)
    (hsupp : ∀ 𝔭 : NK.HeckeL.PrimeIdeal K, 𝔭.asIdeal ∣ 𝔟 → 𝔭 ∈ S' \ S) (h𝔞 : 𝔞 ≠ 0)
    (hcop : ∀ 𝔭 ∈ S', ¬ 𝔭.asIdeal ∣ 𝔞) :
    partAway S' (𝔟 * 𝔞) = 𝔞 := by
  refine NK.HeckeL.Basic.IdealProdFinsupp.ideal_eq_of_count_eq (partAway_ne_zero _ _) h𝔞 ?_
  intro v
  rw [count_partAway, FractionalIdeal.coeIdeal_mul,
    FractionalIdeal.count_mul K v (by simpa using h𝔟) (by simpa using h𝔞)]
  by_cases hv : v ∉ S'
  · rw [if_pos hv]
    have hz : FractionalIdeal.count K v (𝔟 : FractionalIdeal (𝓞 K)⁰ K) = 0 :=
      count_eq_zero_of_not_dvd h𝔟 fun hd => hv (Finset.mem_sdiff.mp (hsupp v hd)).1
    simp [hz]
  · rw [if_neg hv]
    have hz : FractionalIdeal.count K v (𝔞 : FractionalIdeal (𝓞 K)⁰ K) = 0 :=
      count_eq_zero_of_not_dvd h𝔞 (hcop v (not_not.mp hv))
    simp [hz]

/-! ## Basic properties of the counting functions -/

/-- Membership in `rayFinset`, in the form used by the counting arguments. -/
lemma mem_rayFinset (U : Subgroup (NK.GlobalCFT.Idele K))
    (S : Finset (NK.HeckeL.PrimeIdeal K))
    (c : NK.GlobalCFT.IdeleClassGroup.rayClassGroup K U) (N : ℕ) (𝔞 : Ideal (𝓞 K)) :
    𝔞 ∈ rayFinset U S c N ↔
      (𝔞 ≠ 0 ∧ (∀ 𝔭 ∈ S, ¬ 𝔭.asIdeal ∣ 𝔞) ∧ NK.HeckeL.classOfIdeal K U 𝔞 = c ∧
        Ideal.absNorm 𝔞 ≤ N) := by
  simp only [rayFinset, Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
  tauto

/-- Membership in `extraSupports`, in the form used by the counting arguments. -/
lemma mem_extraSupports (S' S : Finset (NK.HeckeL.PrimeIdeal K)) (N : ℕ) (𝔟 : Ideal (𝓞 K)) :
    𝔟 ∈ extraSupports S' S N ↔
      (𝔟 ≠ 0 ∧ (∀ 𝔭 : NK.HeckeL.PrimeIdeal K, 𝔭.asIdeal ∣ 𝔟 → 𝔭 ∈ S' \ S) ∧
        Ideal.absNorm 𝔟 ≤ N) := by
  simp only [extraSupports, Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
  tauto

/-- The cardinality of `s.filter P` is the number of elements of `s` satisfying `P`. -/
lemma natCard_subtype_eq_filter_card {α : Type*} (s : Finset α) (P : α → Prop)
    [DecidablePred P] (hsub : ∀ x, P x → x ∈ s) :
    Nat.card {x : α // P x} = (s.filter P).card := by
  have hfin : ({x : α | P x} : Set α).Finite := s.finite_toSet.subset fun x hx => hsub x hx
  have h1 : Nat.card {x : α // P x} = ({x : α | P x} : Set α).ncard := Nat.card_coe_set_eq _
  rw [h1, Set.ncard_eq_toFinset_card _ hfin]
  congr 1
  ext x
  simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, Finset.mem_filter]
  exact ⟨fun h => ⟨hsub x h, h⟩, fun h => h.2⟩

/-- `rayCnt` is the `Nat.card` of the corresponding subtype (with a natural bound). -/
lemma rayCnt_eq_natCard (U : Subgroup (NK.GlobalCFT.Idele K))
    (S : Finset (NK.HeckeL.PrimeIdeal K))
    (c : NK.GlobalCFT.IdeleClassGroup.rayClassGroup K U) (N : ℕ) :
    rayCnt U S c N = Nat.card {𝔞 : Ideal (𝓞 K) //
      𝔞 ≠ 0 ∧ (∀ 𝔭 ∈ S, ¬ 𝔭.asIdeal ∣ 𝔞) ∧ NK.HeckeL.classOfIdeal K U 𝔞 = c ∧
        Ideal.absNorm 𝔞 ≤ N} := by
  rw [rayCnt, rayFinset]
  refine (natCard_subtype_eq_filter_card
    (s := (Ideal.finite_setOfPred_absNorm_le (S := 𝓞 K) N).toFinset)
    (P := fun 𝔞 => 𝔞 ≠ 0 ∧ (∀ 𝔭 ∈ S, ¬ 𝔭.asIdeal ∣ 𝔞) ∧
      NK.HeckeL.classOfIdeal K U 𝔞 = c ∧ Ideal.absNorm 𝔞 ≤ N) ?_).symm
  intro x hx
  rw [Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
  exact hx.2.2.2

/-- `rayCnt` is the `Nat.card` of the corresponding subtype, with a real bound. -/
lemma rayCnt_eq_natCard_real (U : Subgroup (NK.GlobalCFT.Idele K))
    (S : Finset (NK.HeckeL.PrimeIdeal K))
    (c : NK.GlobalCFT.IdeleClassGroup.rayClassGroup K U) (N : ℕ) :
    rayCnt U S c N = Nat.card {𝔞 : Ideal (𝓞 K) //
      𝔞 ≠ 0 ∧ (∀ 𝔭 ∈ S, ¬ 𝔭.asIdeal ∣ 𝔞) ∧ NK.HeckeL.classOfIdeal K U 𝔞 = c ∧
        (Ideal.absNorm 𝔞 : ℝ) ≤ (N : ℝ)} := by
  rw [rayCnt_eq_natCard]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun 𝔞 => ?_)
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨h1, h2, h3, Nat.cast_le.mpr h4⟩
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨h1, h2, h3, Nat.cast_le.mp h4⟩

/-- The bridge used to apply the counting hypothesis: for a real bound `X`, the corresponding
`Nat.card` is `rayCnt` at `⌊X⌋₊`. -/
lemma rayCnt_eq_natCard_le (U : Subgroup (NK.GlobalCFT.Idele K))
    (S : Finset (NK.HeckeL.PrimeIdeal K))
    (c : NK.GlobalCFT.IdeleClassGroup.rayClassGroup K U) (X : ℝ) (hX : 0 ≤ X) :
    rayCnt U S c ⌊X⌋₊ = Nat.card {𝔞 : Ideal (𝓞 K) //
      𝔞 ≠ 0 ∧ (∀ 𝔭 ∈ S, ¬ 𝔭.asIdeal ∣ 𝔞) ∧ NK.HeckeL.classOfIdeal K U 𝔞 = c ∧
        (Ideal.absNorm 𝔞 : ℝ) ≤ X} := by
  rw [rayCnt_eq_natCard_real]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun 𝔞 => ?_)
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨h1, h2, h3, le_trans h4 (Nat.floor_le hX)⟩
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨h1, h2, h3, Nat.cast_le.mpr (Nat.le_floor h4)⟩

end NK.NUV2.RouteB
