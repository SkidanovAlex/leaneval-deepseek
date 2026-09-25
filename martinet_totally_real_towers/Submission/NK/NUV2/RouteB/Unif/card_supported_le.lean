/-
# Ideals supported on a finite set of primes: a polynomial-in-`log` count

Let `K` be a number field, `E` a finite set of primes of `𝓞 K` and `ε > 0`.  This file proves
that the number of nonzero ideals `𝔟` of `𝓞 K` all of whose prime divisors lie in `E` and with
`absNorm 𝔟 ≤ N` is bounded by `C · N ^ ε` with a constant `C` independent of `N`.

The proof is elementary: such an ideal is `∏_{𝔭 ∈ E} 𝔭 ^ e 𝔭`, its norm is
`∏_{𝔭 ∈ E} N𝔭 ^ e 𝔭 ≥ 2 ^ (∑ e 𝔭)`, so `∑ e 𝔭 ≤ log₂ N`; hence the exponent vector lies in
`∏_{𝔭 ∈ E} {0, …, ⌊log₂ N⌋}`, of cardinality `(⌊log₂ N⌋ + 1) ^ #E`.  Since a power of a logarithm
grows more slowly than `N ^ ε`, this gives the claim.
-/
import Mathlib
import Submission.NK.HeckeL.Basic
import Submission.NK.NUV2.RouteB.Unif.Defs

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped BigOperators Classical nonZeroDivisors

namespace NK.NUV2.RouteB.Unif

variable {K : Type*} [Field K] [NumberField K]

/-! ## The exponent of a prime in an ideal -/

/-- The multiplicity of the prime `𝔭` in the factorisation of the nonzero ideal `𝔟`. -/
noncomputable def expAt (𝔟 : Ideal (𝓞 K)) (𝔭 : NK.HeckeL.PrimeIdeal K) : ℕ :=
  (FractionalIdeal.count K 𝔭 (𝔟 : FractionalIdeal (𝓞 K)⁰ K)).toNat

/-- The multiplicity is the (nonnegative) `𝔭`-adic valuation of `𝔟`. -/
lemma coe_expAt (𝔟 : Ideal (𝓞 K)) (𝔭 : NK.HeckeL.PrimeIdeal K) :
    ((expAt 𝔟 𝔭 : ℕ) : ℤ) = FractionalIdeal.count K 𝔭 (𝔟 : FractionalIdeal (𝓞 K)⁰ K) :=
  Int.toNat_of_nonneg (FractionalIdeal.count_coe_nonneg K 𝔭 𝔟)

/-- A prime ideal of the ring of integers has norm at least `2`. -/
lemma two_le_absNorm_primeIdeal (𝔭 : NK.HeckeL.PrimeIdeal K) : 2 ≤ Ideal.absNorm 𝔭.asIdeal := by
  have h0 : Ideal.absNorm 𝔭.asIdeal ≠ 0 := by
    rw [Ideal.absNorm_ne_zero_iff]
    exact Ideal.finiteQuotientOfFreeOfNeBot 𝔭.asIdeal (by simpa using 𝔭.ne_bot)
  have h1 : Ideal.absNorm 𝔭.asIdeal ≠ 1 := fun h =>
    𝔭.isPrime.ne_top ((Ideal.absNorm_eq_one_iff).mp h)
  omega

/-- **An ideal supported on `E` is the product of the prime powers `𝔭 ^ expAt 𝔟 𝔭`.** -/
lemma eq_prod_of_supported {E : Finset (NK.HeckeL.PrimeIdeal K)} {𝔟 : Ideal (𝓞 K)}
    (h𝔟 : 𝔟 ≠ 0) (hsupp : ∀ 𝔭 : NK.HeckeL.PrimeIdeal K, 𝔭.asIdeal ∣ 𝔟 → 𝔭 ∈ E) :
    𝔟 = ∏ 𝔭 ∈ E, 𝔭.asIdeal ^ expAt 𝔟 𝔭 := by
  have h : (∏ 𝔭 ∈ E, 𝔭.asIdeal ^ expAt 𝔟 𝔭) = 𝔟 := by
    refine NK.HeckeL.Basic.IdealProdFinsupp.ideal_eq_of_count_eq
      (NK.NUV2.RouteB.partAt_ne_zero E 𝔟) h𝔟 ?_
    intro v
    rw [show (∏ 𝔭 ∈ E, 𝔭.asIdeal ^ expAt 𝔟 𝔭) = NK.NUV2.RouteB.partAt E 𝔟 from rfl]
    rw [NK.NUV2.RouteB.count_partAt]
    by_cases hv : v ∈ E
    · rw [if_pos hv]
    · rw [if_neg hv]
      exact (NK.NUV2.RouteB.count_eq_zero_of_not_dvd h𝔟 (fun hd => hv (hsupp v hd))).symm
  exact h.symm

/-- The norm of an ideal supported on `E` is the product of the norms of the prime powers. -/
lemma absNorm_eq_prod_of_supported {E : Finset (NK.HeckeL.PrimeIdeal K)} {𝔟 : Ideal (𝓞 K)}
    (h𝔟 : 𝔟 ≠ 0) (hsupp : ∀ 𝔭 : NK.HeckeL.PrimeIdeal K, 𝔭.asIdeal ∣ 𝔟 → 𝔭 ∈ E) :
    Ideal.absNorm 𝔟 = ∏ 𝔭 ∈ E, (Ideal.absNorm 𝔭.asIdeal) ^ expAt 𝔟 𝔭 := by
  calc Ideal.absNorm 𝔟 = Ideal.absNorm (∏ 𝔭 ∈ E, 𝔭.asIdeal ^ expAt 𝔟 𝔭) := by
        conv_lhs => rw [eq_prod_of_supported h𝔟 hsupp]
    _ = ∏ 𝔭 ∈ E, Ideal.absNorm (𝔭.asIdeal ^ expAt 𝔟 𝔭) := map_prod Ideal.absNorm _ E
    _ = ∏ 𝔭 ∈ E, (Ideal.absNorm 𝔭.asIdeal) ^ expAt 𝔟 𝔭 :=
        Finset.prod_congr rfl fun 𝔭 _ => map_pow _ _ _

/-- **The exponent sum is at most `log₂ N`.**  For `𝔟 ≠ 0` supported on `E` with
`absNorm 𝔟 ≤ N` one has `∑_{𝔭 ∈ E} expAt 𝔟 𝔭 ≤ Nat.log 2 N`. -/
lemma sum_expAt_le_log {E : Finset (NK.HeckeL.PrimeIdeal K)} {𝔟 : Ideal (𝓞 K)}
    (h𝔟 : 𝔟 ≠ 0) (hsupp : ∀ 𝔭 : NK.HeckeL.PrimeIdeal K, 𝔭.asIdeal ∣ 𝔟 → 𝔭 ∈ E)
    {N : ℕ} (hN : Ideal.absNorm 𝔟 ≤ N) :
    ∑ 𝔭 ∈ E, expAt 𝔟 𝔭 ≤ Nat.log 2 N := by
  refine Nat.le_log_of_pow_le one_lt_two ?_
  calc (2:ℕ) ^ (∑ 𝔭 ∈ E, expAt 𝔟 𝔭) = ∏ 𝔭 ∈ E, (2:ℕ) ^ expAt 𝔟 𝔭 :=
        (Finset.prod_pow_eq_pow_sum E (fun 𝔭 => expAt 𝔟 𝔭) 2).symm
    _ ≤ ∏ 𝔭 ∈ E, (Ideal.absNorm 𝔭.asIdeal) ^ expAt 𝔟 𝔭 :=
        Finset.prod_le_prod₀ (fun _ _ => Nat.zero_le _)
          (fun 𝔭 _ => pow_le_pow_left₀ (Nat.zero_le 2) (two_le_absNorm_primeIdeal 𝔭) _)
    _ = Ideal.absNorm 𝔟 := (absNorm_eq_prod_of_supported h𝔟 hsupp).symm
    _ ≤ N := hN

/-- An ideal supported on `E` is determined by the vector of exponents of the primes of `E`. -/
lemma expAt_injective {E : Finset (NK.HeckeL.PrimeIdeal K)} {𝔟 𝔠 : Ideal (𝓞 K)}
    (h𝔟 : 𝔟 ≠ 0) (h𝔟s : ∀ 𝔭, 𝔭.asIdeal ∣ 𝔟 → 𝔭 ∈ E)
    (h𝔠 : 𝔠 ≠ 0) (h𝔠s : ∀ 𝔭, 𝔭.asIdeal ∣ 𝔠 → 𝔭 ∈ E)
    (h : ∀ 𝔭 : {𝔭 : NK.HeckeL.PrimeIdeal K // 𝔭 ∈ E}, expAt 𝔟 𝔭.1 = expAt 𝔠 𝔭.1) :
    𝔟 = 𝔠 := by
  refine NK.HeckeL.Basic.IdealProdFinsupp.ideal_eq_of_count_eq h𝔟 h𝔠 fun v => ?_
  by_cases hv : v ∈ E
  · have hv' := h ⟨v, hv⟩
    rw [← coe_expAt 𝔟 v, ← coe_expAt 𝔠 v, hv']
  · rw [NK.NUV2.RouteB.count_eq_zero_of_not_dvd h𝔟 (fun hd => hv (h𝔟s v hd)),
        NK.NUV2.RouteB.count_eq_zero_of_not_dvd h𝔠 (fun hd => hv (h𝔠s v hd))]

/-! ## The analytic bound: a power of `log₂ N` is `O(N ^ ε)` -/

/-- For every `k : ℕ` and `ε > 0` there is `C > 0` with
`(⌊log₂ N⌋ + 1) ^ k ≤ C · N ^ ε` for all `N ≥ 1`. -/
lemma nat_log_bound (k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N →
      ((Nat.log 2 N : ℝ) + 1) ^ k ≤ C * (N : ℝ) ^ ε := by
  set δ : ℝ := min (ε / (k + 2)) 1 with hδdef
  have hδpos : 0 < δ := lt_min (div_pos hε (by positivity)) one_pos
  have hδle1 : δ ≤ 1 := min_le_right _ _
  have hδle : δ ≤ ε / (k + 2) := min_le_left _ _
  refine ⟨max 1 ((3 / δ) ^ k), lt_max_of_lt_left one_pos, fun N hN => ?_⟩
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNne : N ≠ 0 := by omega
  have hlogb : (Nat.log 2 N : ℝ) ≤ Real.logb 2 (N : ℝ) := by
    rw [Real.le_logb_iff_rpow_le one_lt_two hNpos, Real.rpow_natCast]
    exact_mod_cast Nat.pow_log_le_self 2 hNne
  have hlog2 : (2:ℝ)/3 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hlogN : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg hN1
  have hstep : Real.logb 2 (N : ℝ) ≤ (3/2) * Real.log (N : ℝ) := by
    rw [Real.logb]
    calc Real.log (N:ℝ) / Real.log 2 ≤ Real.log (N:ℝ) / ((2:ℝ)/3) :=
          div_le_div_of_nonneg_left hlogN (by norm_num) hlog2
      _ = (3/2) * Real.log (N:ℝ) := by ring
  have hstep2 : Real.log (N : ℝ) ≤ (N : ℝ) ^ δ / δ := Real.log_le_rpow_div hNpos.le hδpos
  have hNδ1 : (1 : ℝ) ≤ (N : ℝ) ^ δ := Real.one_le_rpow hN1 hδpos.le
  have hL : Real.logb 2 (N : ℝ) ≤ (3/(2*δ)) * (N : ℝ) ^ δ := by
    calc Real.logb 2 (N : ℝ) ≤ (3/2) * ((N : ℝ) ^ δ / δ) :=
          le_trans hstep (mul_le_mul_of_nonneg_left hstep2 (by norm_num))
      _ = (3/(2*δ)) * (N : ℝ) ^ δ := by rw [mul_div_assoc']; ring
  have h1 : (1:ℝ) ≤ (3/(2*δ)) * (N : ℝ) ^ δ := by
    have hp : (1:ℝ) ≤ 3/(2*δ) := by
      rw [le_div_iff₀ (by positivity)]
      nlinarith [hδle1]
    calc (1:ℝ) = 1 * 1 := by ring
      _ ≤ (3/(2*δ)) * (N : ℝ) ^ δ := mul_le_mul hp hNδ1 (by norm_num) (by positivity)
  have hkey : Real.logb 2 (N : ℝ) + 1 ≤ (3/δ) * (N : ℝ) ^ δ := by
    calc Real.logb 2 (N : ℝ) + 1 ≤ (3/(2*δ)) * (N:ℝ)^δ + (3/(2*δ)) * (N:ℝ)^δ := add_le_add hL h1
      _ = (3/δ) * (N : ℝ) ^ δ := by field_simp; ring
  have hbase : (Nat.log 2 N : ℝ) + 1 ≤ (3/δ) * (N : ℝ) ^ δ :=
    le_trans (add_le_add hlogb le_rfl) hkey
  have hpow : ((Nat.log 2 N : ℝ) + 1) ^ k ≤ (3/δ) ^ k * (N : ℝ) ^ ((k:ℝ) * δ) := by
    calc ((Nat.log 2 N : ℝ) + 1) ^ k ≤ ((3/δ) * (N : ℝ) ^ δ) ^ k :=
          pow_le_pow_left₀ (by positivity) hbase k
      _ = (3/δ) ^ k * ((N : ℝ) ^ δ) ^ k := by rw [mul_pow]
      _ = (3/δ) ^ k * (N : ℝ) ^ ((k:ℝ) * δ) := by
          have : ((N : ℝ) ^ δ) ^ k = (N : ℝ) ^ ((k:ℝ) * δ) := by
            rw [← Real.rpow_natCast ((N:ℝ)^δ) k, ← Real.rpow_mul hNpos.le δ (k:ℝ), mul_comm]
          rw [this]
  have hkδ : (k:ℝ) * δ ≤ ε := by
    have h1 : (k:ℝ) * δ ≤ (k:ℝ) * (ε/(k+2)) :=
      mul_le_mul_of_nonneg_left hδle (Nat.cast_nonneg k)
    have h2 : (k:ℝ) * (ε/(k+2)) ≤ ε := by
      rw [mul_div_assoc', div_le_iff₀ (by positivity)]
      nlinarith [hε]
    linarith
  calc ((Nat.log 2 N : ℝ) + 1) ^ k ≤ (3/δ) ^ k * (N : ℝ) ^ ((k:ℝ) * δ) := hpow
    _ ≤ (3/δ) ^ k * (N : ℝ) ^ ε :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hN1 hkδ) (by positivity)
    _ ≤ max 1 ((3/δ) ^ k) * (N : ℝ) ^ ε :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg hNpos.le ε)

/-! ## The count -/

theorem card_supported_le (K : Type) [Field K] [NumberField K]
    (E : Finset (NK.HeckeL.PrimeIdeal K)) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ,
      (Nat.card {𝔟 : Ideal (NumberField.RingOfIntegers K) //
        𝔟 ≠ 0 ∧ (∀ 𝔭 : NK.HeckeL.PrimeIdeal K, 𝔭.asIdeal ∣ 𝔟 → 𝔭 ∈ E) ∧
        Ideal.absNorm 𝔟 ≤ N} : ℝ) ≤ C * (N : ℝ) ^ ε := by
  classical
  obtain ⟨C, hCpos, hC⟩ := nat_log_bound E.card hε
  refine ⟨C, hCpos, fun N => ?_⟩
  rcases Nat.eq_zero_or_pos N with h0 | hN
  · subst h0
    have hempty : IsEmpty {𝔟 : Ideal (𝓞 K) //
        𝔟 ≠ 0 ∧ (∀ 𝔭 : NK.HeckeL.PrimeIdeal K, 𝔭.asIdeal ∣ 𝔟 → 𝔭 ∈ E) ∧
        Ideal.absNorm 𝔟 ≤ 0} :=
      ⟨fun x => by
        have hz : Ideal.absNorm x.1 = 0 := Nat.eq_zero_of_le_zero x.2.2.2
        have hfin : Finite (𝓞 K ⧸ x.1) :=
          Ideal.finiteQuotientOfFreeOfNeBot x.1 (by simpa using x.2.1)
        exact (Ideal.absNorm_ne_zero_iff x.1).mpr hfin hz⟩
    rw [Nat.card_eq_zero.mpr (Or.inl hempty), Nat.cast_zero, Real.zero_rpow hε.ne']
    simp
  · set M := Nat.log 2 N with hM
    have hcard : Nat.card {𝔟 : Ideal (𝓞 K) //
        𝔟 ≠ 0 ∧ (∀ 𝔭 : NK.HeckeL.PrimeIdeal K, 𝔭.asIdeal ∣ 𝔟 → 𝔭 ∈ E) ∧
        Ideal.absNorm 𝔟 ≤ N} ≤ (M + 1) ^ E.card := by
      have hsum : ∀ x : {𝔟 : Ideal (𝓞 K) //
          𝔟 ≠ 0 ∧ (∀ 𝔭 : NK.HeckeL.PrimeIdeal K, 𝔭.asIdeal ∣ 𝔟 → 𝔭 ∈ E) ∧
          Ideal.absNorm 𝔟 ≤ N},
          (∑ i : {𝔭 : NK.HeckeL.PrimeIdeal K // 𝔭 ∈ E}, expAt x.1 i.1) ≤ M := by
        intro x
        rw [← Finset.sum_subtype E (fun _ => Iff.rfl) (fun 𝔭 => expAt x.1 𝔭), hM]
        exact sum_expAt_le_log x.2.1 x.2.2.1 x.2.2.2
      have hinj : Function.Injective
          (fun x : {𝔟 : Ideal (𝓞 K) //
            𝔟 ≠ 0 ∧ (∀ 𝔭 : NK.HeckeL.PrimeIdeal K, 𝔭.asIdeal ∣ 𝔟 → 𝔭 ∈ E) ∧
            Ideal.absNorm 𝔟 ≤ N} =>
            fun i : {𝔭 : NK.HeckeL.PrimeIdeal K // 𝔭 ∈ E} =>
              (⟨expAt x.1 i.1, by
                have h1 : expAt x.1 i.1 ≤
                    ∑ j : {𝔭 : NK.HeckeL.PrimeIdeal K // 𝔭 ∈ E}, expAt x.1 j.1 :=
                  Finset.single_le_sum
                    (f := fun j : {𝔭 : NK.HeckeL.PrimeIdeal K // 𝔭 ∈ E} => expAt x.1 j.1)
                    (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
                exact Nat.lt_succ_of_le (le_trans h1 (hsum x))⟩ : Fin (M + 1))) := by
        intro x y hxy
        refine Subtype.ext (expAt_injective x.2.1 x.2.2.1 y.2.1 y.2.2.1 fun 𝔭 => ?_)
        exact Fin.ext_iff.mp (congrFun hxy 𝔭)
      calc Nat.card {𝔟 : Ideal (𝓞 K) //
            𝔟 ≠ 0 ∧ (∀ 𝔭 : NK.HeckeL.PrimeIdeal K, 𝔭.asIdeal ∣ 𝔟 → 𝔭 ∈ E) ∧
            Ideal.absNorm 𝔟 ≤ N}
          ≤ Nat.card ({𝔭 : NK.HeckeL.PrimeIdeal K // 𝔭 ∈ E} → Fin (M + 1)) :=
            Nat.card_le_card_of_injective _ hinj
        _ = (M + 1) ^ E.card := by
            rw [Nat.card_pi]
            simp [Nat.card_eq_fintype_card, Finset.prod_const]
    calc (Nat.card {𝔟 : Ideal (𝓞 K) //
        𝔟 ≠ 0 ∧ (∀ 𝔭 : NK.HeckeL.PrimeIdeal K, 𝔭.asIdeal ∣ 𝔟 → 𝔭 ∈ E) ∧
        Ideal.absNorm 𝔟 ≤ N} : ℝ) ≤ (((M + 1) ^ E.card : ℕ) : ℝ) := by exact_mod_cast hcard
      _ = ((M : ℝ) + 1) ^ E.card := by push_cast; ring
      _ = ((Nat.log 2 N : ℝ) + 1) ^ E.card := by rw [hM]
      _ ≤ C * (N : ℝ) ^ ε := hC N hN

end NK.NUV2.RouteB.Unif
