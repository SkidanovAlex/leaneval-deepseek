import Mathlib
import Submission.Work.ZeroDensity.Jutila.grahamDefs
import Submission.Work.ZeroDensity.Jutila.BzApplyPrimePowReal
import Submission.Work.LinnikAreas.Density4.prime_log_gap_sum

namespace Work.ZeroDensity.Jutila

open Finset

noncomputable section

/-!
# The mixed von Mangoldt / correction sum (Graham's `S₂`)

This file proves `MulBzAux`: for real `1 ≤ z ≤ N`,

`Σ_{n ≤ N} Λ(n)·Bz z n + N·log(N/z) = O(N)`,

with an absolute implied constant.  The proof splits the sum into its prime and its non-prime
part:

* the prime part is `-Σ_{z < p ≤ N} log p · log(p/z)`, evaluated to `-N log(N/z) + O(N)` by the
  partial-summation estimate `Work.LinnikAreas.Density4.prime_log_gap_sum`;
* the non-prime part is supported on the prime powers `n = p^k`, `k ≥ 2` (`Λ` vanishes off the
  prime powers), of which there are at most `√N · log₂N`, each of size at most `(log N)²`; hence
  it is `O(√N (log N)³) = O(N)` because `log N ≤ 6 N^{1/6}`.
-/

/-- **The summand is uniformly `O((log N)²)`.**  For `1 ≤ z`, `1 ≤ N` and `n ≤ N`,
`|Λ(n)·Bz z n| ≤ (log N)²`:  `Λ` vanishes unless `n = p^k` is a prime power, where
`Λ(n) = log p` and `Bz z n = -log(p/z)` for `p > z` and `0` otherwise
(`BzApplyPrimePowReal`), and both `log p` and `log(p/z)` are at most `log N`. -/
private lemma MulBzAux_summand_bound {z : ℝ} (hz : 1 ≤ z) {N n : ℕ} (hN : 1 ≤ N)
    (hn : n ≤ N) :
    |ArithmeticFunction.vonMangoldt n * Bz z n| ≤ Real.log (N : ℝ) * Real.log (N : ℝ) := by
  have hzpos : (0 : ℝ) < z := by linarith
  have hlogN0 : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN)
  by_cases hp : IsPrimePow n
  · obtain ⟨p, k, hpp, hk0, hpk⟩ := (isPrimePow_nat_iff n).mp hp
    have hpN : (p : ℝ) ≤ (N : ℝ) := by
      have h1 : p ≤ p ^ k := Nat.le_self_pow hk0.ne' p
      have : p ≤ N := by omega
      exact_mod_cast this
    have hlogp0 : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast hpp.one_le)
    have hlogpN : Real.log (p : ℝ) ≤ Real.log (N : ℝ) :=
      Real.log_le_log (by exact_mod_cast hpp.pos) hpN
    have hΛ : ArithmeticFunction.vonMangoldt n = Real.log (p : ℝ) := by
      rw [← hpk, ArithmeticFunction.vonMangoldt_apply_pow hk0.ne',
        ArithmeticFunction.vonMangoldt_apply_prime hpp]
    have hBz : Bz z n = if z < (p : ℝ) then -Real.log ((p : ℝ) / z) else 0 := by
      rw [← hpk]
      exact BzApplyPrimePowReal hz hpp hk0
    rw [hΛ, hBz]
    by_cases hzp : z < (p : ℝ)
    · rw [if_pos hzp]
      have hpz1 : 1 ≤ (p : ℝ) / z := by
        rw [le_div_iff₀ hzpos]
        linarith [hzp.le]
      have hlogpz0 : 0 ≤ Real.log ((p : ℝ) / z) := Real.log_nonneg hpz1
      have hlogpzN : Real.log ((p : ℝ) / z) ≤ Real.log (N : ℝ) := by
        refine Real.log_le_log (by positivity) ?_
        rw [div_le_iff₀ hzpos]
        nlinarith [hpN, hz]
      have h1 : |Real.log (p : ℝ) * (-Real.log ((p : ℝ) / z))|
          = Real.log (p : ℝ) * Real.log ((p : ℝ) / z) := by
        rw [abs_mul, abs_neg, abs_of_nonneg hlogp0, abs_of_nonneg hlogpz0]
      rw [h1]
      calc Real.log (p : ℝ) * Real.log ((p : ℝ) / z)
          ≤ Real.log (N : ℝ) * Real.log ((p : ℝ) / z) :=
            mul_le_mul_of_nonneg_right hlogpN hlogpz0
        _ ≤ Real.log (N : ℝ) * Real.log (N : ℝ) :=
            mul_le_mul_of_nonneg_left hlogpzN hlogN0
    · rw [if_neg hzp, mul_zero, abs_zero]
      exact mul_self_nonneg _
  · rw [ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hp, zero_mul, abs_zero]
    exact mul_self_nonneg _

/-- **Counting the non-prime prime powers.**  The number of `n ≤ N` that are not prime but are
prime powers is at most `√N · log₂N`:  such an `n` is `p^k` with `p` prime, `k ≥ 2` (so `p ≤ √N`),
and `2^k ≤ p^k = n ≤ N` (so `k ≤ Nat.log 2 N`); the map `(p, k) ↦ p^k` sends the `≤ √N · log₂N`
pairs `(p, k)` with `p ≤ √N` prime and `2 ≤ k ≤ log₂N` onto the set. -/
private lemma MulBzAux_card_le (N : ℕ) :
    (((Finset.Icc 1 N).filter (fun n => ¬ Nat.Prime n ∧ IsPrimePow n)).card : ℝ)
      ≤ (Nat.sqrt N : ℝ) * (Nat.log 2 N : ℝ) := by
  set U : Finset ℕ := (Finset.Icc 1 N).filter (fun n => ¬ Nat.Prime n ∧ IsPrimePow n) with hU
  set P : Finset ℕ := (Finset.Icc 2 (Nat.sqrt N)).filter Nat.Prime with hP
  set K : Finset ℕ := Finset.Icc 2 (Nat.log 2 N) with hK
  have hsub : U ⊆ (P ×ˢ K).image (fun pk : ℕ × ℕ => pk.1 ^ pk.2) := by
    intro x hx
    rw [hU, Finset.mem_filter, Finset.mem_Icc] at hx
    obtain ⟨⟨_, hxN⟩, hxnp, hxpp⟩ := hx
    obtain ⟨p, k, hpp, hk0, hpk⟩ := (isPrimePow_nat_iff x).mp hxpp
    have hk2 : 2 ≤ k := by
      by_contra h
      have hk1 : k = 1 := by omega
      rw [hk1, pow_one] at hpk
      exact hxnp (hpk ▸ hpp)
    have hp2 : 2 ≤ p := hpp.two_le
    have hpsq : p * p ≤ N := by
      have h1 : p ^ 2 ≤ p ^ k := Nat.pow_le_pow_right hpp.pos hk2
      have h2 : p ^ 2 ≤ N := by omega
      simpa [pow_two] using h2
    have hpsqrt : p ≤ Nat.sqrt N := Nat.le_sqrt.mpr hpsq
    have hklog : k ≤ Nat.log 2 N := by
      have h2k : 2 ^ k ≤ N := by
        have h1 : 2 ^ k ≤ p ^ k := Nat.pow_le_pow_left hp2 k
        omega
      exact Nat.le_log_of_pow_le (by norm_num) h2k
    refine Finset.mem_image.mpr ⟨(p, k), ?_, hpk⟩
    refine Finset.mem_product.mpr ⟨?_, ?_⟩
    · rw [hP, Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨hp2, hpsqrt⟩, hpp⟩
    · rw [hK, Finset.mem_Icc]
      exact ⟨hk2, hklog⟩
  have h1 : U.card ≤ ((P ×ˢ K).image (fun pk : ℕ × ℕ => pk.1 ^ pk.2)).card :=
    Finset.card_le_card hsub
  have h2 : ((P ×ˢ K).image (fun pk : ℕ × ℕ => pk.1 ^ pk.2)).card ≤ (P ×ˢ K).card :=
    Finset.card_image_le
  have h3 : (P ×ˢ K).card ≤ Nat.sqrt N * Nat.log 2 N := by
    rw [Finset.card_product, hP, hK]
    have ha : ((Finset.Icc 2 (Nat.sqrt N)).filter Nat.Prime).card ≤ Nat.sqrt N := by
      calc ((Finset.Icc 2 (Nat.sqrt N)).filter Nat.Prime).card
          ≤ (Finset.Icc 2 (Nat.sqrt N)).card := Finset.card_filter_le _ _
        _ = Nat.sqrt N + 1 - 2 := Nat.card_Icc 2 (Nat.sqrt N)
        _ ≤ Nat.sqrt N := by omega
    have hb : (Finset.Icc 2 (Nat.log 2 N)).card ≤ Nat.log 2 N := by
      rw [Nat.card_Icc]; omega
    exact Nat.mul_le_mul ha hb
  have h4 : U.card ≤ Nat.sqrt N * Nat.log 2 N := le_trans h1 (le_trans h2 h3)
  exact_mod_cast h4

/-- **The numerical bound.**  `(log N)² · √N · log₂N ≤ (216/log 2) · N` for `1 ≤ N`:
`log x ≤ 6 x^{1/6}` (from `Real.log_le_rpow_div`), hence `(log N)³ ≤ 216 √N`, while
`Nat.log 2 N ≤ log N / log 2`. -/
private lemma MulBzAux_log_bound (N : ℕ) (hN : 1 ≤ N) :
    Real.log (N : ℝ) * Real.log (N : ℝ) * Real.sqrt (N : ℝ) * (Nat.log 2 N : ℝ)
      ≤ (216 / Real.log 2) * (N : ℝ) := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := le_of_lt hNpos
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogN0 : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN)
  have hsqrtnn : 0 ≤ Real.sqrt (N : ℝ) := Real.sqrt_nonneg _
  have hLle : (Nat.log 2 N : ℝ) ≤ Real.log (N : ℝ) / Real.log 2 := by
    have h2L : 2 ^ Nat.log 2 N ≤ N := Nat.pow_log_le_self 2 (by omega)
    have hlog2L : Real.log ((2 : ℝ) ^ Nat.log 2 N) ≤ Real.log (N : ℝ) :=
      Real.log_le_log (by positivity) (by exact_mod_cast h2L)
    rw [Real.log_pow] at hlog2L
    exact (le_div_iff₀ hlog2pos).mpr (by linarith)
  have hlog6 : Real.log (N : ℝ) ≤ 6 * (N : ℝ) ^ (1 / 6 : ℝ) := by
    have h := Real.log_le_rpow_div hN0 (by norm_num : (0 : ℝ) < 1 / 6)
    have he : (N : ℝ) ^ (1 / 6 : ℝ) / (1 / 6 : ℝ) = 6 * (N : ℝ) ^ (1 / 6 : ℝ) := by
      rw [div_eq_mul_inv, show ((1 : ℝ) / 6)⁻¹ = 6 by norm_num]
      ring
    linarith [h, he.le, he.ge]
  set x : ℝ := (N : ℝ) ^ (1 / 6 : ℝ) with hx
  have hx0 : 0 ≤ x := by rw [hx]; exact Real.rpow_nonneg hN0 _
  have h6x0 : 0 ≤ 6 * x := by linarith
  have hcube : Real.log (N : ℝ) * Real.log (N : ℝ) * Real.log (N : ℝ)
      ≤ 216 * Real.sqrt (N : ℝ) := by
    have h1 : Real.log (N : ℝ) * Real.log (N : ℝ) * Real.log (N : ℝ)
        ≤ (6 * x) * (6 * x) * (6 * x) := by
      have ha : Real.log (N : ℝ) * Real.log (N : ℝ) ≤ (6 * x) * (6 * x) :=
        mul_le_mul hlog6 hlog6 hlogN0 h6x0
      exact mul_le_mul ha hlog6 hlogN0 (mul_nonneg h6x0 h6x0)
    have hx3 : x * x * x = Real.sqrt (N : ℝ) := by
      have hxx : x * x = (N : ℝ) ^ (1 / 3 : ℝ) := by
        rw [hx, ← Real.rpow_add hNpos (1 / 6 : ℝ) (1 / 6 : ℝ)]
        norm_num
      have hxxx : x * x * x = (N : ℝ) ^ (1 / 2 : ℝ) := by
        rw [hxx, hx, ← Real.rpow_add hNpos (1 / 3 : ℝ) (1 / 6 : ℝ)]
        norm_num
      rw [hxxx, Real.sqrt_eq_rpow]
    have h2 : (6 * x) * (6 * x) * (6 * x) = 216 * Real.sqrt (N : ℝ) := by
      rw [← hx3]
      ring
    linarith [h1, h2.le, h2.ge]
  have hsq : Real.sqrt (N : ℝ) * Real.sqrt (N : ℝ) = (N : ℝ) := Real.mul_self_sqrt hN0
  have hstep : Real.log (N : ℝ) * Real.log (N : ℝ) * Real.sqrt (N : ℝ) * (Nat.log 2 N : ℝ)
      ≤ Real.log (N : ℝ) * Real.log (N : ℝ) * Real.sqrt (N : ℝ)
          * (Real.log (N : ℝ) / Real.log 2) :=
    mul_le_mul_of_nonneg_left hLle (mul_nonneg (mul_self_nonneg _) hsqrtnn)
  have hstep2 : Real.log (N : ℝ) * Real.log (N : ℝ) * Real.sqrt (N : ℝ)
        * (Real.log (N : ℝ) / Real.log 2)
      = (Real.log (N : ℝ) * Real.log (N : ℝ) * Real.log (N : ℝ)) * Real.sqrt (N : ℝ)
          / Real.log 2 := by ring
  have hstep3 : (Real.log (N : ℝ) * Real.log (N : ℝ) * Real.log (N : ℝ)) * Real.sqrt (N : ℝ)
        / Real.log 2
      ≤ (216 * Real.sqrt (N : ℝ)) * Real.sqrt (N : ℝ) / Real.log 2 :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hcube hsqrtnn) hlog2pos.le
  have hstep4 : (216 * Real.sqrt (N : ℝ)) * Real.sqrt (N : ℝ) / Real.log 2
      = (216 / Real.log 2) * (N : ℝ) := by
    have h1 : (216 * Real.sqrt (N : ℝ)) * Real.sqrt (N : ℝ) = 216 * (N : ℝ) := by
      rw [mul_assoc, hsq]
    rw [h1, div_mul_eq_mul_div]
  linarith [hstep, hstep2.le, hstep2.ge, hstep3, hstep4.le, hstep4.ge]

/-- **The non-prime part of the mixed sum is `O(N)`**, uniformly in `z ≥ 1`.  `Λ` is supported on
prime powers, so the non-prime terms are exactly the `n = p^k` with `k ≥ 2` and `p > z`, whose
size is at most `(log N)²`; there are at most `√N log₂N` of them (`MulBzAux_card_le`). -/
private theorem MulBzAux_nonprime_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℝ, 1 ≤ z → ∀ N : ℕ, 1 ≤ N → z ≤ (N : ℝ) →
      |∑ n ∈ (Finset.Icc 1 N).filter (fun n => ¬ Nat.Prime n),
        ArithmeticFunction.vonMangoldt n * Bz z n| ≤ C * (N : ℝ) := by
  refine ⟨216 / Real.log 2 + 1, by
    have h : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have h2 : 0 < 216 / Real.log 2 := by positivity
    linarith, ?_⟩
  intro z hz N hN hzN
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  set B : Finset ℕ := (Finset.Icc 1 N).filter (fun n => ¬ Nat.Prime n) with hB
  set A : Finset ℕ := (Finset.Icc 1 N).filter (fun n => ¬ Nat.Prime n ∧ IsPrimePow n) with hA
  have hEq : ∑ n ∈ B, |ArithmeticFunction.vonMangoldt n * Bz z n|
      = ∑ n ∈ A, |ArithmeticFunction.vonMangoldt n * Bz z n| := by
    refine (Finset.sum_subset ?_ ?_).symm
    · intro n hn
      simp only [hA, hB, Finset.mem_filter] at hn ⊢
      exact ⟨hn.1, hn.2.1⟩
    · intro n hnB hnA
      simp only [hA, hB, Finset.mem_filter] at hnB hnA
      have hni : ¬ IsPrimePow n := fun h => hnA ⟨hnB.1, hnB.2, h⟩
      rw [ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hni, zero_mul, abs_zero]
  have hle : ∑ n ∈ A, |ArithmeticFunction.vonMangoldt n * Bz z n|
      ≤ ∑ _n ∈ A, Real.log (N : ℝ) * Real.log (N : ℝ) := by
    refine Finset.sum_le_sum (fun n hn => ?_)
    rw [hA, Finset.mem_filter, Finset.mem_Icc] at hn
    exact MulBzAux_summand_bound hz hN hn.1.2
  have hconst : ∑ _n ∈ A, Real.log (N : ℝ) * Real.log (N : ℝ)
      = (A.card : ℝ) * (Real.log (N : ℝ) * Real.log (N : ℝ)) := by
    rw [Finset.sum_const, nsmul_eq_mul]
  have hcard : (A.card : ℝ) ≤ (Nat.sqrt N : ℝ) * (Nat.log 2 N : ℝ) := by
    rw [hA]; exact MulBzAux_card_le N
  calc |∑ n ∈ B, ArithmeticFunction.vonMangoldt n * Bz z n|
      ≤ ∑ n ∈ B, |ArithmeticFunction.vonMangoldt n * Bz z n| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ n ∈ A, |ArithmeticFunction.vonMangoldt n * Bz z n| := hEq
    _ ≤ ∑ _n ∈ A, Real.log (N : ℝ) * Real.log (N : ℝ) := hle
    _ = (A.card : ℝ) * (Real.log (N : ℝ) * Real.log (N : ℝ)) := hconst
    _ ≤ ((Nat.sqrt N : ℝ) * (Nat.log 2 N : ℝ)) * (Real.log (N : ℝ) * Real.log (N : ℝ)) :=
        mul_le_mul_of_nonneg_right hcard (mul_self_nonneg _)
    _ = Real.log (N : ℝ) * Real.log (N : ℝ) * (Nat.sqrt N : ℝ) * (Nat.log 2 N : ℝ) := by ring
    _ ≤ Real.log (N : ℝ) * Real.log (N : ℝ) * Real.sqrt (N : ℝ) * (Nat.log 2 N : ℝ) := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ (mul_self_nonneg _))
          (Nat.cast_nonneg _)
        calc (Nat.sqrt N : ℝ)
            = Real.sqrt ((Nat.sqrt N : ℝ) * (Nat.sqrt N : ℝ)) :=
              (Real.sqrt_mul_self (Nat.cast_nonneg (Nat.sqrt N))).symm
          _ ≤ Real.sqrt (N : ℝ) := Real.sqrt_le_sqrt (by exact_mod_cast Nat.sqrt_le N)
    _ ≤ (216 / Real.log 2) * (N : ℝ) := MulBzAux_log_bound N hN
    _ ≤ (216 / Real.log 2 + 1) * (N : ℝ) := by nlinarith [hNpos]

/-- **The prime part of the mixed sum.**  For `z ≥ 1` and any `N`, only the primes `p > z` in
`[1,N]` contribute, with `Λ(p) = log p` and `Bz z p = -log(p/z)`. -/
private lemma MulBzAux_prime_part (z : ℝ) (hz : 1 ≤ z) (N : ℕ) :
    (∑ n ∈ (Finset.Icc 1 N).filter Nat.Prime, ArithmeticFunction.vonMangoldt n * Bz z n)
      = - (∑ p ∈ (Finset.Icc 1 N).filter (fun p => Nat.Prime p ∧ z < (p : ℝ)),
            Real.log (p : ℝ) * Real.log ((p : ℝ) / z)) := by
  rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  by_cases hP : Nat.Prime n
  · have hBz : Bz z n = if z < (n : ℝ) then -Real.log ((n : ℝ) / z) else 0 := by
      simpa using BzApplyPrimePowReal (z := z) hz (p := n) (k := 1) hP le_rfl
    rw [if_pos hP, ArithmeticFunction.vonMangoldt_apply_prime hP, hBz]
    by_cases hzn : z < (n : ℝ)
    · rw [if_pos hzn, if_pos ⟨hP, hzn⟩]
      ring
    · rw [if_neg hzn, if_neg (fun h => hzn h.2)]
      ring
  · rw [if_neg hP, if_neg (fun h => hP h.1)]
    ring

/-- **The prime sum is the main term.**  `Σ_{z < p ≤ N} log p · log(p/z) = N log(N/z) + O(N)`,
uniformly for `1 ≤ z ≤ N`, a direct consequence of the partial-summation estimate
`Work.LinnikAreas.Density4.prime_log_gap_sum`. -/
private lemma MulBzAux_prime_main :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℝ, 1 ≤ z → ∀ N : ℕ, z ≤ (N : ℝ) →
      |(∑ p ∈ (Finset.Icc 1 N).filter (fun p => Nat.Prime p ∧ z < (p : ℝ)),
          Real.log (p : ℝ) * Real.log ((p : ℝ) / z)) - (N : ℝ) * Real.log ((N : ℝ) / z)|
        ≤ C * (N : ℝ) := by
  obtain ⟨C, hCpos, hC⟩ := Work.LinnikAreas.Density4.prime_log_gap_sum
  refine ⟨C, hCpos, ?_⟩
  intro z hz N hzN
  have h := hC z (N : ℝ) hz hzN
  rw [Nat.floor_natCast] at h
  simpa using h

/-- **The mixed von Mangoldt / correction sum** (Graham's `S₂` term).  For real `1 ≤ z ≤ N`,
`Σ_{n ≤ N} Λ(n)·Bz z n = −N·log(N/z) + O(N)` with an absolute implied constant, where
`Bz z n = Σ_{d ∣ n, z < d} μ(d)·log(d/z)` (`grahamDefs.lean`).

The sum is supported on the prime powers `n = p^k` with `z < p`, where `Bz z (p^k) = −log(p/z)`
(`Work.LinnikAreas.Density4.Bz_apply_prime_pow` in `vonMangoldt_mul_Bz_sum.lean`, proved), so the
claim is exactly `Σ_{z < p^k ≤ N}(log p)(log(p/z)) = N log(N/z) + O(N)`:
* the primes give `Σ_{z<p≤N}(log p)log(p/z) = ∫_z^N log(t/z)dθ(t) = log(N/z)θ(N) − ∫_z^N θ(t)/t dt
  = N log(N/z) + O(N)` by partial summation from `θ(x) = x + O(x/log x)`
  (`Commons.NumberTheory.Zeta.psi_sub_id_powLog_real` and the PNT bounds of
  `Commons.NumberTheory.Chebyshev`; the workspace has the tools `prime_log_sum_repr` and
  `interval_integrable_theta_div`);
* the prime powers `k ≥ 2` with `p > z`, `p^k ≤ N` contribute at most
  `Σ_{p ≤ √N} log p·(log N/log p)·log N ≤ √N log²N = O(N)`, uniformly in `z`
  (an absolute bound; note such `p` automatically satisfy `p > z` when `p^k ≤ N < z²`).
The identity for the hard range `N < z²` (no `k ≥ 2` terms) is
`Work.LinnikAreas.Density4.vonMangoldt_mul_Bz_sum`, proved. -/
theorem MulBzAux :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℝ, 1 ≤ z → ∀ N : ℕ, z ≤ (N : ℝ) →
      |(∑ n ∈ Finset.Icc 1 N, ArithmeticFunction.vonMangoldt n * Bz z n)
        + (N : ℝ) * Real.log ((N : ℝ) / z)| ≤ C * (N : ℝ) := by
  obtain ⟨C1, hC1pos, hC1⟩ := MulBzAux_prime_main
  obtain ⟨C2, hC2pos, hC2⟩ := MulBzAux_nonprime_bound
  refine ⟨C1 + C2 + 1, by linarith, ?_⟩
  intro z hz N hzN
  have hN : 1 ≤ N := by
    have : (1 : ℝ) ≤ (N : ℝ) := le_trans hz hzN
    exact_mod_cast this
  have hNnn : (0 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (by omega : 0 ≤ N)
  have hsplit : (∑ n ∈ Finset.Icc 1 N, ArithmeticFunction.vonMangoldt n * Bz z n)
      = (∑ n ∈ (Finset.Icc 1 N).filter Nat.Prime,
          ArithmeticFunction.vonMangoldt n * Bz z n)
        + (∑ n ∈ (Finset.Icc 1 N).filter (fun n => ¬ Nat.Prime n),
            ArithmeticFunction.vonMangoldt n * Bz z n) :=
    (Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 N) Nat.Prime
      (fun n => ArithmeticFunction.vonMangoldt n * Bz z n)).symm
  have hp := MulBzAux_prime_part z hz N
  have hm := hC1 z hz N hzN
  have hr := hC2 z hz N hN hzN
  rw [hsplit, hp]
  have hEq : -(∑ p ∈ (Finset.Icc 1 N).filter (fun p => Nat.Prime p ∧ z < (p : ℝ)),
          Real.log (p : ℝ) * Real.log ((p : ℝ) / z))
        + (∑ n ∈ (Finset.Icc 1 N).filter (fun n => ¬ Nat.Prime n),
            ArithmeticFunction.vonMangoldt n * Bz z n)
        + (N : ℝ) * Real.log ((N : ℝ) / z)
      = (∑ n ∈ (Finset.Icc 1 N).filter (fun n => ¬ Nat.Prime n),
            ArithmeticFunction.vonMangoldt n * Bz z n)
        - ((∑ p ∈ (Finset.Icc 1 N).filter (fun p => Nat.Prime p ∧ z < (p : ℝ)),
              Real.log (p : ℝ) * Real.log ((p : ℝ) / z))
            - (N : ℝ) * Real.log ((N : ℝ) / z)) := by ring
  rw [hEq]
  calc |(∑ n ∈ (Finset.Icc 1 N).filter (fun n => ¬ Nat.Prime n),
            ArithmeticFunction.vonMangoldt n * Bz z n)
        - ((∑ p ∈ (Finset.Icc 1 N).filter (fun p => Nat.Prime p ∧ z < (p : ℝ)),
              Real.log (p : ℝ) * Real.log ((p : ℝ) / z))
            - (N : ℝ) * Real.log ((N : ℝ) / z))|
      ≤ |(∑ n ∈ (Finset.Icc 1 N).filter (fun n => ¬ Nat.Prime n),
            ArithmeticFunction.vonMangoldt n * Bz z n)|
        + |(∑ p ∈ (Finset.Icc 1 N).filter (fun p => Nat.Prime p ∧ z < (p : ℝ)),
              Real.log (p : ℝ) * Real.log ((p : ℝ) / z))
            - (N : ℝ) * Real.log ((N : ℝ) / z)| := by
        simpa [Real.dist_eq, sub_zero, zero_sub, abs_neg] using (dist_triangle _ (0 : ℝ) _)
    _ ≤ C2 * (N : ℝ) + C1 * (N : ℝ) := add_le_add hr hm
    _ ≤ (C1 + C2 + 1) * (N : ℝ) := by nlinarith [hNnn]

end

end Work.ZeroDensity.Jutila
