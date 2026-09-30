import Mathlib

import Submission.Work.BMF.mr_direct.card_has_prime_factor_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.mr_direct

open Finset

/-- The number of `n ∈ ℕ ∩ [A,B]` having a prime divisor in `[P,Q]` is at most
`12 B (1/K + 1/P)`, provided the interval `[P,Q]` is `K`-short: `K log(Q/P) < 1`.

This is the general-range analogue of `card_has_prime_factor_le` (which covers the dyadic
range `[X, 2X]`); the same elementary argument applies: the set of such `n` is contained in
the union of the arithmetic progressions of multiples of the primes `p ∈ [P,Q]`, the `p`-th of
these has at most `⌊B⌋₊ / p ≤ B / P` elements, and the interval `[P,Q]` contains at most
`3P/K + 1` primes. -/
theorem card_has_prime_factorR_le (A B K P Q : ℝ) (hA : 1 ≤ A) (hB : 1 ≤ B) (hK : 1 ≤ K)
    (hP : 2 ≤ P) (hPQ : P ≤ Q) (hsmall : K * Real.log (Q / P) < 1) :
    ((Work.BMF.natIcc A B).filter
        (fun n => ∃ p ∈ Work.BMF.mrDirect.primeSet P Q, p ∣ n)).card
      ≤ 12 * B * (1 / K + 1 / P) := by
  have hApos : 0 < A := by linarith
  have hKpos : 0 < K := by linarith
  have hPpos : 0 < P := by linarith
  have hQ0 : 0 ≤ Q := by linarith
  have hQpos : 0 < Q := by linarith
  have hB0 : 0 ≤ B := by linarith
  set S : Finset ℕ := Work.BMF.mrDirect.primeSet P Q with hS
  have hmemS : ∀ p : ℕ, p ∈ S ↔ p.Prime ∧ P ≤ (p : ℝ) ∧ (p : ℝ) ≤ Q := by
    intro p; rw [hS, Work.BMF.mrDirect.mem_primeSet hQ0]
  -- Step 1: the set of `n` is contained in the union of the `p`-multiples.
  have hsub : (Work.BMF.natIcc A B).filter (fun n => ∃ p ∈ S, p ∣ n) ⊆
      S.biUnion (fun p => (Work.BMF.natIcc A B).filter (fun n => p ∣ n)) := by
    intro n hn
    rw [Finset.mem_filter] at hn
    obtain ⟨hnN, p, hpS, hpd⟩ := hn
    exact Finset.mem_biUnion.mpr ⟨p, hpS, Finset.mem_filter.mpr ⟨hnN, hpd⟩⟩
  have hcard_nat : ((Work.BMF.natIcc A B).filter (fun n => ∃ p ∈ S, p ∣ n)).card
      ≤ ∑ p ∈ S, ⌊B⌋₊ / p := by
    calc ((Work.BMF.natIcc A B).filter (fun n => ∃ p ∈ S, p ∣ n)).card
        ≤ (S.biUnion (fun p => (Work.BMF.natIcc A B).filter (fun n => p ∣ n))).card :=
          Finset.card_le_card hsub
      _ ≤ ∑ p ∈ S, ((Work.BMF.natIcc A B).filter (fun n => p ∣ n)).card :=
          Finset.card_biUnion_le
      _ ≤ ∑ p ∈ S, ⌊B⌋₊ / p := by
          apply Finset.sum_le_sum
          intro p _
          exact card_filter_dvd_le_floor A B p hApos
  -- Step 2: sum bound, each prime `p ≥ P` contributes `≤ B/P`.
  have hsum_le : ((∑ p ∈ S, ⌊B⌋₊ / p : ℕ) : ℝ) ≤ (S.card : ℝ) * (B / P) := by
    have h1 : ((∑ p ∈ S, ⌊B⌋₊ / p : ℕ) : ℝ) ≤ ∑ p ∈ S, (B / P) := by
      rw [Nat.cast_sum]
      apply Finset.sum_le_sum
      intro p hp
      obtain ⟨hpp, hPp, _⟩ := (hmemS p).mp hp
      have hppos : 0 < (p : ℝ) := by exact_mod_cast hpp.pos
      calc ((⌊B⌋₊ / p : ℕ) : ℝ) ≤ (⌊B⌋₊ : ℝ) / (p : ℝ) := Nat.cast_div_le
        _ ≤ B / (p : ℝ) := by
            apply div_le_div_of_nonneg_right _ hppos.le
            exact Nat.floor_le hB0
        _ ≤ B / P := div_le_div_of_nonneg_left hB0 hPpos hPp
    have h2 : (∑ p ∈ S, (B / P)) = (S.card : ℝ) * (B / P) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    rw [h2] at h1; exact h1
  -- Step 3: `[P, Q]` is short, so `Q - P ≤ 3P/K`.
  have h3 : Q - P ≤ 3 * P / K := by
    have hratio0 : 0 < Q / P := div_pos hQpos hPpos
    have hlog : Real.log (Q / P) < 1 / K := by
      rw [lt_div_iff₀ hKpos]; linarith [hsmall]
    have hlog1 : Real.log (Q / P) < 1 := by
      have h1k : 1 / K ≤ 1 := by rw [div_le_one hKpos]; linarith
      linarith
    have hQP_lt : Q / P < Real.exp 1 := (Real.log_lt_iff_lt_exp hratio0).mp hlog1
    have hQlt : Q < 3 * P := by
      have h1 : Q / P < 3 := lt_trans hQP_lt Real.exp_one_lt_three
      have h2 : Q / P * P < 3 * P := mul_lt_mul_of_pos_right h1 hPpos
      rwa [div_mul_cancel₀ Q (ne_of_gt hPpos)] at h2
    have hineq : 1 - P / Q < 1 / K := by
      have h := Real.one_sub_inv_le_log_of_pos hratio0
      rw [inv_div] at h
      linarith
    have hQP : Q - P < Q / K := by
      have h1 : (1 - P / Q) * Q < (1 / K) * Q := mul_lt_mul_of_pos_right hineq hQpos
      have e1 : (1 - P / Q) * Q = Q - P := by
        rw [sub_mul, one_mul, div_mul_cancel₀ P (ne_of_gt hQpos)]
      have e2 : (1 / K) * Q = Q / K := by ring
      linarith
    have hdiv : Q / K < 3 * P / K := div_lt_div_of_pos_right hQlt hKpos
    linarith
  -- Step 4: at most `3P/K + 1` primes in `[P, Q]`.
  have hScard : (S.card : ℝ) ≤ 3 * P / K + 1 := by
    have hSsub : S ⊆ Finset.Icc ⌈P⌉₊ ⌊Q⌋₊ := by
      rw [hS, Work.BMF.mrDirect.primeSet]
      exact Finset.filter_subset _ _
    have h1 : S.card ≤ (Finset.Icc ⌈P⌉₊ ⌊Q⌋₊).card := Finset.card_le_card hSsub
    calc (S.card : ℝ) ≤ ((Finset.Icc ⌈P⌉₊ ⌊Q⌋₊).card : ℝ) := by exact_mod_cast h1
      _ ≤ Q - P + 1 := card_Icc_real_le P Q hQ0 hPQ
      _ ≤ 3 * P / K + 1 := by linarith
  -- Step 5: elementary arithmetic.
  have hfinal : (3 * P / K + 1) * (B / P) ≤ 12 * B * (1 / K + 1 / P) := by
    have e1 : (3 * P / K + 1) * (B / P) = 3 * (B / K) + B / P := by
      field_simp
    have e2 : 12 * B * (1 / K + 1 / P) = 12 * (B / K) + 12 * (B / P) := by
      ring
    rw [e1, e2]
    have h1 : (0 : ℝ) ≤ B / K := div_nonneg hB0 hKpos.le
    have h2 : (0 : ℝ) ≤ B / P := div_nonneg hB0 hPpos.le
    linarith
  calc (((Work.BMF.natIcc A B).filter (fun n => ∃ p ∈ S, p ∣ n)).card : ℝ)
      ≤ ((∑ p ∈ S, ⌊B⌋₊ / p : ℕ) : ℝ) := by exact_mod_cast hcard_nat
    _ ≤ (S.card : ℝ) * (B / P) := hsum_le
    _ ≤ (3 * P / K + 1) * (B / P) :=
        mul_le_mul_of_nonneg_right hScard (div_nonneg hB0 hPpos.le)
    _ ≤ 12 * B * (1 / K + 1 / P) := hfinal

end Work.BMF.mr_direct
