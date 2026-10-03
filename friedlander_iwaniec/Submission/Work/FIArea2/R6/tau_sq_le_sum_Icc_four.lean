/-
# `FIArea2/R6/tau_sq_le_sum_Icc_four` — FI Lemma 2.2 (`k = 4`) for `τ²`

For `m ≤ K⁴`,

  `τ(m)² ≤ 65536 · Σ_{1 ≤ d ≤ K, d ∣ m} τ(d)¹⁶`.

Indeed Lemma 2.2 (`Work.FIArea3.lemma_2_2`) with `k = 4` supplies `d ∣ m` with `d⁴ ≤ m` and
`τ(m) ≤ (2τ(d))^{4 log 4/log 2} = (2τ(d))⁸`; squaring gives `τ(m)² ≤ (2τ(d))¹⁶ = 65536 τ(d)¹⁶`,
and `d⁴ ≤ m ≤ K⁴` gives `d ≤ K`, so `τ(d)¹⁶` is one of the (nonnegative) terms of the sum.
-/
import Mathlib
import Submission.Work.FIArea3.lemma_2_2
import Submission.Work.FIArea3.joint_tau_reduction

set_option maxHeartbeats 2000000

open Finset
open scoped BigOperators

namespace Work.FIArea2.R6

/-- **FI Lemma 2.2 with `k = 4`, squared form.** -/
theorem tau_sq_le_sum_Icc_four (m K : ℕ) (hK : 1 ≤ K) (h : (m : ℝ) ≤ (K : ℝ) ^ (4 : ℕ)) :
    (((m.divisors.card : ℕ) : ℝ)) ^ (2 : ℕ)
      ≤ 65536 * ∑ d ∈ Finset.Icc 1 K,
          (if d ∣ m then ((((d.divisors.card : ℕ) : ℝ)) ^ (16 : ℕ)) else 0) := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    rw [Nat.divisors_zero, Finset.card_empty, Nat.cast_zero]
    have h0 : (0 : ℝ) ≤ ∑ d ∈ Finset.Icc 1 K,
        (if d ∣ 0 then ((((d.divisors.card : ℕ) : ℝ)) ^ (16 : ℕ)) else 0) :=
      Finset.sum_nonneg (fun i _ => by split_ifs <;> positivity)
    have hz : ((0 : ℝ)) ^ (2 : ℕ) = 0 := by norm_num
    rw [hz]
    exact mul_nonneg (by norm_num) h0
  · obtain ⟨d, hdvd, hdk, hbound⟩ := Work.FIArea3.lemma_2_2 (k := 4) (by norm_num) hm
    rw [Work.FIArea3.exp_eq_eight, Real.rpow_natCast] at hbound
    have hd4 : ((d : ℝ)) ^ 4 ≤ (m : ℝ) := by exact_mod_cast hdk
    have hdK4 : ((d : ℝ)) ^ 4 ≤ (K : ℝ) ^ 4 := le_trans hd4 h
    have hdK : d ≤ K := by
      have := (pow_le_pow_iff_left₀ (show (0 : ℝ) ≤ (d : ℝ) by positivity)
        (show (0 : ℝ) ≤ (K : ℝ) by positivity) (by norm_num : (4 : ℕ) ≠ 0)).mp hdK4
      exact_mod_cast this
    have hd1 : 1 ≤ d := Nat.pos_of_dvd_of_pos hdvd hm
    have hmem : d ∈ Finset.Icc 1 K := Finset.mem_Icc.mpr ⟨hd1, hdK⟩
    have hsingle : (if d ∣ m then ((((d.divisors.card : ℕ) : ℝ)) ^ (16 : ℕ)) else 0)
        ≤ ∑ d' ∈ Finset.Icc 1 K,
            (if d' ∣ m then ((((d'.divisors.card : ℕ) : ℝ)) ^ (16 : ℕ)) else 0) :=
      Finset.single_le_sum (s := Finset.Icc 1 K)
        (f := fun d' => if d' ∣ m then ((((d'.divisors.card : ℕ) : ℝ)) ^ (16 : ℕ)) else 0)
        (by intro i _
            by_cases h : i ∣ m
            · simp only [h, if_true]; positivity
            · simp only [h, if_false]; norm_num) hmem
    rw [if_pos hdvd] at hsingle
    have hb2 : ((m.divisors.card : ℝ)) ^ (2 : ℕ)
        ≤ (2 * (d.divisors.card : ℝ)) ^ (16 : ℕ) := by
      calc ((m.divisors.card : ℝ)) ^ (2 : ℕ)
          ≤ ((2 * (d.divisors.card : ℝ)) ^ (8 : ℕ)) ^ (2 : ℕ) :=
            pow_le_pow_left₀ (by positivity) hbound 2
        _ = (2 * (d.divisors.card : ℝ)) ^ (16 : ℕ) := by rw [← pow_mul]
    have hb3 : (2 * (d.divisors.card : ℝ)) ^ (16 : ℕ)
        = 65536 * ((d.divisors.card : ℝ)) ^ (16 : ℕ) := by ring
    rw [hb3] at hb2
    calc ((m.divisors.card : ℝ)) ^ (2 : ℕ)
        ≤ 65536 * ((d.divisors.card : ℝ)) ^ (16 : ℕ) := hb2
      _ ≤ 65536 * ∑ d' ∈ Finset.Icc 1 K,
            (if d' ∣ m then ((((d'.divisors.card : ℕ) : ℝ)) ^ (16 : ℕ)) else 0) :=
          mul_le_mul_of_nonneg_left hsingle (by norm_num)

end Work.FIArea2.R6
