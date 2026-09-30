import Mathlib
import Submission.Work.BW.ulcm_le_three_pow
import Submission.Work.BW.syl_floor_sum_lb
import Submission.Work.BW.syl_div_sum_lt
import Submission.Work.BW.floor_div_log_bound

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

open Finset

lemma log_factorial_ge' (m : ℕ) :
    (m : ℝ) * Real.log (m : ℝ) - (m : ℝ) ≤ Real.log (m.factorial : ℝ) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [Real.log_zero]
  · have h := log_factorial_ge m hm
    linarith

lemma log_factorial_div_sylBlocks (n : ℕ) :
    Real.log ((Nat.factorial n : ℝ) / (sylBlocks n : ℝ))
      = Real.log (Nat.factorial n : ℝ)
        - ∑ i ∈ Finset.range (n + 1), Real.log ((n / syl i).factorial : ℝ) := by
  have hfac : (Nat.factorial n : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hbl : (sylBlocks n : ℝ) ≠ 0 := by exact_mod_cast sylBlocks_ne_zero n
  have hcast : (sylBlocks n : ℝ)
      = ∏ i ∈ Finset.range (n + 1), (((n / syl i).factorial : ℕ) : ℝ) := by
    rw [sylBlocks, Nat.cast_prod]
  rw [Real.log_div hfac hbl, hcast,
    Real.log_prod (fun i _ => by exact_mod_cast Nat.factorial_ne_zero (n / syl i))]

lemma range_div_mul_log_le (n : ℕ) :
    (∑ i ∈ Finset.range (n + 1), ((n / syl i : ℕ) : ℝ) * Real.log (syl i : ℝ))
      ≤ (n : ℝ) * Lw n := by
  rw [Lw]
  have hsub : (Finset.range (n + 1)).filter (fun i => syl i ≤ n) ⊆ Finset.range (n + 1) :=
    Finset.filter_subset _ _
  have hzero : ∀ x ∈ Finset.range (n + 1),
      x ∉ (Finset.range (n + 1)).filter (fun i => syl i ≤ n) →
      ((n / syl x : ℕ) : ℝ) * Real.log (syl x : ℝ) = 0 := by
    intro x hx hxn
    have hlt : n < syl x := by
      by_contra hcon
      exact hxn (Finset.mem_filter.mpr ⟨hx, not_lt.mp hcon⟩)
    rw [Nat.div_eq_of_lt hlt]
    norm_num
  rw [← Finset.sum_subset hsub hzero]
  calc ∑ i ∈ (Finset.range (n + 1)).filter (fun i => syl i ≤ n),
          ((n / syl i : ℕ) : ℝ) * Real.log (syl i : ℝ)
      ≤ ∑ i ∈ (Finset.range (n + 1)).filter (fun i => syl i ≤ n),
          (n : ℝ) * (Real.log (syl i : ℝ) / (syl i : ℝ)) := by
        refine Finset.sum_le_sum (fun i hi => ?_)
        have hlog : 0 ≤ Real.log (syl i : ℝ) :=
          Real.log_nonneg (by exact_mod_cast (by have := syl_two_le i; omega : 1 ≤ syl i))
        calc ((n / syl i : ℕ) : ℝ) * Real.log (syl i : ℝ)
            ≤ ((n : ℝ) / (syl i : ℝ)) * Real.log (syl i : ℝ) :=
              mul_le_mul_of_nonneg_right Nat.cast_div_le hlog
          _ = (n : ℝ) * (Real.log (syl i : ℝ) / (syl i : ℝ)) := by ring
    _ = (n : ℝ) * ∑ i ∈ (Finset.range (n + 1)).filter (fun i => syl i ≤ n),
          Real.log (syl i : ℝ) / (syl i : ℝ) := by rw [Finset.mul_sum]

/-! ### the theorem -/

/-- **Hanson's entropy bound** for the multinomial-type integer of Hanson (1972).

With `syl` Sylvester's sequence (`syl 0 = 2`, `syl (i+1) = syl i * (syl i - 1) + 1`),
`sylBlocks n = ∏_{i ≤ n} (n / syl i)!` and `Lw n = ∑_{syl i ≤ n} log (syl i) / syl i`
(all three defined in `Submission.Work.BW.ulcm_le_three_pow`), for `n ≥ 1`:
`log (n ! / sylBlocks n) ≤ log n + log (n+1) + 1 + n * Lw n + K * log n`,
where `K = #{i ≤ n : syl i ≤ n}` is the number of Sylvester terms not exceeding `n`.

Numerically verified (`math.lgamma`) with large slack for `n ≤ 10^7` and at the regime switches;
the statement is a standard Hanson estimate and is true.

Route. Write `m_i = n / syl i` (so `m_i = 0` for `syl i > n`) and `r = n - ∑_i m_i`.
Use the sorry-free helpers in `Submission.Work.BW.ulcm_le_three_pow`:
`log_factorial_le'` (`log n! ≤ n log n - n + log (n+1) + 1` for `n ≥ 1`),
`log_factorial_ge` (`m log m - m + 1 ≤ log m!` for `m ≥ 1`),
`Real.log_le_sub_one_of_pos` (concavity `log u - log v ≤ (u-v)/v` for `0 < v ≤ u`, applied to
`u = (n:ℝ)/syl i ≥ v = m_i`: `m_i log m_i ≥ m_i (log n - log (syl i)) - (n/syl i - m_i)`; for
`m_i = 0` this holds trivially since `m_i log m_i = 0 ≥ -(n/syl i)`),
`syl_sum_inv`, `syl_prod`, `syl_mono`, `syl_lt_of_lt`, `syl_ge` for `r ≤ K + 1`:
`{i : syl i ≤ n} = {0,…,K-1}` is an initial segment, `∑_{i<K} 1/syl i = 1 - 1/(syl K - 1)` and
`syl K - 1 ≥ n` (as `syl K > n`), so `∑_{syl i ≤ n} n/syl i ≥ n - 1`, and each floor loses `< 1`,
hence `r ≤ K + 1`.  Also `∑_{i ∈ range (n+1)} (n:ℝ)/syl i < n` because the partial reciprocal sum
`∑_{i ≤ n} 1/syl i = 1 - 1/(syl (n+1) - 1) < 1`.
Chain: `log (n!/sylBlocks n) = log n! - ∑_{i ≤ n} log m_i!` (log of a `Finset.prod` of positive
naturals) `≤ (n log n - n) + log (n+1) + 1 - ∑ (m_i log m_i - m_i) - K + K`
`≤ r log n + ∑ m_i log (syl i) + (∑_i n/syl i - n) - K + log (n+1) + 1`
`≤ (K+1) log n + n * Lw n + log (n+1) + 1` (`∑_i n/syl i - n < 0`, `-K ≤ 0`, and
`∑ m_i log (syl i) ≤ ∑_{syl i ≤ n} (n/syl i) log (syl i) = n * Lw n`).
NOTE: do not use the theorem `Work.BW.ulcm_le_three_pow` itself or `Work.BW.log_ulcm_le` /
`Work.BW.syl_entropy_bound` (proofs still contain `sorry`, so using them would taint the result
with `sorryAx`); every helper listed above is verified sorry-free. -/
theorem est14_hanson_entropy (n : ℕ) (hn : 1 ≤ n) :
    Real.log ((Nat.factorial n : ℝ) / (sylBlocks n : ℝ)) ≤
      Real.log n + Real.log (n + 1) + 1 + n * Lw n
        + (((Finset.range (n + 1)).filter (fun i => syl i ≤ n)).card : ℝ) * Real.log n := by
  have hlogn : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn)
  set A1 : ℝ := ∑ i ∈ Finset.range (n + 1), ((n / syl i : ℕ) : ℝ) with hA1
  set A2 : ℝ := ∑ i ∈ Finset.range (n + 1), ((n / syl i : ℕ) : ℝ) * Real.log (syl i : ℝ) with hA2
  set A3 : ℝ := ∑ i ∈ Finset.range (n + 1), (n : ℝ) / (syl i : ℝ) with hA3
  set K : ℕ := ((Finset.range (n + 1)).filter (fun i => syl i ≤ n)).card with hK
  have hL := log_factorial_div_sylBlocks n
  have hfac : Real.log (Nat.factorial n : ℝ)
      ≤ (n : ℝ) * Real.log n - n + Real.log (n + 1) + 1 := log_factorial_le' n hn
  have hblk : (∑ i ∈ Finset.range (n + 1),
        (((n / syl i : ℕ) : ℝ) * Real.log ((n / syl i : ℕ) : ℝ) - ((n / syl i : ℕ) : ℝ)))
      ≤ ∑ i ∈ Finset.range (n + 1), Real.log ((n / syl i).factorial : ℝ) :=
    Finset.sum_le_sum (fun i _ => log_factorial_ge' (n / syl i))
  have hcon : (∑ i ∈ Finset.range (n + 1),
        (((n / syl i : ℕ) : ℝ) * Real.log n - ((n / syl i : ℕ) : ℝ) * Real.log (syl i : ℝ)
          - (n : ℝ) / (syl i : ℝ)))
      ≤ ∑ i ∈ Finset.range (n + 1),
        (((n / syl i : ℕ) : ℝ) * Real.log ((n / syl i : ℕ) : ℝ) - ((n / syl i : ℕ) : ℝ)) :=
    Finset.sum_le_sum (fun i _ => floor_div_log_bound n i hn)
  have hsplit : (∑ i ∈ Finset.range (n + 1),
        (((n / syl i : ℕ) : ℝ) * Real.log n - ((n / syl i : ℕ) : ℝ) * Real.log (syl i : ℝ)
          - (n : ℝ) / (syl i : ℝ)))
      = A1 * Real.log n - A2 - A3 := by
    rw [hA1, hA2, hA3, Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_mul]
  have hmain : Real.log ((Nat.factorial n : ℝ) / (sylBlocks n : ℝ))
      ≤ (n : ℝ) * Real.log n - n + Real.log (n + 1) + 1 - (A1 * Real.log n - A2 - A3) := by
    rw [hL]
    linarith [hfac, le_trans hcon hblk, hsplit]
  have hR : (n : ℝ) - A1 ≤ (K : ℝ) + 1 := by
    have h := syl_floor_sum_lb n hn
    have h' : (n : ℝ) ≤ A1 + (K : ℝ) + 1 := by
      rw [hA1, hK]
      exact h
    linarith
  have hprod : (n : ℝ) * Real.log n - A1 * Real.log n ≤ ((K : ℝ) + 1) * Real.log n := by
    have h1 : ((n : ℝ) - A1) * Real.log n ≤ ((K : ℝ) + 1) * Real.log n :=
      mul_le_mul_of_nonneg_right hR hlogn
    have h2 : ((n : ℝ) - A1) * Real.log n = (n : ℝ) * Real.log n - A1 * Real.log n := by ring
    rwa [h2] at h1
  have hA2le : A2 ≤ (n : ℝ) * Lw n := by
    rw [hA2]; exact range_div_mul_log_le n
  have hA3lt : A3 < (n : ℝ) := by
    rw [hA3]; exact syl_div_sum_lt n hn
  have hgoal : Real.log ((Nat.factorial n : ℝ) / (sylBlocks n : ℝ))
      ≤ Real.log n + Real.log (n + 1) + 1 + n * Lw n + (K : ℝ) * Real.log n := by
    linarith [hmain, hprod, hA2le, hA3lt]
  exact hgoal

end Work.BW
