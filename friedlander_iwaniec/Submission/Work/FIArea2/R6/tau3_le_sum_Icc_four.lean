/-
# `FIArea2/R6/tau3_le_sum_Icc_four` — the `τ₃` analogue of `tau_sq_le_sum_Icc_four`

For `m ≤ K⁴`,

  `τ₃(m) ≤ 65536 · Σ_{1 ≤ d ≤ K, d ∣ m} τ(d)¹⁶`.

Since `τ₃(n) = Σ_{e ∣ n} τ(n/e) ≤ τ(n)²` for `n ≥ 1`, this is immediate from
`tau_sq_le_sum_Icc_four`; `m = 0` is the trivial case `τ₃(0) = 1 ≤ 65536·τ(1)¹⁶`.
-/
import Mathlib
import Submission.Work.FIArea2.R6.SixDefs
import Submission.Work.FIArea2.R6.tau_sq_le_sum_Icc_four

open Finset
open scoped BigOperators

set_option maxHeartbeats 1000000

namespace Work.FIArea2.R6

/-- `τ₃(n) ≤ τ(n)²` for `n ≥ 1`. -/
theorem tau3_le_sq {n : ℕ} (hn : n ≠ 0) : tau3 n ≤ (n.divisors.card) ^ (2 : ℕ) := by
  rw [tau3, if_neg hn]
  have hterm : ∀ d ∈ n.divisors, (n / d).divisors.card ≤ n.divisors.card := by
    intro d hd
    refine Finset.card_le_card (Nat.divisors_subset_of_dvd hn ?_)
    exact Nat.div_dvd_of_dvd (Nat.mem_divisors.mp hd).1
  calc ∑ d ∈ n.divisors, (n / d).divisors.card
      ≤ ∑ _d ∈ n.divisors, n.divisors.card := Finset.sum_le_sum hterm
    _ = n.divisors.card * n.divisors.card := by rw [Finset.sum_const, smul_eq_mul]
    _ = (n.divisors.card) ^ (2 : ℕ) := by ring

/-- **FI Lemma 2.2 with `k = 4` for `τ₃`.** -/
theorem tau3_le_sum_Icc_four (m K : ℕ) (hK : 1 ≤ K) (h : (m : ℝ) ≤ (K : ℝ) ^ (4 : ℕ)) :
    ((tau3 m : ℕ) : ℝ)
      ≤ 65536 * ∑ d ∈ Finset.Icc 1 K,
          (if d ∣ m then ((((d.divisors.card : ℕ) : ℝ)) ^ (16 : ℕ)) else 0) := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    have h1 : tau3 0 = 1 := by rw [tau3, if_pos rfl]
    rw [h1]
    have hmem : (1 : ℕ) ∈ Finset.Icc 1 K := Finset.mem_Icc.mpr ⟨le_refl 1, hK⟩
    have h0 : ∀ i ∈ Finset.Icc 1 K, (0 : ℝ) ≤
        (if i ∣ (0 : ℕ) then ((((i.divisors.card : ℕ) : ℝ)) ^ (16 : ℕ)) else 0) := by
      intro i _
      by_cases hh : i ∣ (0 : ℕ)
      · simp only [hh, if_true]; positivity
      · simp only [hh, if_false]; norm_num
    have hle := Finset.single_le_sum (s := Finset.Icc 1 K)
      (f := fun d => (if d ∣ (0 : ℕ) then ((((d.divisors.card : ℕ) : ℝ)) ^ (16 : ℕ)) else 0))
      h0 hmem
    have hS : (1 : ℝ) ≤ ∑ d ∈ Finset.Icc 1 K,
        (if d ∣ (0 : ℕ) then ((((d.divisors.card : ℕ) : ℝ)) ^ (16 : ℕ)) else 0) := by
      simpa using hle
    calc ((1 : ℕ) : ℝ) = 1 := by norm_num
      _ ≤ 1 * 65536 := by norm_num
      _ ≤ (∑ d ∈ Finset.Icc 1 K,
            (if d ∣ (0 : ℕ) then ((((d.divisors.card : ℕ) : ℝ)) ^ (16 : ℕ)) else 0)) * 65536 :=
          mul_le_mul_of_nonneg_right hS (by norm_num)
      _ = 65536 * ∑ d ∈ Finset.Icc 1 K,
            (if d ∣ (0 : ℕ) then ((((d.divisors.card : ℕ) : ℝ)) ^ (16 : ℕ)) else 0) := by ring
  · have hsq := tau3_le_sq (Nat.pos_iff_ne_zero.mp hm)
    have hR := tau_sq_le_sum_Icc_four m K hK h
    have hcast : ((tau3 m : ℕ) : ℝ) ≤ ((m.divisors.card : ℝ)) ^ (2 : ℕ) := by
      calc ((tau3 m : ℕ) : ℝ) ≤ (((m.divisors.card) ^ (2 : ℕ) : ℕ) : ℝ) := by
            exact_mod_cast hsq
        _ = ((m.divisors.card : ℝ)) ^ (2 : ℕ) := by push_cast; ring
    linarith [hcast, hR]

end Work.FIArea2.R6
