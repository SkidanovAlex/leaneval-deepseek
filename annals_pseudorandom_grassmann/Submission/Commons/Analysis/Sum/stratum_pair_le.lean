import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Int.ConditionallyCompleteOrder
import Mathlib.Data.Int.Star

namespace Commons.Analysis.Sum

/-- Auxiliary arithmetic estimate: for `1 ≤ s ≤ d`, `k ≤ s` and `41 ≤ C`, the exponent
occurring in each summand of `stratum_pair_le` (after multiplying by `2 ^ (4*d*k)`) is at
most `C * d ^ 2 - 2 * d`. -/
lemma key_arith (C d s k : ℕ) (hC : 41 ≤ C) (hs1 : 1 ≤ s) (hsd : s ≤ d) (hks : k ≤ s) :
    2 * s * d + (26 * d * s + C * (d - s) ^ 2 + 7 * d * k) + 4 * d * k
      ≤ C * d ^ 2 - 2 * d := by
  have hmain : 28 * d * s + C * (d - s) ^ 2 + 11 * d * k + 2 * d ≤ C * d ^ 2 := by
    obtain ⟨m, hm⟩ : ∃ m, d = m + s := ⟨d - s, by omega⟩
    rw [hm]
    simp only [Nat.add_sub_cancel]
    have hk : 11 * (m + s) * k ≤ 11 * (m + s) * s := Nat.mul_le_mul_left _ hks
    have hCsq : 41 * (2 * m * s + s ^ 2) ≤ C * (2 * m * s + s ^ 2) :=
      Nat.mul_le_mul_right _ hC
    nlinarith [hk, hCsq, hs1, Nat.zero_le m]
  have he : 2 * s * d + (26 * d * s + C * (d - s) ^ 2 + 7 * d * k) + 4 * d * k + 2 * d
      = 28 * d * s + C * (d - s) ^ 2 + 11 * d * k + 2 * d := by ring
  rw [← he] at hmain
  exact Nat.le_sub_of_add_le hmain

theorem stratum_pair_le (C d k : ℕ) (hC : 41 ≤ C) :
    (∑ i : Fin (d + 1), ∑ j : Fin (d + 1),
      (if i.1 + j.1 + k ≤ d ∧ 1 ≤ i.1 + j.1 + k then
        (2 : ℝ) ^ (2 * (i.1 + j.1 + k) * d) *
          (2 : ℝ) ^ (26 * d * (i.1 + j.1 + k) + C * (d - (i.1 + j.1 + k)) ^ 2 + 7 * d * k)
      else 0))
      ≤ (2 : ℝ) ^ (C * d ^ 2) * ((2 : ℝ) ^ (4 * d * k))⁻¹ := by
  rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  have hterm : ∀ i j : Fin (d + 1),
      (if i.1 + j.1 + k ≤ d ∧ 1 ≤ i.1 + j.1 + k then
        (2 : ℝ) ^ (2 * (i.1 + j.1 + k) * d) *
          (2 : ℝ) ^ (26 * d * (i.1 + j.1 + k) + C * (d - (i.1 + j.1 + k)) ^ 2 + 7 * d * k)
      else 0) * (2 : ℝ) ^ (4 * d * k) ≤ (2 : ℝ) ^ (C * d ^ 2 - 2 * d) := by
    intro i j
    set s := i.1 + j.1 + k with hs
    split_ifs with h
    · obtain ⟨hsd, hs1⟩ := h
      have hks : k ≤ s := by rw [hs]; omega
      have hrew : (2 : ℝ) ^ (2 * s * d) *
            (2 : ℝ) ^ (26 * d * s + C * (d - s) ^ 2 + 7 * d * k) * (2 : ℝ) ^ (4 * d * k)
          = (2 : ℝ) ^ (2 * s * d + (26 * d * s + C * (d - s) ^ 2 + 7 * d * k) + 4 * d * k) := by
        rw [← pow_add, ← pow_add]
      rw [hrew]
      apply pow_le_pow_right₀ (by norm_num)
      exact key_arith C d s k hC hs1 hsd hks
    · rw [zero_mul]; positivity
  have hcount : (((d + 1 : ℕ) : ℝ)) * (((d + 1 : ℕ) : ℝ)) ≤ (2 : ℝ) ^ (2 * d) := by
    have hle : (((d + 1 : ℕ) : ℝ)) ≤ (2 : ℝ) ^ d := by
      have hd : d < 2 ^ d := Nat.lt_two_pow_self
      exact_mod_cast (Nat.succ_le_of_lt hd)
    calc (((d + 1 : ℕ) : ℝ)) * (((d + 1 : ℕ) : ℝ)) = (((d + 1 : ℕ) : ℝ)) ^ 2 := by ring
      _ ≤ ((2 : ℝ) ^ d) ^ 2 := pow_le_pow_left₀ (by positivity) hle 2
      _ = (2 : ℝ) ^ (2 * d) := by rw [← pow_mul]; congr 1; ring
  have h2 : 2 * d ≤ C * d ^ 2 := by
    rcases Nat.eq_zero_or_pos d with hd | hd
    · rw [hd]; simp
    · nlinarith [hC, hd]
  have hsum2 : 2 * d + (C * d ^ 2 - 2 * d) = C * d ^ 2 := by omega
  simp_rw [Finset.sum_mul]
  calc (∑ i : Fin (d + 1), ∑ j : Fin (d + 1),
          (if i.1 + j.1 + k ≤ d ∧ 1 ≤ i.1 + j.1 + k then
            (2 : ℝ) ^ (2 * (i.1 + j.1 + k) * d) *
              (2 : ℝ) ^ (26 * d * (i.1 + j.1 + k) + C * (d - (i.1 + j.1 + k)) ^ 2 + 7 * d * k)
          else 0) * (2 : ℝ) ^ (4 * d * k))
      ≤ ∑ i : Fin (d + 1), ∑ j : Fin (d + 1), (2 : ℝ) ^ (C * d ^ 2 - 2 * d) := by
        apply Finset.sum_le_sum; intro i _
        apply Finset.sum_le_sum; intro j _
        exact hterm i j
    _ = (((d + 1 : ℕ) : ℝ) * ((d + 1 : ℕ) : ℝ)) * (2 : ℝ) ^ (C * d ^ 2 - 2 * d) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring
    _ ≤ (2 : ℝ) ^ (2 * d) * (2 : ℝ) ^ (C * d ^ 2 - 2 * d) :=
        mul_le_mul_of_nonneg_right hcount (by positivity)
    _ = (2 : ℝ) ^ (2 * d + (C * d ^ 2 - 2 * d)) := by rw [← pow_add]
    _ = (2 : ℝ) ^ (C * d ^ 2) := by rw [hsum2]

end Commons.Analysis.Sum