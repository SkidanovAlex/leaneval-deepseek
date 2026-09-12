import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Sub.Basic

namespace Commons.Nat.Icc

private lemma ite_ge_compl_lt (a b : ℕ) :
    (if a ≤ b then (1 : ℕ) else 0) = 1 - (if b < a then (1 : ℕ) else 0) := by
  by_cases h : a ≤ b
  · have hb : ¬ b < a := by omega
    simp [h, hb]
  · have hb : b < a := by omega
    simp [h, hb]

private lemma ite_lt_compl_ge (b a : ℕ) :
    (if b < a then (1 : ℕ) else 0) = 1 - (if a ≤ b then (1 : ℕ) else 0) := by
  by_cases h : b < a
  · have ha : ¬ a ≤ b := by omega
    simp [h, ha]
  · have ha : a ≤ b := by omega
    simp [h, ha]

theorem levelIndicator_flip {n j k : ℕ} (hn : 1 ≤ n) (hj1 : 1 ≤ j) (hj2 : j ≤ 2 * n - 1)
    (hk1 : 1 ≤ k) (hk2 : k ≤ 2 * n) :
    (if 2 * n + 1 - k ≤ n then
        (if j < 2 * n + 1 - k then (1 : ℕ) else 0)
      else (if 2 * n + 1 - (2 * n + 1 - k) ≤ j then (1 : ℕ) else 0)) =
      1 - (if k ≤ n then (if j < k then (1 : ℕ) else 0)
        else (if 2 * n + 1 - k ≤ j then (1 : ℕ) else 0)) := by
  have _ := hn
  have _ := hj1
  have _ := hj2
  by_cases hk : k ≤ n
  · have hnot : ¬ 2 * n + 1 - k ≤ n := by omega
    have hsub : 2 * n + 1 - (2 * n + 1 - k) = k := by omega
    rw [if_pos hk]
    rw [if_neg hnot]
    rw [hsub]
    exact ite_ge_compl_lt k j
  · have hle : 2 * n + 1 - k ≤ n := by omega
    rw [if_neg hk]
    rw [if_pos hle]
    exact ite_lt_compl_ge j (2 * n + 1 - k)

end Commons.Nat.Icc