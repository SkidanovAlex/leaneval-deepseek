import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Data.Real.Basic

open scoped BigOperators
open Finset

namespace Commons.Algebra.BigOperators

private lemma prod_fin_add_one_eq_prod_Ico_one (a : ℕ → ℝ) (n : ℕ) :
    (∏ j : Fin n, a (j.val + 1)) = ∏ k ∈ Finset.Ico 1 (n + 1), a k := by
  rw [Fin.prod_univ_eq_prod_range (fun k => a (k + 1)) n]
  rw [Finset.range_eq_Ico]
  simpa using (Finset.prod_Ico_add' (f := a) (a := 0) (b := n) (c := 1))

theorem pow_le_prod_of_mono_succ {n i : ℕ} (a : ℕ → ℝ)
    (hi1 : 1 ≤ i) (hin : i ≤ n)
    (ha0 : ∀ j : ℕ, j ≤ n → 0 ≤ a j)
    (ham : ∀ j : ℕ, j ≤ n → i ≤ j → a i ≤ a j)
    (ha1 : ∀ j : ℕ, 1 ≤ j → j < i → 1 ≤ a j) :
    a i ^ (n + 1 - i) ≤ ∏ j : Fin n, a (j.val + 1) := by
  rw [prod_fin_add_one_eq_prod_Ico_one a n]
  have hin1 : i ≤ n + 1 := le_trans hin (Nat.le_succ n)
  calc
    a i ^ (n + 1 - i) = (∏ t ∈ Finset.range (n + 1 - i), a i) := by
      rw [Finset.prod_const, Finset.card_range]
    _ ≤ (∏ t ∈ Finset.range (n + 1 - i), a (t + i)) := by
      refine Finset.prod_le_prod ?h0 ?h1
      · intro t ht
        exact ha0 i hin
      · intro t ht
        have ht' : t < n + 1 - i := Finset.mem_range.mp ht
        refine ham (t + i) ?_ ?_
        · omega
        · omega
    _ = (∏ t ∈ Finset.Ico i (n + 1), a t) := by
      rw [Finset.range_eq_Ico]
      rw [Finset.prod_Ico_add' (f := a) (a := 0) (b := n + 1 - i) (c := i)]
      rw [Nat.sub_add_cancel hin1]
      rw [zero_add]
    _ ≤ (∏ k ∈ Finset.Ico 1 i, a k) * (∏ k ∈ Finset.Ico i (n + 1), a k) := by
      have hhead : (1 : ℝ) ≤ ∏ k ∈ Finset.Ico 1 i, a k := by
        apply Finset.one_le_prod
        intro k hk
        exact ha1 k (Finset.mem_Ico.mp hk).1 (Finset.mem_Ico.mp hk).2
      have htail : (0 : ℝ) ≤ ∏ k ∈ Finset.Ico i (n + 1), a k := by
        apply Finset.prod_nonneg
        intro k hk
        exact ha0 k (Nat.le_of_lt_succ (Finset.mem_Ico.mp hk).2)
      simpa using (mul_le_mul_of_nonneg_right hhead htail)
    _ = ∏ k ∈ Finset.Ico 1 (n + 1), a k := Finset.prod_Ico_consecutive a hi1 hin1

end Commons.Algebra.BigOperators