import Mathlib

namespace Commons.Analysis.HardyLittlewood

open Finset

theorem sunrise_card_le_sum {a : ℕ → ℝ} {lam : ℝ} {φ : ℕ → ℝ} {E : Finset ℕ}
    (hφ : ∀ n, 0 ≤ φ n) (hE : ∀ n, n ∈ E ↔ 0 < φ n)
    (hrec : ∀ n ∈ E, φ n = a n - lam + φ (n + 1)) :
    lam * (E.card : ℝ) ≤ ∑ n ∈ E, a n := by
  -- φ vanishes outside E
  have hzero : ∀ n, n ∉ E → φ n = 0 := by
    intro n hn
    have hle : φ n ≤ 0 := not_lt.mp (fun h => hn ((hE n).mpr h))
    linarith [hφ n]
  -- rewrite a on E
  have ha : ∀ n ∈ E, a n = φ n + lam - φ (n + 1) := by
    intro n hn
    have := hrec n hn
    linarith
  -- key inequality: the shifted sum is bounded by the sum over E
  have hkey : ∑ n ∈ E, φ (n + 1) ≤ ∑ n ∈ E, φ n := by
    have hinj : Set.InjOn (fun n : ℕ => n + 1) (↑E : Set ℕ) :=
      fun x _ y _ h => Nat.succ.inj h
    have h1 : ∑ m ∈ E.image (fun n : ℕ => n + 1), φ m = ∑ n ∈ E, φ (n + 1) :=
      Finset.sum_image hinj
    have h2 : ∑ m ∈ (E.image (fun n : ℕ => n + 1)) ∩ E, φ m
        = ∑ m ∈ E.image (fun n : ℕ => n + 1), φ m := by
      apply Finset.sum_subset Finset.inter_subset_left
      intro x hx hxn
      apply hzero x
      intro hxE
      exact hxn (Finset.mem_inter.mpr ⟨hx, hxE⟩)
    have h3 : ∑ m ∈ (E.image (fun n : ℕ => n + 1)) ∩ E, φ m ≤ ∑ m ∈ E, φ m :=
      Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
        (fun i _ _ => hφ i)
    linarith
  -- compute the sum of a over E
  have hsum : ∑ n ∈ E, a n
      = ∑ n ∈ E, φ n + (E.card : ℝ) * lam - ∑ n ∈ E, φ (n + 1) := by
    have h1 : ∑ n ∈ E, a n = ∑ n ∈ E, (φ n + lam - φ (n + 1)) :=
      Finset.sum_congr rfl (fun n hn => ha n hn)
    rw [h1, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const,
      nsmul_eq_mul]
  linarith

end Commons.Analysis.HardyLittlewood
