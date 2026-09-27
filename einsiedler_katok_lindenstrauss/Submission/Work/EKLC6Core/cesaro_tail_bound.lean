import Mathlib

namespace Work.EKLC6Core

/-- Cesàro-style tail bound: split a sum over `range k` into the head `n < N`
(bounded by `C`) and the tail `N ≤ n` (bounded by `D`, with `D ≥ 0`). -/
theorem cesaro_tail_bound {c : ℕ → ℝ} {N k : ℕ} {C D : ℝ} (hNk : N ≤ k)
    (hhead : ∀ n, n < N → c n ≤ C) (htail : ∀ n, N ≤ n → c n ≤ D) (hD : 0 ≤ D) :
    ∑ n ∈ Finset.range k, c n ≤ C * N + D * k := by
  have h1 : ∑ n ∈ Finset.range N, c n ≤ C * N := by
    calc ∑ n ∈ Finset.range N, c n ≤ ∑ _ ∈ Finset.range N, C :=
          Finset.sum_le_sum (fun n hn => hhead n (Finset.mem_range.mp hn))
      _ = (Finset.range N).card • C := Finset.sum_const C
      _ = (N : ℝ) * C := by simp
      _ = C * N := by ring
  have h2 : ∑ n ∈ Finset.Ico N k, c n ≤ D * k := by
    calc ∑ n ∈ Finset.Ico N k, c n ≤ ∑ _ ∈ Finset.Ico N k, D :=
          Finset.sum_le_sum (fun n hn => htail n (Finset.mem_Ico.mp hn).1)
      _ = (Finset.Ico N k).card • D := Finset.sum_const D
      _ = ((k - N : ℕ) : ℝ) * D := by simp
      _ ≤ (k : ℝ) * D := by
          apply mul_le_mul_of_nonneg_right
          · exact_mod_cast Nat.sub_le k N
          · exact hD
      _ = D * k := by ring
  rw [← Finset.sum_range_add_sum_Ico c hNk]
  linarith [h1, h2]

end Work.EKLC6Core
