import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.Archimedean.Real.Basic

namespace Commons.Analysis.Asymptotics

/-- If the tail sums of a sequence of nonnegative terms, each at most `1 / 2`,
eventually reach `1`, then from every starting index `N` there is a stopping
index `Y > N` for which the sum over `Icc N Y` lies in `[1, 3 / 2]`.

Proof: take the least `Y ≥ N` whose sum reaches `1`. Then `Y > N` (otherwise
`a N ≥ 1`), and the sum just before `Y` is `< 1`, so adding the last term
(≤ `1 / 2`) keeps the sum `< 3 / 2`. -/
theorem exists_Icc_sum_between_of_tail_lower (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n)
    (hb : ∀ n, a n ≤ 1 / 2)
    (htail : ∀ N : ℕ, ∃ Y ≥ N, 1 ≤ ∑ n ∈ Finset.Icc N Y, a n) :
    ∀ N : ℕ, ∃ Y, N < Y ∧ 1 ≤ ∑ n ∈ Finset.Icc N Y, a n ∧
      ∑ n ∈ Finset.Icc N Y, a n ≤ 3 / 2 := by
  classical
  intro N
  let S : ℕ → ℝ := fun Y => ∑ n ∈ Finset.Icc N Y, a n
  let Q : ℕ → Prop := fun Y => N ≤ Y ∧ 1 ≤ S Y
  have hnonempty : ∃ Y, Q Y := by
    rcases htail N with ⟨Y, hY, hS⟩
    exact ⟨Y, hY, hS⟩
  let Y := Nat.find hnonempty
  have hQY : Q Y := by
    dsimp [Y]
    exact Nat.find_spec hnonempty
  have hQmin : ∀ m < Y, ¬ Q m := by
    intro m hm
    exact Nat.find_min hnonempty hm
  have hYgtN : N < Y := by
    by_contra hnot
    have hYleN : Y ≤ N := Nat.le_of_not_gt hnot
    have hYeq : Y = N := le_antisymm hYleN hQY.1
    have hSN : S N = a N := by
      dsimp [S]
      simp
    have h1 : (1 : ℝ) ≤ a N := by
      simpa [hYeq, hSN] using hQY.2
    linarith [hb N]
  have hZlt : Y - 1 < Y := by omega
  have hNZ : N ≤ Y - 1 := by omega
  have hnQZ : ¬ Q (Y - 1) := hQmin (Y - 1) hZlt
  have hSZlt1 : S (Y - 1) < 1 := by
    have hnot1 : ¬ (1 : ℝ) ≤ S (Y - 1) := by
      intro h1
      exact hnQZ ⟨hNZ, h1⟩
    exact lt_of_not_ge hnot1
  have hrel : S Y = S (Y - 1) + a Y := by
    have hsub : Y - 1 + 1 = Y := Nat.sub_add_cancel (by omega : 1 ≤ Y)
    have hle : N ≤ Y - 1 + 1 := by omega
    have hm := Finset.sum_Icc_succ_top (a := N) (b := Y - 1) hle a
    simpa [S, hsub] using hm
  have hSY : S Y < (3 : ℝ) / 2 := by
    calc
      S Y = S (Y - 1) + a Y := hrel
      _ < 1 + a Y := add_lt_add_left hSZlt1 (a Y)
      _ ≤ 1 + (1 : ℝ) / 2 := add_le_add_right (hb Y) 1
      _ = (3 : ℝ) / 2 := by norm_num
  refine ⟨Y, hYgtN, ?_, ?_⟩
  · simpa [S] using hQY.2
  · simpa [S] using (le_of_lt hSY)

end Commons.Analysis.Asymptotics