import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.Star

namespace Commons.Analysis.Real

/-- For a monotone sequence `a`, the sum of the first `k` terms is at most `k` times
the `k`-th term: `∑_{i<k} a i ≤ k * a k`. -/
lemma prefix_sum_le_card_mul {a : ℕ → ℝ} (hmono : Monotone a) (k : ℕ) :
    (Finset.range k).sum a ≤ (k : ℝ) * a k := by
  calc (Finset.range k).sum a
      ≤ (Finset.range k).sum (fun _ => a k) := by
        refine Finset.sum_le_sum (fun i hi => ?_)
        exact hmono (Nat.le_of_lt (Finset.mem_range.mp hi))
    _ = (k : ℝ) * a k := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- The averages of the prefixes of length `k+1` and `k+2` are ordered, for a monotone
sequence. -/
lemma div_prefix_mono_step {a : ℕ → ℝ} (hmono : Monotone a) (k : ℕ) :
    (Finset.range (k+1)).sum a / ((k+1 : ℕ) : ℝ) ≤
      (Finset.range (k+2)).sum a / ((k+2 : ℕ) : ℝ) := by
  have hk : (Finset.range (k+1)).sum a ≤ ((k+1 : ℕ) : ℝ) * a (k+1) :=
    prefix_sum_le_card_mul hmono (k+1)
  have h2 : (Finset.range (k+2)).sum a = (Finset.range (k+1)).sum a + a (k+1) := by
    rw [Finset.sum_range_succ]
  rw [h2, div_le_div_iff₀ (by positivity) (by positivity)]
  push_cast at hk ⊢
  nlinarith [hk]

/-- For a monotone sequence, the sequence of averages of its nonempty prefixes is
monotone. -/
lemma prefix_avg_monotone {a : ℕ → ℝ} (hmono : Monotone a) :
    Monotone (fun k : ℕ => (Finset.range (k+1)).sum a / ((k+1 : ℕ) : ℝ)) :=
  monotone_nat_of_le_succ (fun k => div_prefix_mono_step hmono k)

/-- The average of the first `m` terms of a monotone sequence is at most the average of
the first `n` terms, when `m ≤ n`. -/
theorem sum_prefix_le_mul {a : ℕ → ℝ} (hmono : Monotone a) {m n : ℕ} (hmn : m ≤ n) :
    (Finset.range m).sum a ≤ ((m : ℝ) / (n : ℝ)) * (Finset.range n).sum a := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm; simp
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  have hle : m' ≤ n' := by omega
  have key := prefix_avg_monotone hmono hle
  have hmpos : (0:ℝ) < ((m'+1 : ℕ) : ℝ) := by positivity
  have h2 : (Finset.range (m'+1)).sum a
      ≤ ((m'+1 : ℕ) : ℝ) * ((Finset.range (n'+1)).sum a / ((n'+1 : ℕ) : ℝ)) := by
    rw [← mul_div_cancel₀ ((Finset.range (m'+1)).sum a) (ne_of_gt hmpos)]
    exact mul_le_mul_of_nonneg_left key (le_of_lt hmpos)
  have h3 : ((m'+1 : ℕ) : ℝ) * ((Finset.range (n'+1)).sum a / ((n'+1 : ℕ) : ℝ))
      = (((m'+1 : ℕ) : ℝ) / ((n'+1 : ℕ) : ℝ)) * (Finset.range (n'+1)).sum a := by
    ring
  rw [h3] at h2
  exact h2

end Commons.Analysis.Real