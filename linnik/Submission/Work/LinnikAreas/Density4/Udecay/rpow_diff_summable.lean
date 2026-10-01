import Mathlib
import Submission.Work.LinnikAreas.Density4.Udecay.mellin_defs

namespace Work.LinnikAreas.Density4.Udecay

/-- The step weights `Δ m = m^{-s} - (m+1)^{-s}` are absolutely summable for `s > 0`.
`Δ 0 = 0^{-s} - 1 = -1` (Lean: `0^{-s} = 0` for `s ≠ 0`) and `Δ m ≥ 0` for `m ≥ 1` by monotonicity
of `x ↦ x^{-s}` on `(0,∞)`; telescoping gives `Σ_{m<N} |Δ m| = 1 + (1 - N^{-s}) = 2 - N^{-s} → 2`
for `N ≥ 1`, so `hasSum_iff_tendsto_nat_of_nonneg` applies. -/
theorem rpow_diff_summable {s : ℝ} (hs : 0 < s) :
    Summable (fun m : ℕ => |(m : ℝ) ^ (-s) - ((m : ℝ) + 1) ^ (-s)|) := by
  set f : ℕ → ℝ := fun m => |(m : ℝ) ^ (-s) - ((m : ℝ) + 1) ^ (-s)| with hf
  -- The partial sums `Σ_{m<N} f m` are bounded by `2`; the terms are nonnegative.
  refine summable_of_sum_range_le (c := 2) (fun m => abs_nonneg _) ?_
  intro n
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hn)
    set g : ℕ → ℝ := fun i => (i : ℝ) ^ (-s) with hg
    -- `f 0 = |0^{-s} - 1| = 1` because `0^{-s} = 0` for `s ≠ 0`.
    have hf0 : f 0 = 1 := by
      have hne : (-s : ℝ) ≠ 0 := by linarith
      simp only [hf, Nat.cast_zero, Real.zero_rpow hne]
      norm_num
    -- For `k ≥ 0` the difference is nonnegative (`x ↦ x^{-s}` is antitone on `(0,∞)`),
    -- so the absolute value can be dropped.
    have hterm : ∀ k : ℕ, f (k+1) = g (k+1) - g (k+2) := by
      intro k
      simp only [hf, hg]
      have hcast : ((k+1 : ℕ) : ℝ) + 1 = ((k+2 : ℕ) : ℝ) := by push_cast; ring
      rw [hcast, abs_of_nonneg]
      apply sub_nonneg.mpr
      apply Real.rpow_le_rpow_of_nonpos (by positivity) (by push_cast; linarith) (by linarith)
    -- Telescoping: `Σ_{k<m} (g(k+1) - g(k+2)) = g 1 - g(m+1) = 1 - (m+1)^{-s}`.
    have hsum : (∑ k ∈ Finset.range m, f (k+1)) = 1 - g (m+1) := by
      rw [Finset.sum_congr rfl (fun k _ => hterm k)]
      rw [show (∑ k ∈ Finset.range m, (g (k+1) - g (k+2))) = g 1 - g (m+1) from
        by simpa using Finset.sum_range_sub' (fun j : ℕ => g (j+1)) m]
      have hg1 : g 1 = 1 := by simp only [hg, Nat.cast_one, Real.one_rpow]
      rw [hg1]
    rw [Finset.sum_range_succ', hsum, hf0]
    have : 0 ≤ g (m+1) := by simp only [hg]; positivity
    linarith

end Work.LinnikAreas.Density4.Udecay
