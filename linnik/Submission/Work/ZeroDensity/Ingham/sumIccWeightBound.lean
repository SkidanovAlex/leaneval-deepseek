import Mathlib
import Submission.Work.ZeroDensity.Montgomery.normCpowAddIt_le_abel

set_option linter.unusedVariables false

namespace Work.ZeroDensity.Ingham

/-- The sum `∑_{n=1}^{N-1} (n^{-σ} - (n+1)^{-σ})` telescopes to `1 - N^{-σ}`,
hence is `≤ 1`. -/
theorem sumIccWeightBound (N : ℕ) (hN : 1 ≤ N) (σ : ℝ) (hσ : 0 ≤ σ) :
    ∑ n ∈ Finset.Icc 1 (N - 1), ((n : ℝ) ^ (-σ) - (((n + 1 : ℕ)) : ℝ) ^ (-σ)) ≤ 1 := by
  rcases eq_or_lt_of_le hN with h | h
  · subst h; simp
  · have h2 : 1 ≤ N - 1 := by omega
    have htel : ∑ n ∈ Finset.Icc 1 (N - 1), ((n : ℝ) ^ (-σ) - (((n + 1 : ℕ)) : ℝ) ^ (-σ))
        = 1 - (N : ℝ) ^ (-σ) := by
      set f : ℕ → ℝ := fun k => (k : ℝ) ^ (-σ) with hf
      have hsub := Finset.sum_Icc_sub (f := f) (m := 1) (n := N - 1) h2
      have hstep : ∑ n ∈ Finset.Icc 1 (N - 1), ((n : ℝ) ^ (-σ) - (((n + 1 : ℕ)) : ℝ) ^ (-σ))
          = - ∑ n ∈ Finset.Icc 1 (N - 1), (f (n+1) - f n) := by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro n hn
        simp only [hf]
        ring
      rw [hstep, hsub, Nat.sub_add_cancel hN]
      have hf1 : f 1 = (1 : ℝ) := by simp [hf]
      have hfN : f N = (N : ℝ) ^ (-σ) := by simp [hf]
      rw [hf1, hfN]
      ring
    rw [htel]
    have hp : 0 ≤ (N : ℝ) ^ (-σ) := Real.rpow_nonneg (Nat.cast_nonneg N) _
    linarith

end Work.ZeroDensity.Ingham
