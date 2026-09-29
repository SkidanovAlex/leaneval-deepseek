import Mathlib
import Submission.Work.Holonomy3.pnt_deps

namespace Work.Holonomy3

/-- Chebyshev's asymptotic `ψ(N) ~ N` in the form needed by the lcm-cap estimate: for every `δ > 0` there is a constant `K` with `log [1,…,N] ≤ (1+δ)·N + K` for **all** `N`. Use `Commons.NumberTheory.Chebyshev.tendsto_log_lcmUpto_div_id` (`log lcmUpto N / N → 1`, i.e. `ψ(N) ~ N`) together with monotonicity of `lcmUpto N` in `N` (small `N` go into the constant). -/
theorem lcmUpto_log_le (δ : ℝ) (hδ : 0 < δ) :
    ∃ K : ℝ, ∀ N : ℕ,
      Real.log ((Submission.CDTPlan.lcmUpto N : ℕ) : ℝ) ≤ (1 + δ) * (N : ℝ) + K := by
  -- `log (lcmUpto N) / N → 1`, so eventually `log (lcmUpto N) / N < 1 + δ`, and for `N > 0`
  -- this gives `log (lcmUpto N) < (1 + δ) · N`.  The finitely many smaller `N` are absorbed
  -- into the constant `K`.
  have htend := Commons.NumberTheory.Chebyshev.tendsto_log_lcmUpto_div_id
  rw [Metric.tendsto_atTop] at htend
  obtain ⟨N₀, hN₀⟩ := htend δ hδ
  refine ⟨∑ i ∈ Finset.range (max N₀ 1),
      |Real.log ((Submission.CDTPlan.lcmUpto i : ℕ) : ℝ) - (1 + δ) * (i : ℝ)|, ?_⟩
  intro N
  rcases lt_or_ge N (max N₀ 1) with hN | hN
  · -- small `N`: the term is bounded by the whole sum, which is nonnegative
    have hmem : N ∈ Finset.range (max N₀ 1) := Finset.mem_range.mpr hN
    have hsum : |Real.log ((Submission.CDTPlan.lcmUpto N : ℕ) : ℝ) - (1 + δ) * (N : ℝ)|
        ≤ ∑ i ∈ Finset.range (max N₀ 1),
            |Real.log ((Submission.CDTPlan.lcmUpto i : ℕ) : ℝ) - (1 + δ) * (i : ℝ)| :=
      Finset.single_le_sum
        (f := fun i => |Real.log ((Submission.CDTPlan.lcmUpto i : ℕ) : ℝ) - (1 + δ) * (i : ℝ)|)
        (fun i _ => abs_nonneg _) hmem
    have hle :=
      le_abs_self (Real.log ((Submission.CDTPlan.lcmUpto N : ℕ) : ℝ) - (1 + δ) * (N : ℝ))
    linarith
  · -- large `N`: `log (lcmUpto N) < (1 + δ) · N`, so `K` is not even needed
    have hNpos : 1 ≤ N := le_trans (Nat.le_max_right N₀ 1) hN
    have h1 : |Real.log ((Submission.CDTPlan.lcmUpto N : ℕ) : ℝ) / (N : ℝ) - 1| < δ := by
      have hh := hN₀ N (le_trans (Nat.le_max_left N₀ 1) hN)
      rwa [Real.dist_eq] at hh
    have h2 : Real.log ((Submission.CDTPlan.lcmUpto N : ℕ) : ℝ) / (N : ℝ) < 1 + δ := by
      have := (abs_lt.mp h1).2
      linarith
    have hNn : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hNpos
    have h3 : Real.log ((Submission.CDTPlan.lcmUpto N : ℕ) : ℝ) < (1 + δ) * (N : ℝ) := by
      calc Real.log ((Submission.CDTPlan.lcmUpto N : ℕ) : ℝ)
          = (Real.log ((Submission.CDTPlan.lcmUpto N : ℕ) : ℝ) / (N : ℝ)) * (N : ℝ) :=
            (div_mul_cancel₀ _ (ne_of_gt hNn)).symm
        _ < (1 + δ) * (N : ℝ) := mul_lt_mul_of_pos_right h2 hNn
    have hK : 0 ≤ ∑ i ∈ Finset.range (max N₀ 1),
        |Real.log ((Submission.CDTPlan.lcmUpto i : ℕ) : ℝ) - (1 + δ) * (i : ℝ)| :=
      Finset.sum_nonneg (fun i _ => abs_nonneg _)
    linarith

end Work.Holonomy3
