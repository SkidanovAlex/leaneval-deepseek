import Mathlib

set_option linter.unusedVariables false
namespace Work.TMComp.RedProj

theorem bound_all_of_bound_large (f w : ℤ → ℝ) (η : ℝ) (hη : 0 < η)
    (hw : ∀ k : ℤ, 0 < w k) (N : ℤ)
    (h : ∀ k : ℤ, N ≤ |k| → f k ≤ w k * Real.exp (-(η * |(k : ℝ)|))) :
    ∃ C : ℝ, 0 < C ∧ ∀ k : ℤ, f k ≤ C * (w k * Real.exp (-(η * |(k : ℝ)|))) := by
  have habsN : (0:ℤ) ≤ |N| := abs_nonneg N
  -- The finitely many indices with `|k| < N` all lie in this finite interval.
  let U : Finset ℤ := Finset.Icc (-(|N| + 1)) (|N| + 1)
  have hU : U.Nonempty := by
    refine ⟨0, ?_⟩
    simp only [U, Finset.mem_Icc]
    constructor <;> omega
  -- Pointwise ratio `f k / (w k * exp (-(η|k|)))`.
  let G : ℤ → ℝ := fun k => f k / (w k * Real.exp (-(η * |(k : ℝ)|)))
  -- The absorbing constant: at least `1`, and dominating all finitely many ratios.
  let C : ℝ := max 1 (U.sup' hU G)
  refine ⟨C, ?_, ?_⟩
  · exact lt_of_lt_of_le zero_lt_one (le_max_left 1 _)
  · intro k
    have hden : 0 < w k * Real.exp (-(η * |(k : ℝ)|)) :=
      mul_pos (hw k) (Real.exp_pos _)
    by_cases hk : N ≤ |k|
    · -- Large index: the hypothesis already gives `f k ≤` the denominator, and `1 ≤ C`.
      have h1C : (1:ℝ) ≤ C := le_max_left 1 _
      exact le_trans (h k hk) (le_mul_of_one_le_left (le_of_lt hden) h1C)
    · -- Small index: `k` lies in `U`, so the ratio is bounded by `C`.
      have hkN : |k| < N := lt_of_not_ge hk
      have habs : |k| < |N| + 1 := by
        have h2 : N ≤ |N| := le_abs_self N
        omega
      have hmem : k ∈ U := by
        simp only [U, Finset.mem_Icc]
        obtain ⟨hl, hr⟩ := abs_lt.mp habs
        omega
      have hGk : G k ≤ C := by
        have := Finset.le_sup' G hmem
        exact le_trans this (le_max_right 1 _)
      calc f k = G k * (w k * Real.exp (-(η * |(k : ℝ)|))) := by
              simp only [G]
              rw [div_mul_cancel₀ _ (ne_of_gt hden)]
        _ ≤ C * (w k * Real.exp (-(η * |(k : ℝ)|))) :=
              mul_le_mul_of_nonneg_right hGk (le_of_lt hden)

end Work.TMComp.RedProj
