import Mathlib

namespace Work.LinnikAreas.Density4

/-- For `M ≥ 15000` and `N = ⌊exp (M-2)⌋`, the integer `N` satisfies `2 ≤ N` and
`M - 2 < log (N + 1) ≤ M - 1`. -/
theorem dls_exp_floor_bounds (M : ℝ) (hM : 15000 ≤ M) (N : ℕ)
    (hN : N = ⌊Real.exp (M - 2)⌋₊) :
    2 ≤ N ∧ M - 2 < Real.log ((N : ℝ) + 1) ∧ Real.log ((N : ℝ) + 1) ≤ M - 1 := by
  have hpos : 0 < Real.exp (M - 2) := Real.exp_pos _
  -- `2 ≤ N`: since `2 ≤ M - 1 ≤ ⌊exp (M-2)⌋₊`.
  have h1 : 2 ≤ N := by
    rw [hN]
    apply Nat.le_floor
    show (2 : ℝ) ≤ Real.exp (M - 2)
    have he : M - 2 + 1 ≤ Real.exp (M - 2) := Real.add_one_le_exp _
    linarith
  -- `M - 2 < log (N + 1)`: since `exp (M-2) < N + 1` and `log ∘ exp = id`.
  have h2 : M - 2 < Real.log ((N : ℝ) + 1) := by
    rw [hN]
    have hlt : Real.exp (M - 2) < (⌊Real.exp (M - 2)⌋₊ : ℝ) + 1 :=
      Nat.lt_floor_add_one _
    have := Real.log_lt_log hpos hlt
    rw [Real.log_exp] at this
    exact this
  -- `log (N + 1) ≤ M - 1`: since `N + 1 ≤ exp (M-2) + 1 ≤ exp (M-1)`.
  have h3 : Real.log ((N : ℝ) + 1) ≤ M - 1 := by
    rw [← Real.log_exp (M - 1)]
    apply Real.log_le_log (by positivity)
    have hle : (N : ℝ) ≤ Real.exp (M - 2) := by
      rw [hN]; exact Nat.floor_le hpos.le
    have h1e : (1 : ℝ) ≤ Real.exp (M - 2) := Real.one_le_exp (by linarith)
    have h2e : (2 : ℝ) ≤ Real.exp 1 := le_of_lt Real.exp_one_gt_two
    have key : Real.exp (M - 1) = Real.exp (M - 2) * Real.exp 1 := by
      rw [← Real.exp_add]; congr 1; ring
    rw [key]
    nlinarith [hle, h1e, h2e, Real.exp_pos (M - 2)]
  exact ⟨h1, h2, h3⟩

end Work.LinnikAreas.Density4
