import Mathlib

namespace Work.LinnikAreas.Density4

/-- The partial sums of `∑ 1/(j+1)^2` are bounded by `2`.

For every `j`, `1/(j+1)^2 ≤ 2/(j+1) - 2/(j+2) = 2/((j+1)(j+2))` (indeed
`(j+1)(j+2) ≤ 2 (j+1)^2` for `j ≥ 0`).  Summing the telescoping right-hand side
over `j ∈ range n` gives `2 - 2/(n+1) ≤ 2`. -/
theorem sum_range_inv_succ_sq_le_two (n : ℕ) :
    ∑ j ∈ Finset.range n, (((j + 1 : ℕ) : ℝ) ^ 2)⁻¹ ≤ 2 := by
  have hterm : ∀ j ∈ Finset.range n,
      (((j + 1 : ℕ) : ℝ) ^ 2)⁻¹ ≤
        2 * (((j + 1 : ℕ) : ℝ))⁻¹ - 2 * (((j + 2 : ℕ) : ℝ))⁻¹ := by
    intro j _
    have ha : (1:ℝ) ≤ ((j + 1 : ℕ) : ℝ) := by
      have h : (1:ℕ) ≤ j + 1 := by omega
      exact_mod_cast h
    have key : (((j + 1 : ℕ) : ℝ) ^ 2)⁻¹ ≤
       2 * (((j + 1 : ℕ) : ℝ) * (((j + 1 : ℕ) : ℝ) + 1))⁻¹ := by
      have hb : (0:ℝ) < ((j+1:ℕ):ℝ) := by linarith
      have h1 : ((j+1:ℕ):ℝ) ≠ 0 := ne_of_gt hb
      have h2 : ((j+1:ℕ):ℝ) + 1 ≠ 0 := by positivity
      field_simp
      nlinarith [ha]
    have hrw : 2 * (((j+1:ℕ):ℝ))⁻¹ - 2 * (((j+2:ℕ):ℝ))⁻¹
        = 2 * (((j+1:ℕ):ℝ) * (((j+1:ℕ):ℝ)+1))⁻¹ := by
      have hcast : ((j+2:ℕ):ℝ) = ((j+1:ℕ):ℝ) + 1 := by push_cast; ring
      rw [hcast]
      have h1 : ((j+1:ℕ):ℝ) ≠ 0 := by positivity
      have h2 : ((j+1:ℕ):ℝ) + 1 ≠ 0 := by positivity
      field_simp
      ring
    rw [hrw]
    exact key
  calc ∑ j ∈ Finset.range n, (((j + 1 : ℕ) : ℝ) ^ 2)⁻¹
      ≤ ∑ j ∈ Finset.range n,
          (2 * (((j + 1 : ℕ) : ℝ))⁻¹ - 2 * (((j + 2 : ℕ) : ℝ))⁻¹) :=
        Finset.sum_le_sum hterm
    _ = 2 - 2 * (((n+1:ℕ):ℝ))⁻¹ := by
        rw [Finset.sum_range_sub' (fun j : ℕ => 2 * (((j+1:ℕ):ℝ))⁻¹) n]
        norm_num
    _ ≤ 2 := by
        have hn : (0:ℝ) ≤ (((n+1:ℕ):ℝ))⁻¹ := by positivity
        linarith

end Work.LinnikAreas.Density4
