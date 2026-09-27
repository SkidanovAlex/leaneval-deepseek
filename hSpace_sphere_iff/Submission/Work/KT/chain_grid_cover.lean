import Mathlib

namespace Work.KT

/-- The grid points `y_j = 1 - 2j/m` (for `m > 0`) cover `[-1,1]`: every `y ∈ [-1,1]` lies in one
of the intervals `[y_{j+1}, y_j]`, `j < m`. -/
theorem chain_grid_cover (m : ℕ) (hm : 0 < m) (y : ℝ) (hy1 : -1 ≤ y) (hy2 : y ≤ 1) :
    ∃ j : ℕ, j < m ∧ 1 - 2 * ((j : ℝ) + 1) / m ≤ y ∧ y ≤ 1 - 2 * (j : ℝ) / m := by
  classical
  -- The index `m-1` always satisfies the left inequality, since `y_m = -1 ≤ y`.
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hcast : ((m - 1 : ℕ) : ℝ) + 1 = (m : ℝ) := by
    have hnat : m - 1 + 1 = m := Nat.sub_add_cancel (by omega : 1 ≤ m)
    have := congrArg (fun n : ℕ => (n : ℝ)) hnat
    push_cast at this
    exact this
  have h0 : 1 - 2 * (((m - 1 : ℕ) : ℝ) + 1) / (m : ℝ) ≤ y := by
    rw [hcast]
    have h2 : 2 * (m : ℝ) / (m : ℝ) = 2 := by
      rw [mul_div_assoc, div_self (ne_of_gt hmR), mul_one]
    linarith
  have hex : ∃ k : ℕ, 1 - 2 * ((k : ℝ) + 1) / (m : ℝ) ≤ y := ⟨m - 1, h0⟩
  -- Take the least such index.
  have hjm : Nat.find hex < m := by
    have h := Nat.find_min' hex h0
    omega
  refine ⟨Nat.find hex, hjm, Nat.find_spec hex, ?_⟩
  by_cases hj0 : Nat.find hex = 0
  · rw [hj0]
    push_cast
    simp only [mul_zero, zero_div, sub_zero]
    linarith
  · -- Minimality gives the right inequality.
    have hnot := Nat.find_min hex (Nat.sub_one_lt hj0)
    have hj1 : 1 ≤ Nat.find hex := by omega
    have hcast2 : ((Nat.find hex - 1 : ℕ) : ℝ) + 1 = (Nat.find hex : ℝ) := by
      have hnat : Nat.find hex - 1 + 1 = Nat.find hex := Nat.sub_add_cancel hj1
      have := congrArg (fun n : ℕ => (n : ℝ)) hnat
      push_cast at this
      exact this
    rw [hcast2] at hnot
    linarith

end Work.KT
