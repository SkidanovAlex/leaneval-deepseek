import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Basic.Real.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Coercivity

/-- Reindexing identity on the triangular index region `{(a,b) : 1 ≤ a, a + b ≤ k+1}`:
splitting off the row `a = 1` (which contributes `∑_{i≤k} G 1 i`) leaves the rows
`a = i+1 ≥ 2`, which are exactly the shifted triangle `1 ≤ i, i + j ≤ k`. -/
theorem SumRowShift_eq (k : ℕ) (G : ℕ → ℕ → ℝ) :
    (∑ i ∈ Finset.range (k + 1), G 1 i)
      + (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
          (if 1 ≤ i ∧ i + j ≤ k then G (i + 1) j else 0))
    = ∑ a ∈ Finset.range (k + 2), ∑ b ∈ Finset.range (k + 2),
        (if 1 ≤ a ∧ a + b ≤ k + 1 then G a b else 0) := by
  -- The shifted inner sums agree: row `a = i+2` on the right is the same as
  -- the `(i+1)`-th inner sum on the left (the range `k+2` has a spurious, vanishing
  -- last term).
  have hinner : ∀ i : ℕ,
      (∑ b ∈ Finset.range (k + 2),
          (if 1 ≤ i + 2 ∧ i + 2 + b ≤ k + 1 then G (i + 2) b else 0))
        = (∑ j ∈ Finset.range (k + 1),
          (if 1 ≤ i + 1 ∧ i + 1 + j ≤ k then G (i + 2) j else 0)) := by
    intro i
    rw [Finset.sum_range_succ]
    have hz : (if 1 ≤ i + 2 ∧ i + 2 + (k + 1) ≤ k + 1 then G (i + 2) (k + 1) else 0) = 0 := by
      rw [ite_eq_right (by omega)]
    rw [hz, add_zero]
    apply Finset.sum_congr rfl
    intro j hj
    by_cases h : 1 ≤ i + 2 ∧ i + 2 + j ≤ k + 1
    · rw [ite_eq_left h, ite_eq_left (show 1 ≤ i + 1 ∧ i + 1 + j ≤ k by omega)]
    · rw [ite_eq_right h, ite_eq_right (show ¬(1 ≤ i + 1 ∧ i + 1 + j ≤ k) by omega)]
  -- The row `a = 1` on the right is the first summand on the left.
  have hT1 : (∑ b ∈ Finset.range (k + 2),
        (if 1 ≤ 1 ∧ 1 + b ≤ k + 1 then G 1 b else 0))
      = (∑ i ∈ Finset.range (k + 1), G 1 i) := by
    rw [Finset.sum_range_succ]
    have hz : (if 1 ≤ 1 ∧ 1 + (k + 1) ≤ k + 1 then G 1 (k + 1) else 0) = 0 := by
      rw [ite_eq_right (by omega)]
    rw [hz, add_zero]
    apply Finset.sum_congr rfl
    intro b hb
    rw [Finset.mem_range] at hb
    rw [ite_eq_left (show 1 ≤ 1 ∧ 1 + b ≤ k + 1 by omega)]
  -- Peel the vanishing `i = 0` term off the second summand on the left.
  have hT2 : (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
          (if 1 ≤ i ∧ i + j ≤ k then G (i + 1) j else 0))
      = ∑ i ∈ Finset.range k, ∑ j ∈ Finset.range (k + 1),
          (if 1 ≤ i + 1 ∧ i + 1 + j ≤ k then G (i + 2) j else 0) := by
    rw [Finset.sum_range_succ']
    have hz : (∑ j ∈ Finset.range (k + 1),
          (if 1 ≤ (0:ℕ) ∧ (0:ℕ) + j ≤ k then G ((0:ℕ) + 1) j else 0)) = 0 := by simp
    rw [hz, add_zero]
  -- Peel the rows `a = 0` and `a = 1` off the right-hand side.
  have hR : (∑ a ∈ Finset.range (k + 2), ∑ b ∈ Finset.range (k + 2),
        (if 1 ≤ a ∧ a + b ≤ k + 1 then G a b else 0))
      = (∑ i ∈ Finset.range k, ∑ b ∈ Finset.range (k + 2),
            (if 1 ≤ i + 2 ∧ i + 2 + b ≤ k + 1 then G (i + 2) b else 0))
        + (∑ b ∈ Finset.range (k + 2),
            (if 1 ≤ 1 ∧ 1 + b ≤ k + 1 then G 1 b else 0)) := by
    rw [Finset.sum_range_succ']
    have hz0 : (∑ b ∈ Finset.range (k + 2),
          (if 1 ≤ (0:ℕ) ∧ (0:ℕ) + b ≤ k + 1 then G (0:ℕ) b else 0)) = 0 := by simp
    rw [hz0, add_zero]
    rw [Finset.sum_range_succ']
  -- Assemble.
  rw [← hT1, hT2, hR]
  rw [show (∑ i ∈ Finset.range k, ∑ j ∈ Finset.range (k + 1),
        (if 1 ≤ i + 1 ∧ i + 1 + j ≤ k then G (i + 2) j else 0))
      = ∑ i ∈ Finset.range k, ∑ b ∈ Finset.range (k + 2),
        (if 1 ≤ i + 2 ∧ i + 2 + b ≤ k + 1 then G (i + 2) b else 0) from
    Finset.sum_congr rfl (fun i _ => (hinner i).symm)]
  exact add_comm _ _

end Work.Coercivity
