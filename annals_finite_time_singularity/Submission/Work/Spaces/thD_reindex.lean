import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.Ring.RingNF

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Spaces

/-- Reindexing identity for the Leibniz/Pascal convolution:

`∑_{a} C(i,a) X(a+1) Y(i-a) + ∑_{a} C(i,a) X(a) Y(i-a+1)
  = ∑_{b} C(i+1,b) X(b) Y(i+1-b)`,

i.e. the derivative of the binomial convolution equals the sum of the two
shifted convolutions. -/
theorem thD_reindex (i : ℕ) (X Y : ℕ → ℝ) :
    (∑ a ∈ Finset.range (i + 1), (Nat.choose i a : ℝ) * X (a + 1) * Y (i - a))
      + (∑ a ∈ Finset.range (i + 1), (Nat.choose i a : ℝ) * X a * Y ((i - a) + 1))
    = ∑ b ∈ Finset.range (i + 1 + 1), (Nat.choose (i + 1) b : ℝ) * X b * Y (i + 1 - b) := by
  have hA : (∑ a ∈ Finset.range (i + 1), (Nat.choose i a : ℝ) * X (a + 1) * Y (i - a))
      = (∑ a ∈ Finset.range i, (Nat.choose i a : ℝ) * X (a + 1) * Y (i - a)) + X (i+1) * Y 0 := by
    rw [Finset.sum_range_succ]
    congr 1
    simp [Nat.choose_self]
  have hB : (∑ a ∈ Finset.range (i + 1), (Nat.choose i a : ℝ) * X a * Y ((i - a) + 1))
      = (∑ a ∈ Finset.range i, (Nat.choose i (a+1) : ℝ) * X (a + 1) * Y (i - a)) + X 0 * Y (i+1) := by
    rw [Finset.sum_range_succ']
    congr 1
    · apply Finset.sum_congr rfl
      intro a ha
      have ha' : a < i := Finset.mem_range.mp ha
      have h : i - (a+1) + 1 = i - a := by omega
      simp [h]
    · simp [Nat.choose_zero_right]
  have hS1 : (∑ b ∈ Finset.range (i + 1 + 1), (Nat.choose (i + 1) b : ℝ) * X b * Y (i + 1 - b))
      = (∑ b ∈ Finset.range (i+1), (Nat.choose (i + 1) (b+1) : ℝ) * X (b+1) * Y (i + 1 - (b+1))) + X 0 * Y (i+1) := by
    rw [Finset.sum_range_succ']
    have h0 : (Nat.choose (i + 1) 0 : ℝ) * X 0 * Y (i + 1 - 0) = X 0 * Y (i+1) := by
      simp [Nat.choose_zero_right]
    rw [h0]
  have hS2 : (∑ b ∈ Finset.range (i+1), (Nat.choose (i + 1) (b+1) : ℝ) * X (b+1) * Y (i + 1 - (b+1)))
      = (∑ b ∈ Finset.range i, (Nat.choose (i + 1) (b+1) : ℝ) * X (b+1) * Y (i - b)) + X (i+1) * Y 0 := by
    rw [Finset.sum_range_succ]
    congr 1
    · apply Finset.sum_congr rfl
      intro a ha
      have ha' : a < i := Finset.mem_range.mp ha
      have h : i + 1 - (a+1) = i - a := by omega
      simp [h]
    · simp [Nat.choose_self]
  have hJ : (∑ a ∈ Finset.range i, (Nat.choose i a : ℝ) * X (a + 1) * Y (i - a))
        + (∑ a ∈ Finset.range i, (Nat.choose i (a+1) : ℝ) * X (a + 1) * Y (i - a))
      = (∑ a ∈ Finset.range i, (Nat.choose (i+1) (a+1) : ℝ) * X (a + 1) * Y (i - a)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a ha
    rw [Nat.choose_succ_succ']
    push_cast
    ring
  rw [hA, hB, hS1, hS2]
  linarith [hJ]

end Work.Spaces
