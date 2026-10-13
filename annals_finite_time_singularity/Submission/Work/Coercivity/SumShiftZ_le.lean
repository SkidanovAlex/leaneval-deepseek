import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Basic.Real.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Coercivity

/-- The left-hand double sum over the `(k+1) × (k+1)` square, with the term `G i (j+1)`
selected by `1 ≤ i ∧ i + j ≤ k`, is dominated by the right-hand double sum over the
`(k+2) × (k+2)` square selecting `1 ≤ a ∧ a + b ≤ k+1`.  Indeed the substitution
`(a, b) = (i, j+1)` is injective and the target index set is contained in the source
index set; all omitted terms are nonnegative by `hG`. -/
theorem SumShiftZ_le (k : ℕ) (G : ℕ → ℕ → ℝ) (hG : ∀ a b, 0 ≤ G a b) :
    (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
        (if 1 ≤ i ∧ i + j ≤ k then G i (j + 1) else 0))
    ≤ ∑ a ∈ Finset.range (k + 2), ∑ b ∈ Finset.range (k + 2),
        (if 1 ≤ a ∧ a + b ≤ k + 1 then G a b else 0) := by
  -- Pointwise bound of the inner sums: shift the `j`-index by one.
  have hstep : ∀ i : ℕ,
      (∑ j ∈ Finset.range (k + 1), (if 1 ≤ i ∧ i + j ≤ k then G i (j + 1) else 0))
      ≤ (∑ b ∈ Finset.range (k + 2), (if 1 ≤ i ∧ i + b ≤ k + 1 then G i b else 0)) := by
    intro i
    let F : ℕ → ℝ := fun b => if 1 ≤ i ∧ i + b ≤ k + 1 then G i b else 0
    -- Rewrite the inner left sum as a sum over the image `{1,…,k+1}` of the same `F`.
    have hL : (∑ j ∈ Finset.range (k + 1),
          (if 1 ≤ i ∧ i + j ≤ k then G i (j + 1) else 0))
        = ∑ b ∈ (Finset.range (k + 1)).image (fun j => j + 1), F b := by
      rw [Finset.sum_image]
      · apply Finset.sum_congr rfl
        intro j hj
        dsimp only [F]
        by_cases h : 1 ≤ i ∧ i + j ≤ k
        · have h2 : 1 ≤ i ∧ i + (j + 1) ≤ k + 1 := by omega
          rw [ite_eq_left h, ite_eq_left h2]
        · have h2 : ¬ (1 ≤ i ∧ i + (j + 1) ≤ k + 1) := by omega
          rw [ite_eq_right h, ite_eq_right h2]
      · intro x hx y hy hxy
        simp only at hxy
        omega
    rw [hL]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · -- the shifted index set sits inside `range (k+2)`
      intro b hb
      rcases Finset.mem_image.mp hb with ⟨j, hj, rfl⟩
      simp only [Finset.mem_range] at hj ⊢
      omega
    · -- omitted terms are nonnegative
      intro b hb hnb
      dsimp only [F]
      split_ifs with h
      · exact hG i b
      · exact le_refl 0
  calc (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
        (if 1 ≤ i ∧ i + j ≤ k then G i (j + 1) else 0))
      ≤ ∑ i ∈ Finset.range (k + 1), (∑ b ∈ Finset.range (k + 2),
          (if 1 ≤ i ∧ i + b ≤ k + 1 then G i b else 0)) :=
        Finset.sum_le_sum (fun i hi => hstep i)
    _ ≤ ∑ a ∈ Finset.range (k + 2), (∑ b ∈ Finset.range (k + 2),
          (if 1 ≤ a ∧ a + b ≤ k + 1 then G a b else 0)) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro a ha
          simp only [Finset.mem_range] at ha ⊢
          omega
        · intro a ha hna
          apply Finset.sum_nonneg
          intro b hb
          split_ifs with h
          · exact hG a b
          · exact le_refl 0

end Work.Coercivity
