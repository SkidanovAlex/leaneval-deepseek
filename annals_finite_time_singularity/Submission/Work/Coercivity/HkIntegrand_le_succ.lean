import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Coercivity

/-- The `H^k`-integrand is monotone in `k`: enlarging `k` only adds non-negative
terms, both in the first (pure `D_z`) sum and in the double (mixed) sum, and
moreover weakens the constraint `i + j ≤ k` on the mixed summands. -/
theorem HkIntegrand_le_succ (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.HkIntegrand α k f z θ ≤ Work.Spaces.HkIntegrand α (k + 1) f z θ := by
  simp only [Work.Spaces.HkIntegrand]
  refine add_le_add ?_ ?_
  · -- the first sum: `range (k+1) ⊆ range (k+2)` and all summands are squares
    refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega)) ?_
    intro i _ _
    positivity
  · -- the double sum
    have inner : ∀ i : ℕ,
        (∑ j ∈ Finset.range (k + 1),
            (if 1 ≤ i ∧ i + j ≤ k then (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0))
        ≤ (∑ j ∈ Finset.range (k + 2),
            (if 1 ≤ i ∧ i + j ≤ k + 1 then
              (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0)) := by
      intro i
      -- pointwise in `j`: the constraint `i + j ≤ k` implies `i + j ≤ k + 1`
      have hpt : ∀ j : ℕ,
          (if 1 ≤ i ∧ i + j ≤ k then (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0)
          ≤ (if 1 ≤ i ∧ i + j ≤ k + 1 then
              (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0) := by
        intro j
        split_ifs with h1 h2
        · exact le_refl _
        · exact absurd ⟨h1.1, by omega⟩ h2
        · positivity
        · exact le_refl 0
      calc (∑ j ∈ Finset.range (k + 1),
              (if 1 ≤ i ∧ i + j ≤ k then (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0))
          ≤ (∑ j ∈ Finset.range (k + 1),
              (if 1 ≤ i ∧ i + j ≤ k + 1 then
                (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0)) :=
            Finset.sum_le_sum (fun j _ => hpt j)
        _ ≤ (∑ j ∈ Finset.range (k + 2),
              (if 1 ≤ i ∧ i + j ≤ k + 1 then
                (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0)) := by
            refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega)) ?_
            intro j _ _
            by_cases h2 : 1 ≤ i ∧ i + j ≤ k + 1
            · simp [h2]; positivity
            · simp [h2]
    calc (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
            (if 1 ≤ i ∧ i + j ≤ k then (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0))
        ≤ (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 2),
            (if 1 ≤ i ∧ i + j ≤ k + 1 then
              (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0)) :=
          Finset.sum_le_sum (fun i _ => inner i)
      _ ≤ (∑ i ∈ Finset.range (k + 2), ∑ j ∈ Finset.range (k + 2),
            (if 1 ≤ i ∧ i + j ≤ k + 1 then
              (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0)) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega)) ?_
          intro i _ _
          refine Finset.sum_nonneg (fun j _ => ?_)
          by_cases h2 : 1 ≤ i ∧ i + j ≤ k + 1
          · simp [h2]; positivity
          · simp [h2]

end Work.Coercivity
