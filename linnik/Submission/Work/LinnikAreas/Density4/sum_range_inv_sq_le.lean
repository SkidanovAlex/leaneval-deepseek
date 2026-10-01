import Mathlib

namespace Work.LinnikAreas.Density4

/-- The partial sums of `1/(n+2)^2` over `n < N` are at most `1`, since the full sum
`∑_{n≥0} 1/(n+2)^2 = ζ(2) - 1 < 1`.  The proof compares each term with the telescoping
difference `1/(n+1) - 1/(n+2) = 1/((n+1)(n+2)) ≥ 1/(n+2)^2`. -/
lemma sum_range_inv_sq_le (N : ℕ) :
    (∑ i ∈ Finset.range N, (1 : ℝ) / ((i : ℝ) + 2) ^ 2) ≤ 1 := by
  -- Termwise bound: `1/(n+2)^2 ≤ 1/(n+1) - 1/(n+2) = 1/((n+1)(n+2))`.
  have hterm : ∀ i ∈ Finset.range N,
      (1 : ℝ) / ((i : ℝ) + 2) ^ 2 ≤ (1 : ℝ) / ((i : ℝ) + 1) - 1 / ((i : ℝ) + 2) := by
    intro i _
    have h1 : (0 : ℝ) < ((i : ℝ) + 1) * ((i : ℝ) + 2) := by positivity
    have h2 : ((i : ℝ) + 1) * ((i : ℝ) + 2) ≤ ((i : ℝ) + 2) ^ 2 := by
      have hle : (i : ℝ) + 1 ≤ (i : ℝ) + 2 := by linarith
      have h0 : (0 : ℝ) ≤ (i : ℝ) + 2 := by positivity
      nlinarith [mul_le_mul_of_nonneg_right hle h0]
    have h3 := one_div_le_one_div_of_le h1 h2
    have h4 : (1 : ℝ) / ((i : ℝ) + 1) - 1 / ((i : ℝ) + 2)
        = 1 / (((i : ℝ) + 1) * ((i : ℝ) + 2)) := by
      field_simp
      ring
    rw [h4]
    exact h3
  -- Telescoping: `∑_{i<N} (1/(i+1) - 1/(i+2)) = 1 - 1/(N+1)`.
  have htel : (∑ i ∈ Finset.range N, ((1 : ℝ) / ((i : ℝ) + 1) - 1 / ((i : ℝ) + 2)))
      = 1 - 1 / ((N : ℝ) + 1) := by
    have hcongr : (∑ i ∈ Finset.range N, ((1 : ℝ) / ((i : ℝ) + 1) - 1 / ((i : ℝ) + 2)))
        = ∑ i ∈ Finset.range N,
            ((fun j : ℕ => (1 : ℝ) / ((j : ℝ) + 1)) i
              - (fun j : ℕ => (1 : ℝ) / ((j : ℝ) + 1)) (i + 1)) := by
      apply Finset.sum_congr rfl
      intro i _
      show (1 : ℝ) / ((i : ℝ) + 1) - 1 / ((i : ℝ) + 2)
          = (1 : ℝ) / ((i : ℝ) + 1) - 1 / ((((i + 1 : ℕ)) : ℝ) + 1)
      push_cast
      ring_nf
    rw [hcongr, Finset.sum_range_sub']
    norm_num
  calc (∑ i ∈ Finset.range N, (1 : ℝ) / ((i : ℝ) + 2) ^ 2)
      ≤ ∑ i ∈ Finset.range N, ((1 : ℝ) / ((i : ℝ) + 1) - 1 / ((i : ℝ) + 2)) :=
        Finset.sum_le_sum hterm
    _ = 1 - 1 / ((N : ℝ) + 1) := htel
    _ ≤ 1 := by
        have : (0 : ℝ) < 1 / ((N : ℝ) + 1) := by positivity
        linarith

end Work.LinnikAreas.Density4
