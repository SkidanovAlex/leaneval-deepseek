import Mathlib

namespace Work.BourgainPlan.Maximal

/-- For `w > 0`, the shifted inverse-square series `∑ 1/(w+k)^2` converges, with
`∑ 1/(w+k)^2 ≤ 1/w + 1/w^2`. -/
theorem nat_inv_sq_shift_tail (w : ℝ) (hw : 0 < w) :
    Summable (fun k : ℕ => 1 / (w + k) ^ 2) ∧
      (∑' k : ℕ, 1 / (w + k) ^ 2) ≤ 1 / w + 1 / w ^ 2 := by
  -- Termwise bound: `1/(w+k+1)^2 ≤ 1/(w+k) - 1/(w+k+1)`.
  have hstep : ∀ k : ℕ,
      1 / (w + ((k:ℝ) + 1)) ^ 2 ≤ 1 / (w + (k:ℝ)) - 1 / (w + ((k:ℝ) + 1)) := by
    intro k
    have hA : 1 / (w + ((k:ℝ) + 1)) ^ 2
        = 1 / ((w + ((k:ℝ) + 1)) * (w + ((k:ℝ) + 1))) := by ring_nf
    have hB : 1 / (w + (k:ℝ)) - 1 / (w + ((k:ℝ) + 1))
        = 1 / ((w + (k:ℝ)) * (w + ((k:ℝ) + 1))) := by
      field_simp
      ring
    rw [hA, hB]
    apply one_div_le_one_div_of_le
    · positivity
    · nlinarith
  -- Telescoping identity for the comparison series.
  have htel : ∀ m : ℕ,
      ∑ k ∈ Finset.range m, (1 / (w + (k:ℝ)) - 1 / (w + ((k:ℝ) + 1)))
        = 1 / w - 1 / (w + m) := by
    intro m
    have h := Finset.sum_range_sub (fun k : ℕ => -(1 / (w + (k:ℝ)))) m
    simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, add_zero] at h
    have h' : ∑ k ∈ Finset.range m, (1 / (w + (k:ℝ)) - 1 / (w + ((k:ℝ) + 1)))
        = ∑ k ∈ Finset.range m, (-(1 / (w + ((k:ℝ) + 1))) - -(1 / (w + (k:ℝ)))) := by
      apply Finset.sum_congr rfl
      intro k _
      ring
    rw [h', h]
    ring
  -- Bound on every finite partial sum.
  have hbound : ∀ n : ℕ,
      ∑ i ∈ Finset.range n, 1 / (w + (i:ℝ)) ^ 2 ≤ 1 / w + 1 / w ^ 2 := by
    intro n
    cases n with
    | zero =>
      rw [Finset.range_zero, Finset.sum_empty]
      positivity
    | succ m =>
      rw [Finset.sum_range_succ']
      simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, add_zero]
      have hsum1 : ∑ k ∈ Finset.range m, 1 / (w + ((k:ℝ) + 1)) ^ 2
          ≤ ∑ k ∈ Finset.range m, (1 / (w + (k:ℝ)) - 1 / (w + ((k:ℝ) + 1))) :=
        Finset.sum_le_sum (fun k _ => hstep k)
      calc ∑ k ∈ Finset.range m, 1 / (w + ((k:ℝ) + 1)) ^ 2 + 1 / w ^ 2
          ≤ ∑ k ∈ Finset.range m, (1 / (w + (k:ℝ)) - 1 / (w + ((k:ℝ) + 1)))
              + 1 / w ^ 2 := by
            linarith [hsum1]
        _ = (1 / w - 1 / (w + m)) + 1 / w ^ 2 := by rw [htel m]
        _ ≤ 1 / w + 1 / w ^ 2 := by
            have hpos : (0:ℝ) < 1 / (w + m) := by positivity
            linarith
  have hnn : ∀ k : ℕ, (0:ℝ) ≤ 1 / (w + (k:ℝ)) ^ 2 := by intro k; positivity
  exact ⟨summable_of_sum_range_le hnn hbound, Real.tsum_le_of_sum_range_le hnn hbound⟩

end Work.BourgainPlan.Maximal
