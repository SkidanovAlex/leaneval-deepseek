import Mathlib

/-!
# Telescoping bound for a walk with bounded increments

If every increment `m (j + 1) - m j` of a walk `m : ℕ → ℝ` over the range `j < n`
is at most `c₁`, then the total displacement `m n - m 0` is at most `n * c₁`:
the increments telescope, and there are `n` of them.
-/

namespace Work.Pert.Count

/-- Telescoping bound: a walk whose `n` successive increments are each `≤ c₁`
grows by at most `n * c₁`. -/
theorem walk_telescope_le {m : ℕ → ℝ} {c₁ : ℝ} {n : ℕ}
    (hstep : ∀ j < n, m (j + 1) - m j ≤ c₁) :
    m n - m 0 ≤ (n : ℝ) * c₁ := by
  -- The differences telescope to the total displacement.
  rw [← Finset.sum_range_sub m n]
  calc ∑ j ∈ Finset.range n, (m (j + 1) - m j)
      ≤ ∑ _j ∈ Finset.range n, c₁ :=
        Finset.sum_le_sum (fun j hj => hstep j (Finset.mem_range.mp hj))
    _ = (n : ℝ) * c₁ := by simp

end Work.Pert.Count
