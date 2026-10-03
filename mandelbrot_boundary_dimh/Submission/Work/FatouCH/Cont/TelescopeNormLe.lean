import Mathlib

namespace Work.FatouCH.Cont

/-- Telescoping norm estimate: the total displacement from `g 0` to `g N` is bounded
by the sum of the (upper bounds on the) successive increments. -/
theorem TelescopeNormLe {g : ℕ → ℂ} {b : ℕ → ℝ} {N : ℕ}
    (hb : ∀ i < N, ‖g (i + 1) - g i‖ ≤ b i) :
    ‖g N - g 0‖ ≤ ∑ i ∈ Finset.range N, b i := by
  have h1 : ‖g N - g 0‖ = ‖∑ i ∈ Finset.range N, (g (i + 1) - g i)‖ := by
    rw [Finset.sum_range_sub]
  rw [h1]
  exact le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun i hi => hb i (Finset.mem_range.mp hi))

end Work.FatouCH.Cont
