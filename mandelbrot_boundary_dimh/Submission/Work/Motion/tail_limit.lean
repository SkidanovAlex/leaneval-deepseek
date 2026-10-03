import Mathlib

set_option linter.unusedVariables false

namespace Work.Motion

/-- If a real number `a` is bounded by `b + C t^(k-1)` for every `k ≥ 1`, with `0 ≤ t < 1` and
`C ≥ 0`, then `a ≤ b`. -/
theorem tail_limit {a b C t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) (hC : 0 ≤ C)
    (h : ∀ k : ℕ, 1 ≤ k → a ≤ b + C * t ^ (k - 1)) : a ≤ b := by
  -- It suffices to show `a ≤ b + ε` for every `ε > 0`.
  refine le_of_forall_pos_le_add fun ε hε => ?_
  -- Since `0 ≤ t < 1`, the sequence `C * t^n` tends to `0`.
  have htend : Filter.Tendsto (fun n : ℕ => C * t ^ n) Filter.atTop (nhds 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one ht0 ht1).const_mul C
  -- Hence eventually `C * t^n < ε`.
  have hev : ∀ᶠ n : ℕ in Filter.atTop, C * t ^ n < ε :=
    htend.eventually (isOpen_Iio.mem_nhds hε)
  rw [Filter.eventually_atTop] at hev
  obtain ⟨N, hN⟩ := hev
  -- Apply the hypothesis at `k = N + 1`, where `t^(k-1) = t^N`.
  have hle : a ≤ b + C * t ^ N := by
    have := h (N + 1) (Nat.le_add_left 1 N)
    rwa [Nat.add_sub_cancel] at this
  have := hN N le_rfl
  linarith

end Work.Motion
