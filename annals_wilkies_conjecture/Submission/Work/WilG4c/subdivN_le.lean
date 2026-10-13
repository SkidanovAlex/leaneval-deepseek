import Mathlib
import Submission.Work.WilG4c.StepHigherDefs

namespace Work.WilG4c

/-- The number `N = subdivN n r` of subdivision intervals grows at most linearly in `r`:
`subdivN n r ≤ K * r + 1` for a constant `K` depending only on `n` (namely
`⌈2 e (1 + n e) (n+1) + 1⌉`).  This is the counterpart of `Work.WilkG4c.subdivN_ge`, needed
for the *cardinality* bound of the §5.4 assembly (the number of subdivision charts is
`(3·(N-1)+1)^(n+1)`, which must be dominated by a polynomial in `r`). -/
theorem subdivN_le (n : ℕ) : ∃ K : ℕ, ∀ r : ℕ, Work.WilkG4c.subdivN n r ≤ K * r + 1 := by
  refine ⟨Nat.ceil (2 * Real.exp 1 * (1 + n * Real.exp 1) * ((n : ℝ) + 1) + 1), fun r => ?_⟩
  have hK : (2 * Real.exp 1 * (1 + n * Real.exp 1) * ((n : ℝ) + 1) + 1) ≤
      ((Nat.ceil (2 * Real.exp 1 * (1 + n * Real.exp 1) * ((n : ℝ) + 1) + 1) : ℕ) : ℝ) :=
    Nat.le_ceil _
  rw [show Work.WilkG4c.subdivN n r =
      Nat.ceil ((2 * Real.exp 1 * (1 + n * Real.exp 1) * ((n : ℝ) + 1) + 1) * (r : ℝ))
        from rfl,
    Nat.ceil_le]
  have hprod : (2 * Real.exp 1 * (1 + n * Real.exp 1) * ((n : ℝ) + 1) + 1) * (r : ℝ) ≤
      ((Nat.ceil (2 * Real.exp 1 * (1 + n * Real.exp 1) * ((n : ℝ) + 1) + 1) : ℕ) : ℝ)
        * (r : ℝ) :=
    mul_le_mul_of_nonneg_right hK (Nat.cast_nonneg r)
  push_cast
  linarith [hprod]

end Work.WilG4c
