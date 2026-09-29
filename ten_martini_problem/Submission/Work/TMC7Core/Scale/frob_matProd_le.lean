import Mathlib
import Submission.Work.TMC7Core.Cocycle
import Submission.Work.TMC7Core.Cocycle.frob_mul_le

namespace Work.TMC7Core.Scale

/-- Growth bound for ordered products: if `frob (A j) ≤ M` for all `j` with `0 ≤ M`, then
`matProd A n = A (n-1) * ⋯ * A 0` has Frobenius norm at most `√2 * M ^ n`.

The constant `√2` is exactly `frob (1 : Matrix (Fin 2) (Fin 2) ℂ)`, so the estimate is
sharp at `n = 0`; for `n ≥ 1` the `√2` can be dropped. -/
theorem frob_matProd_le (A : ℕ → Matrix (Fin 2) (Fin 2) ℂ) (M : ℝ) (hM : 0 ≤ M)
    (hA : ∀ j, Work.TMC7Core.frob (A j) ≤ M) (n : ℕ) :
    Work.TMC7Core.frob (Work.TMC7Core.matProd A n) ≤ Real.sqrt 2 * M ^ n := by
  induction n with
  | zero => rw [matProd_zero, frob_one, pow_zero, mul_one]
  | succ n ih =>
    rw [matProd_succ]
    calc Work.TMC7Core.frob (A n * matProd A n)
        ≤ Work.TMC7Core.frob (A n) * Work.TMC7Core.frob (Work.TMC7Core.matProd A n) :=
          Cocycle.frob_mul_le _ _
      _ ≤ M * (Real.sqrt 2 * M ^ n) :=
          mul_le_mul (hA n) ih (frob_nonneg _) hM
      _ = Real.sqrt 2 * M ^ (n + 1) := by rw [pow_succ]; ring

end Work.TMC7Core.Scale
