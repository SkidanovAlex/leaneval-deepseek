import Mathlib
import Submission.Work.TMC14Core.hyps_reduce

namespace Work.TMC14Core

/-- The traces of the powers of a `2 × 2` real matrix with determinant `1` and
trace `t` satisfy the Chebyshev recurrence `s_{n+2} = t·s_{n+1} − s_n`, and the
values `u n = 2·cos (n θ)` with `2 cos θ = t` satisfy the same recurrence with
the same initial data.  Hence `tr A^m = 2 cos (m θ)`, which is bounded by `2`. -/
theorem sl2TracePowEasy (m : ℕ) (A : Matrix (Fin 2) (Fin 2) ℝ) (hdet : A.det = 1)
    (h : |A.trace| ≤ 2) : |(A ^ m).trace| ≤ 2 := by
  -- `A.trace / 2 ∈ [-1, 1]`, so it is the cosine of some angle `θ`.
  have ht2 : -1 ≤ A.trace / 2 ∧ A.trace / 2 ≤ 1 := by
    constructor <;> nlinarith [h, neg_abs_le A.trace, le_abs_self A.trace]
  set θ : ℝ := Real.arccos (A.trace / 2) with hθdef
  have hcos : Real.cos θ = A.trace / 2 := by
    rw [hθdef]
    exact Real.cos_arccos ht2.1 ht2.2
  have htrace : A.trace = 2 * Real.cos θ := by linarith
  -- The two sequences agree.
  have key : ∀ n : ℕ, (A ^ n).trace = 2 * Real.cos ((n : ℝ) * θ) := by
    refine Nat.twoStepInduction ?_ ?_ ?_
    · simp
    · simp only [pow_one, Nat.cast_one, one_mul]
      exact htrace
    · intro n ih0 ih1
      -- trig product-to-sum identity: `2 cos a cos b = cos (a+b) + cos (a-b)`
      have hid : Real.cos (((n : ℝ) + 2) * θ) + Real.cos ((n : ℝ) * θ)
          = 2 * Real.cos (((n : ℝ) + 1) * θ) * Real.cos θ := by
        have hadd := Real.cos_add_cos (x := ((n : ℝ) + 2) * θ) (y := (n : ℝ) * θ)
        have h1 : (((n : ℝ) + 2) * θ + (n : ℝ) * θ) / 2 = ((n : ℝ) + 1) * θ := by ring
        have h2 : (((n : ℝ) + 2) * θ - (n : ℝ) * θ) / 2 = θ := by ring
        rwa [h1, h2] at hadd
      rw [trace_pow_rec A hdet n, ih0, ih1, htrace]
      push_cast
      nlinarith [hid]
  rw [key m, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  nlinarith [Real.abs_cos_le_one ((m : ℝ) * θ)]

end Work.TMC14Core
