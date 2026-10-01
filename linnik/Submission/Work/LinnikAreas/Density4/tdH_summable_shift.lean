import Mathlib
import Submission.Work.LinnikAreas.Density4.thetaDiag_eval_defs
import Submission.Work.LinnikAreas.Density4.thetaDiag_sum_bounds

namespace Work.LinnikAreas.Density4

/-- The shifted majorant is nonnegative: `0 ≤ tdH σ A (n+1)`.
The base `n+1` of the power is a nonnegative real, and the exponential is positive. -/
lemma tdH_shift_nonneg (σ A : ℝ) (n : ℕ) : 0 ≤ tdH σ A (n + 1) := by
  have hb : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
  unfold tdH
  rw [Nat.cast_add, Nat.cast_one]
  exact mul_nonneg (Real.rpow_nonneg hb _) (Real.exp_pos _).le

/-- Pointwise domination of the shifted majorant by a pure exponential:
for `σ ≤ 1` and `A > 0`, `tdH σ A (n+1) ≤ exp (-(1/A) * (n+1))`.

The power `(n+1)^{σ-1}` is `≤ 1` because the base is `≥ 1` and the exponent `σ - 1 ≤ 0`,
and the exponential factor is rewritten as `exp (-(1/A) * (n+1))`. -/
lemma tdH_shift_le_exp (σ A : ℝ) (hσ1 : σ ≤ 1) (_hA : 0 < A) (n : ℕ) :
    tdH σ A (n + 1) ≤ Real.exp (-(1 / A) * ((n : ℝ) + 1)) := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have h1 : ((n : ℝ) + 1) ^ (σ - 1) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hn1 (by linarith)
  have harg : -(↑n + 1) / A = -(1 / A) * (↑n + 1) := by
    ring
  unfold tdH
  rw [Nat.cast_add, Nat.cast_one, harg]
  calc ((↑n + 1) ^ (σ - 1)) * Real.exp (-(1 / A) * (↑n + 1))
      ≤ 1 * Real.exp (-(1 / A) * (↑n + 1)) :=
        mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    _ = Real.exp (-(1 / A) * (↑n + 1)) := one_mul _

theorem tdH_summable_shift (σ A : ℝ) (hσ1 : σ ≤ 1) (hA : 0 < A) :
    Summable (fun n : ℕ => tdH σ A (n + 1)) := by
  have hc : -(1 / A) < 0 := by
    have : (0 : ℝ) < 1 / A := by positivity
    linarith
  have hbig : Summable (fun n : ℕ => Real.exp (-(1 / A) * ((n : ℝ) + 1))) :=
    Real.summable_exp_nat_mul_of_ge hc (f := fun n : ℕ => (n : ℝ) + 1)
      (fun i => by linarith)
  refine Summable.of_nonneg_of_le (fun n => tdH_shift_nonneg σ A n) (fun n => ?_) hbig
  exact tdH_shift_le_exp σ A hσ1 hA n

end Work.LinnikAreas.Density4
