import ChallengeDeps
import Mathlib.Tactic

/-!
# Growth of the evaluation of an integer polynomial

A local copy of `Commons.Analysis.Polynomial.exists_abs_intCast_eval_le`: for a polynomial
`P : ℤ[X]` the evaluation `P.eval n` grows at most like `|n| ^ P.natDegree`.  The copy lives
here because the commons version imports `Mathlib`, which would disturb the instance priorities
needed for the syntactic comparison of the statements in `Submission.lean`.
-/

set_option autoImplicit false

namespace Submission

open _root_.PointwiseErgodicTheorems
open Polynomial

namespace PointwiseErgodicTheorems

/-- For an integer polynomial `P` there is a constant `C ≥ 0` with
`|P.eval n| ≤ C * max |n| 1 ^ P.natDegree`. -/
theorem exists_abs_intCast_eval_le (P : ℤ[X]) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℤ,
      |((Polynomial.eval n P : ℤ) : ℝ)| ≤ C * (max |(n : ℝ)| 1) ^ P.natDegree := by
  refine ⟨∑ k ∈ P.support, |((P.coeff k : ℤ) : ℝ)|, by positivity, ?_⟩
  intro n
  set b : ℝ := max |(n : ℝ)| 1 with hb
  have hb1 : 1 ≤ b := le_max_right _ _
  have hcast : ((Polynomial.eval n P : ℤ) : ℝ) =
      ∑ k ∈ P.support, ((P.coeff k : ℤ) : ℝ) * (n : ℝ) ^ k := by
    rw [Polynomial.eval_eq_sum, Polynomial.sum_def]
    push_cast
    rfl
  rw [hcast]
  calc
    |∑ k ∈ P.support, ((P.coeff k : ℤ) : ℝ) * (n : ℝ) ^ k|
        ≤ ∑ k ∈ P.support, |((P.coeff k : ℤ) : ℝ) * (n : ℝ) ^ k| :=
          Finset.abs_sum_le_sum_abs _ _
    _ = ∑ k ∈ P.support, |((P.coeff k : ℤ) : ℝ)| * |(n : ℝ)| ^ k := by
          apply Finset.sum_congr rfl
          intro k _
          rw [abs_mul, abs_pow]
    _ ≤ ∑ k ∈ P.support, |((P.coeff k : ℤ) : ℝ)| * b ^ P.natDegree := by
          apply Finset.sum_le_sum
          intro k hk
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
          calc |(n : ℝ)| ^ k ≤ b ^ k := pow_le_pow_left₀ (abs_nonneg _) (le_max_left _ _) k
            _ ≤ b ^ P.natDegree := pow_le_pow_right₀ hb1 (Polynomial.le_natDegree_of_mem_supp k hk)
    _ = (∑ k ∈ P.support, |((P.coeff k : ℤ) : ℝ)|) * b ^ P.natDegree := by
          rw [Finset.sum_mul]

end PointwiseErgodicTheorems
end Submission
