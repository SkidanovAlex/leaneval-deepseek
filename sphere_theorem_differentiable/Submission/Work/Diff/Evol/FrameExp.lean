import Mathlib
import Submission.Diff.Evol
import Submission.Work.Diff.Evol.Vocab

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The matrix exponential as an orthogonal-valued correction

For a `C^∞` matrix-valued function `B : M → Matrix (Fin n) (Fin n) ℝ` whose values are
skew-symmetric, the pointwise exponential `y ↦ exp (B y)` takes values in the orthogonal group,
equals `1` where `B` vanishes, and is `C^∞`.  These are the elementary facts behind the
"orthogonal correction" step of the construction of the parallel frame.
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology Matrix Matrix.Norms.Operator
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

namespace Work.Diff.Evol

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **The exponential of a skew-symmetric matrix is orthogonal** (on the left). -/
theorem exp_transpose_mul_exp {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ)
    (hB : Matrix.transpose B = -B) :
    Matrix.transpose (NormedSpace.exp B) * NormedSpace.exp B = 1 := by
  have hcomm : Commute (Matrix.transpose B) B := by
    rw [hB]; exact (Commute.refl B).neg_left
  rw [← Matrix.exp_transpose B, ← Matrix.exp_add_of_commute (Matrix.transpose B) B hcomm,
    hB, neg_add_cancel, NormedSpace.exp_zero]

/-- **The exponential of a skew-symmetric matrix is orthogonal** (on the right). -/
theorem exp_mul_exp_transpose {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ)
    (hB : Matrix.transpose B = -B) :
    NormedSpace.exp B * Matrix.transpose (NormedSpace.exp B) = 1 := by
  have hcomm : Commute B (Matrix.transpose B) := by
    rw [hB]; exact (Commute.refl B).neg_right
  rw [← Matrix.exp_transpose B,
    ← Matrix.exp_add_of_commute B (Matrix.transpose B) hcomm, hB, add_neg_cancel,
    NormedSpace.exp_zero]

/-- The (matrix) exponential is `C^∞`. -/
theorem contDiff_exp_matrix {n : ℕ} :
    ContDiff ℝ ∞ (NormedSpace.exp : Matrix (Fin n) (Fin n) ℝ → Matrix (Fin n) (Fin n) ℝ) :=
  contDiff_iff_contDiffAt.mpr fun y => (NormedSpace.exp_analytic y).contDiffAt

/-- **The exponential of a skew-valued matrix function is smooth.** -/
theorem smoothMap_exp_of_smooth {n : ℕ} (B : M → Matrix (Fin n) (Fin n) ℝ)
    (hB : SmoothMap I M B) : SmoothMap I M (fun y : M => NormedSpace.exp (B y)) :=
  (contDiff_exp_matrix (n := n)).contMDiff.comp hB

/-- The pointwise exponential is `1` where `B` vanishes. -/
theorem exp_apply_of_eq_zero {n : ℕ} (B : M → Matrix (Fin n) (Fin n) ℝ) {y : M}
    (h : B y = 0) : NormedSpace.exp (B y) = 1 := by
  rw [h, NormedSpace.exp_zero]

end Work.Diff.Evol
