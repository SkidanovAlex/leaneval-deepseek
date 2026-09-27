import Mathlib
import Submission.Work.Octonion.Basic

open scoped Quaternion

namespace Work.Octonion

/-- Left multiplication by the identity pair `(1, 0)` under the Cayley–Dickson product. -/
theorem cdMul_one_left (y : Quaternion ℝ × Quaternion ℝ) :
    Submission.Octonion.cdMul (1, 0) y = y := by
  obtain ⟨a, b⟩ := y
  simp [Submission.Octonion.cdMul]

theorem one_mul (x : Submission.Octonion) : 1 * x = x := by
  apply WithLp.ofLp_injective 2
  rw [Submission.Octonion.ofLp_mul, Submission.Octonion.ofLp_one, cdMul_one_left]

end Work.Octonion
