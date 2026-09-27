import Mathlib
import Submission.Work.Octonion.Basic

open scoped Quaternion

namespace Work.Octonion

/-- `(1, 0)` is a right unit for the Cayley–Dickson product on `ℍ × ℍ`. -/
theorem cdMul_one (x : ℍ × ℍ) : Submission.Octonion.cdMul x (1, 0) = x := by
  simp [Submission.Octonion.cdMul]

theorem mul_one (x : Submission.Octonion) : x * 1 = x := by
  apply WithLp.ofLp_injective
  simpa using cdMul_one (WithLp.ofLp x)

end Work.Octonion
