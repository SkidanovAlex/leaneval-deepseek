import Mathlib.Algebra.Ring.Rat

namespace Commons.Data.Rat

/-- For a rational `q`, `q.den * q = q.num`, in `ℚ`. -/
lemma den_mul_self (q : ℚ) : (q.den : ℚ) * q = (q.num : ℚ) := by
  rw [mul_comm, Rat.mul_den_eq_num]

end Commons.Data.Rat