import Mathlib
import Submission.Work.TMC7Core.Trig

namespace Work.TMC7Core.Trig

/-- `e^{2πix} · ω^j = e^{2πi(x + jα)}` where `ω = e^{2πiα}`, the elementary
multiplicativity of the complex exponential used all over the Laurent-cocycle
calculus. -/
theorem exp_mul_omega_pow (α x : ℝ) (j : ℕ) :
    Complex.exp (2 * Real.pi * Complex.I * x) * (omega α) ^ j
      = Complex.exp (2 * Real.pi * Complex.I * (x + (j : ℝ) * α)) := by
  rw [omega, ← Complex.exp_nat_mul, ← Complex.exp_add]
  congr 1
  push_cast
  ring

end Work.TMC7Core.Trig
