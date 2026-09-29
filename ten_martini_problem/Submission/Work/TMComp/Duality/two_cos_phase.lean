import Mathlib
import Submission.Work.TMComp.Duality.Defs

namespace Work.TMComp.Duality

theorem two_cos_phase (α lam ϑ : ℝ) (n : ℤ) :
    ((2 * lam * Real.cos (2 * Real.pi * (ϑ + (n : ℝ) * α)) : ℝ) : ℂ)
      = (lam : ℂ) * Work.TMComp.Duality.ph α n * Work.TMComp.Duality.phR ϑ
        + (lam : ℂ) * Work.TMComp.Duality.ph α (-n) * Work.TMComp.Duality.phR (-ϑ) := by
  have h1 : ph α n * phR ϑ = phR (ϑ + (n : ℝ) * α) := by
    rw [ph, mul_comm, ← phR_add]
  have h2 : ph α (-n) * phR (-ϑ) = phR (-(ϑ + (n : ℝ) * α)) := by
    rw [ph, ← phR_add]
    congr 1
    push_cast
    ring
  have H1 : (lam : ℂ) * ph α n * phR ϑ = (lam : ℂ) * phR (ϑ + (n : ℝ) * α) := by
    rw [mul_assoc, h1]
  have H2 : (lam : ℂ) * ph α (-n) * phR (-ϑ) = (lam : ℂ) * phR (-(ϑ + (n : ℝ) * α)) := by
    rw [mul_assoc, h2]
  rw [H1, H2]
  have hcos : phR (ϑ + (n : ℝ) * α) + phR (-(ϑ + (n : ℝ) * α))
      = 2 * Complex.cos (((2 * Real.pi * (ϑ + (n : ℝ) * α)) : ℝ) : ℂ) := by
    have hx : phR (ϑ + (n : ℝ) * α)
        = Complex.exp ((((2 * Real.pi * (ϑ + (n : ℝ) * α)) : ℝ) : ℂ) * Complex.I) := rfl
    have hy : phR (-(ϑ + (n : ℝ) * α))
        = Complex.exp (-((((2 * Real.pi * (ϑ + (n : ℝ) * α)) : ℝ) : ℂ) * Complex.I)) := by
      rw [phR]
      congr 1
      push_cast
      ring
    rw [hx, hy, ← neg_mul, ← Complex.two_cos]
  rw [← mul_add, hcos, ← Complex.ofReal_cos]
  push_cast
  ring

end Work.TMComp.Duality
