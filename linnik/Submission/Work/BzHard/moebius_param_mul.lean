import Mathlib
import Submission.Work.BzHard.moebius_mul_cast_of_coprime

namespace Work.BzHard

theorem moebius_param_mul {m r t : ℕ} (h : Nat.Coprime m (r * t)) :
    (ArithmeticFunction.moebius (m * t) : ℝ) * (ArithmeticFunction.moebius (m * r) : ℝ)
      = (ArithmeticFunction.moebius r : ℝ) * (ArithmeticFunction.moebius t : ℝ) *
        (ArithmeticFunction.moebius m : ℝ) ^ 2 := by
  have hmt : Nat.Coprime m t := h.coprime_dvd_right (Nat.dvd_mul_left t r)
  have hmr : Nat.Coprime m r := h.coprime_dvd_right (Nat.dvd_mul_right r t)
  have h1 : (ArithmeticFunction.moebius (m * t) : ℝ)
      = (ArithmeticFunction.moebius m : ℝ) * (ArithmeticFunction.moebius t : ℝ) := by
    rw [ArithmeticFunction.IsMultiplicative.map_mul_of_coprime
      ArithmeticFunction.isMultiplicative_moebius hmt]
    push_cast
    ring
  have h2 : (ArithmeticFunction.moebius (m * r) : ℝ)
      = (ArithmeticFunction.moebius m : ℝ) * (ArithmeticFunction.moebius r : ℝ) := by
    rw [ArithmeticFunction.IsMultiplicative.map_mul_of_coprime
      ArithmeticFunction.isMultiplicative_moebius hmr]
    push_cast
    ring
  rw [h1, h2]
  ring

end Work.BzHard
