import Mathlib

namespace Work.BzHard

theorem moebius_mul_cast_of_coprime {a b : ℕ} (h : Nat.Coprime a b) :
    (ArithmeticFunction.moebius (a * b) : ℝ) =
      (ArithmeticFunction.moebius a : ℝ) * (ArithmeticFunction.moebius b : ℝ) := by
  have hm := ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime h
  simp only [Int.cast_mul, hm]

end Work.BzHard
