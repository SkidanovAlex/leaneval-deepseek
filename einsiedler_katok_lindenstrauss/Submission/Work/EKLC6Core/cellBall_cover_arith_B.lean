import Mathlib

namespace Work.EKLC6Core

theorem cellBall_cover_arith_B {P Q R : ℝ} (hP0 : 0 ≤ P) (hQ0 : 0 ≤ Q) (hR : 0 ≤ R)
    (hRh : R ≤ 1 / 2) (hPQ : P ≤ 16 * Q) (hQR : Q ≤ 16 * R) :
    10 * (P / 2 ^ 80) + 10 * (Q / 2 ^ 20) + 3 * (10 * (P / 2 ^ 80)) * (10 * (Q / 2 ^ 20))
      ≤ R / 4096 := by
  have hPQ0 : 0 ≤ P * Q := mul_nonneg hP0 hQ0
  nlinarith [hP0, hQ0, hR, hRh, hPQ, hQR, hPQ0]

end Work.EKLC6Core
