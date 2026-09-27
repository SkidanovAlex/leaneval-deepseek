import Mathlib

namespace Work.EKLC6Core

theorem cellBall_cover_arith_sel {P Q : ℝ} (hQ : 0 ≤ Q) (hPQ : P ≤ 16 * Q) :
    10 * (P / 2 ^ 80) ≤ Q / 4096 := by
  nlinarith [hQ, hPQ]

end Work.EKLC6Core
