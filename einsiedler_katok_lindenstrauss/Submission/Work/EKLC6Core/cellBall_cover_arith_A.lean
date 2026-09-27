import Mathlib

namespace Work.EKLC6Core

theorem cellBall_cover_arith_A {P Q R : ℝ} (hR : 0 ≤ R) (hRh : R ≤ 1 / 2) (hPQ : P ≤ 16 * Q)
    (hQR : Q ≤ 2 ^ 19 * R) :
    10 * (P / 2 ^ 80) + R / 2 ^ 20 + 3 * (10 * (P / 2 ^ 80)) * (R / 2 ^ 20) ≤ R / 4096 := by
  -- P is bounded above by 2^23 * R since 16 * (2^19 * R) = 2^23 * R.
  have hP : P ≤ 2 ^ 23 * R := by nlinarith [hPQ, hQR]
  -- R ≤ 1/2 with R ≥ 0 gives R^2 ≤ R/2.
  have hsq : R ^ 2 ≤ R / 2 := by nlinarith [hR, hRh]
  nlinarith [hR, hRh, hP, hsq]

end Work.EKLC6Core
