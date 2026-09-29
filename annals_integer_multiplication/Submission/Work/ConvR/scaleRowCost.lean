import Mathlib
import Submission.Work.ConvR.scaleFacts

set_option autoImplicit false

namespace Work.ConvR

open HvdH

/-- Cost bookkeeping for one row of the pointwise array scaling of `Work.ConvR.scaleArr`:
the per-row work `6 * Kp * (4 * p + 14) + Ks * (p + 1) ^ 2 + Km * (cfxSz p + 1)` charged `r` times,
plus one final `Km` term, fits into `(84 * Kp + Ks + 10 * Km) * ((r + 1) * (p + 1) ^ 2 + 1)`.

For `cfxSz p = 2 * p + 8` the only nontrivial inputs are the quadratic estimates
`24 * p + 84 ≤ 84 * (p + 1) ^ 2` (linear cost dominated by the square) and
`2 * p + 9 ≤ 10 * (p + 1) ^ 2` (the `2 * p + 1`-bit integers of a coefficient dominated by
`10 * (p + 1) ^ 2`). -/
theorem scaleRowCost (Kp Km Ks r p : ℕ) :
    r * (6 * Kp * (4 * p + 14) + Ks * (p + 1) ^ 2 + Km * (Work.ConvR.cfxSz p + 1)) + Km ≤
      (84 * Kp + Ks + 10 * Km) * (r + 1) * (p + 1) ^ 2 + (84 * Kp + Ks + 10 * Km) := by
  have hcfx : cfxSz p = 2 * p + 8 := rfl
  rw [hcfx]
  have hp : 24 * p + 84 ≤ 84 * (p + 1) ^ 2 := by nlinarith [Nat.zero_le p]
  have hq : 2 * p + 9 ≤ 10 * (p + 1) ^ 2 := by nlinarith [Nat.zero_le p]
  have hB : (84 * Kp + Ks + 10 * Km) * (r + 1) * (p + 1) ^ 2 + (84 * Kp + Ks + 10 * Km)
      = (84 * Kp + Ks + 10 * Km) * ((r + 1) * (p + 1) ^ 2 + 1) := by ring
  rw [hB]
  have t1 : r * (6 * Kp * (4 * p + 14)) ≤ 84 * Kp * ((r + 1) * (p + 1) ^ 2 + 1) := by
    have hA : r * (24 * p + 84) ≤ 84 * ((r + 1) * (p + 1) ^ 2 + 1) := by
      calc r * (24 * p + 84)
          ≤ r * (84 * (p + 1) ^ 2) := Nat.mul_le_mul_left r hp
        _ = 84 * (r * (p + 1) ^ 2) := by ring
        _ ≤ 84 * ((r + 1) * (p + 1) ^ 2) :=
              Nat.mul_le_mul_left 84 (Nat.mul_le_mul_right ((p + 1) ^ 2) (Nat.le_succ r))
        _ ≤ 84 * ((r + 1) * (p + 1) ^ 2 + 1) :=
              Nat.mul_le_mul_left 84 (Nat.le_succ _)
    calc r * (6 * Kp * (4 * p + 14)) = Kp * (r * (24 * p + 84)) := by ring
      _ ≤ Kp * (84 * ((r + 1) * (p + 1) ^ 2 + 1)) := Nat.mul_le_mul_left Kp hA
      _ = 84 * Kp * ((r + 1) * (p + 1) ^ 2 + 1) := by ring
  have t2 : r * (Ks * (p + 1) ^ 2) ≤ Ks * ((r + 1) * (p + 1) ^ 2 + 1) := by
    have h : r * (p + 1) ^ 2 ≤ (r + 1) * (p + 1) ^ 2 + 1 :=
      le_trans (Nat.mul_le_mul_right ((p + 1) ^ 2) (Nat.le_succ r)) (Nat.le_succ _)
    calc r * (Ks * (p + 1) ^ 2) = Ks * (r * (p + 1) ^ 2) := by ring
      _ ≤ Ks * ((r + 1) * (p + 1) ^ 2 + 1) := Nat.mul_le_mul_left Ks h
  have t3 : r * (Km * (2 * p + 8 + 1)) + Km ≤ 10 * Km * ((r + 1) * (p + 1) ^ 2 + 1) := by
    have hx : r * (2 * p + 9) ≤ 10 * ((r + 1) * (p + 1) ^ 2) := by
      calc r * (2 * p + 9) ≤ r * (10 * (p + 1) ^ 2) := Nat.mul_le_mul_left r hq
        _ = 10 * (r * (p + 1) ^ 2) := by ring
        _ ≤ 10 * ((r + 1) * (p + 1) ^ 2) :=
              Nat.mul_le_mul_left 10 (Nat.mul_le_mul_right ((p + 1) ^ 2) (Nat.le_succ r))
    have hy : r * (2 * p + 9) + 1 ≤ 10 * ((r + 1) * (p + 1) ^ 2 + 1) := by nlinarith [hx]
    calc r * (Km * (2 * p + 8 + 1)) + Km = Km * (r * (2 * p + 9) + 1) := by ring
      _ ≤ Km * (10 * ((r + 1) * (p + 1) ^ 2 + 1)) := Nat.mul_le_mul_left Km hy
      _ = 10 * Km * ((r + 1) * (p + 1) ^ 2 + 1) := by ring
  calc r * (6 * Kp * (4 * p + 14) + Ks * (p + 1) ^ 2 + Km * (2 * p + 8 + 1)) + Km
      = r * (6 * Kp * (4 * p + 14)) + r * (Ks * (p + 1) ^ 2) + (r * (Km * (2 * p + 8 + 1)) + Km) := by
        ring
    _ ≤ 84 * Kp * ((r + 1) * (p + 1) ^ 2 + 1) + Ks * ((r + 1) * (p + 1) ^ 2 + 1)
          + 10 * Km * ((r + 1) * (p + 1) ^ 2 + 1) := add_le_add (add_le_add t1 t2) t3
    _ = (84 * Kp + Ks + 10 * Km) * ((r + 1) * (p + 1) ^ 2 + 1) := by ring

end Work.ConvR
