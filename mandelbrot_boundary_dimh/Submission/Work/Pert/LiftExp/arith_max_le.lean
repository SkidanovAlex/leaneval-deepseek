import Mathlib

namespace Work.Pert.LiftExp

/-- Purely arithmetic cleaning-up step: for `rr > 0` and `0 < S ≤ 2`, the maximum of the two
constants appearing in the gates `16 * (8 / rr + 4)` and
`1 / (32 * min (rr / 4) (min (1 / 8) (1 / (16 * S * (8 / rr + 4)))))` is at most
`2 ^ 12 * (1 + 1 / rr)`.

The key point is the lower bound `c := rr / (131072 * (1 + rr))` for the minimum: each of the three
terms inside the `min` dominates `c`, and `1 / (32 * c) = 2 ^ 12 * (1 + 1 / rr)`. -/
theorem arith_max_le {rr S : ℝ} (hrr : 0 < rr) (hSp : 0 < S) (hS : S ≤ 2) :
    max (16 * (8 / rr + 4))
        (1 / (32 * min (rr / 4) (min (1 / 8) (1 / (16 * S * (8 / rr + 4))))))
      ≤ 2 ^ 12 * (1 + 1 / rr) := by
  set c : ℝ := rr / (131072 * (1 + rr)) with hc
  have hden : 0 < 131072 * (1 + rr) := by positivity
  have hcpos : 0 < c := by rw [hc]; positivity
  -- the three arguments of the inner `min` all dominate `c`
  have hc1 : c ≤ rr / 4 := by
    rw [hc]
    apply div_le_div_of_nonneg_left hrr.le (by norm_num)
    nlinarith
  have hc2 : c ≤ 1 / 8 := by
    rw [hc, div_le_iff₀ hden]
    nlinarith
  have hc3 : c ≤ 1 / (16 * S * (8 / rr + 4)) := by
    have hE : 0 < 16 * S * (8 / rr + 4) := by positivity
    rw [hc, div_le_iff₀ hden]
    rw [show (1 / (16 * S * (8 / rr + 4))) * (131072 * (1 + rr))
        = (131072 * (1 + rr)) / (16 * S * (8 / rr + 4)) by ring]
    rw [le_div_iff₀ hE]
    have heq : rr * (16 * S * (8 / rr + 4)) = 16 * S * (8 + 4 * rr) := by
      field_simp
    rw [heq]
    nlinarith [hrr, hSp, hS]
  have hmin : c ≤ min (rr / 4) (min (1 / 8) (1 / (16 * S * (8 / rr + 4)))) :=
    le_min hc1 (le_min hc2 hc3)
  have h32 : 32 * c ≤ 32 * min (rr / 4) (min (1 / 8) (1 / (16 * S * (8 / rr + 4)))) := by
    linarith
  have h32c : 0 < 32 * c := by positivity
  -- the second argument of the outer `max`
  have hB : 1 / (32 * min (rr / 4) (min (1 / 8) (1 / (16 * S * (8 / rr + 4)))))
      ≤ 2 ^ 12 * (1 + 1 / rr) := by
    calc 1 / (32 * min (rr / 4) (min (1 / 8) (1 / (16 * S * (8 / rr + 4)))))
        ≤ 1 / (32 * c) := one_div_le_one_div_of_le h32c h32
      _ = 2 ^ 12 * (1 + 1 / rr) := by
          rw [hc]; field_simp; ring
  -- the first argument of the outer `max`
  have hA : 16 * (8 / rr + 4) ≤ 2 ^ 12 * (1 + 1 / rr) := by
    have h1 : (16:ℝ) * (8 / rr + 4) = 128 / rr + 64 := by ring
    have h2 : (2:ℝ) ^ 12 * (1 + 1 / rr) = 4096 + 4096 / rr := by ring
    rw [h1, h2]
    have e1 : (128:ℝ) / rr = 128 * (1 / rr) := by ring
    have e2 : (4096:ℝ) / rr = 4096 * (1 / rr) := by ring
    rw [e1, e2]
    nlinarith [show (0:ℝ) < 1 / rr by positivity]
  exact max_le hA hB

end Work.Pert.LiftExp
