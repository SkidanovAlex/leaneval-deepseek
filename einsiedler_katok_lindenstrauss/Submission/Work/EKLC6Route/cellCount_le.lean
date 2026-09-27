import Mathlib
import Submission.Work.EKLC6Route.L7Aux

/-!
# `Work.EKLC6Route.cellCount_le`

The number of grid cells at level `i`,
`cellCount t i = (2 ^ (gridLev t i + 1) + 3) ^ 9`, grows at most like
`7^9 * exp (9 * betaExp t * i)`.

The proof rests on the single real-variable estimate
`2 ^ (gridLev t i + 1) ≤ 4 * exp (betaExp t * i)`, which follows from
`gridLev t i = ⌈betaExp t * i / log 2⌉₊ < betaExp t * i / log 2 + 1` and
`2 ^ (x / log 2) = exp x`; the additive `3` is absorbed because
`exp (betaExp t * i) ≥ 1`.
-/

namespace Work.EKLC6Route

theorem cellCount_le (t : Fin 3 → ℝ) (i : ℕ) :
    (Work.EKLC6Route.cellCount t i : ℝ) ≤
      (7 : ℝ) ^ 9 * Real.exp (9 * Work.EKLC6Route.betaExp t * (i : ℝ)) := by
  have hb0 : 0 ≤ betaExp t := by simp [betaExp]
  have hn0 : (0:ℝ) ≤ (i:ℝ) := Nat.cast_nonneg i
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hLlt : ((gridLev t i : ℕ) : ℝ) < betaExp t * (i:ℝ) / Real.log 2 + 1 := by
    have := Nat.ceil_lt_add_one (show (0:ℝ) ≤ betaExp t * (i:ℝ) / Real.log 2 from
      div_nonneg (mul_nonneg hb0 hn0) (le_of_lt hlog2))
    simpa [gridLev] using this
  have hLle : (((gridLev t i + 1 : ℕ)) : ℝ) ≤ betaExp t * (i:ℝ) / Real.log 2 + 2 := by
    have : ((gridLev t i : ℕ) : ℝ) + 1 ≤ betaExp t * (i:ℝ) / Real.log 2 + 2 := by linarith
    simpa using this
  have hpow : (2:ℝ) ^ (gridLev t i + 1) ≤ 4 * Real.exp (betaExp t * (i:ℝ)) := by
    have hmono : (2:ℝ) ^ (((gridLev t i + 1 : ℕ)) : ℝ) ≤
        (2:ℝ) ^ (betaExp t * (i:ℝ) / Real.log 2 + 2) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) hLle
    have hval : (2:ℝ) ^ (betaExp t * (i:ℝ) / Real.log 2 + 2) =
        4 * Real.exp (betaExp t * (i:ℝ)) := by
      rw [Real.rpow_add (by norm_num : (0:ℝ) < 2)]
      have h1 : (2:ℝ) ^ (betaExp t * (i:ℝ) / Real.log 2) =
          Real.exp (betaExp t * (i:ℝ)) := by
        rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 2), Real.exp_eq_exp]
        field_simp
      have h2 : (2:ℝ) ^ (2:ℝ) = 4 := by rw [Real.rpow_two]; norm_num
      rw [h1, h2]; ring
    rw [hval] at hmono
    rw [← Real.rpow_natCast 2 (gridLev t i + 1)]
    exact hmono
  have hmain : ((2 ^ (gridLev t i + 1) + 3 : ℕ) : ℝ) ≤
      7 * Real.exp (betaExp t * (i:ℝ)) := by
    have hcast : ((2 ^ (gridLev t i + 1) + 3 : ℕ) : ℝ) =
        (2:ℝ) ^ (gridLev t i + 1) + 3 := by
      push_cast; ring
    rw [hcast]
    have hone : 1 ≤ Real.exp (betaExp t * (i:ℝ)) := Real.one_le_exp (mul_nonneg hb0 hn0)
    linarith [hpow, hone]
  calc (cellCount t i : ℝ)
      = ((2 ^ (gridLev t i + 1) + 3 : ℕ) : ℝ) ^ 9 := by simp [cellCount, Nat.cast_pow]
    _ ≤ (7 * Real.exp (betaExp t * (i:ℝ))) ^ 9 := by
        apply pow_le_pow_left₀ (by positivity) hmain
    _ = (7:ℝ) ^ 9 * Real.exp (9 * betaExp t * (i:ℝ)) := by
        rw [mul_pow]
        congr 1
        rw [← Real.exp_nat_mul]
        congr 1
        push_cast
        ring

end Work.EKLC6Route
