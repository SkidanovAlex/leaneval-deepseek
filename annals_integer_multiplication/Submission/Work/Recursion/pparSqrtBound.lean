import Mathlib
import Submission.Work.Recursion.defs

namespace Work.Recursion

/-- Paper §5.1: `√(6b) + 1 ≤ 4√b`. -/
theorem pparSqrtBound (n : ℕ) (hn : 2 ≤ n) :
    (Nat.sqrt (HvdH.ppar n) : ℝ) + 1 ≤ 4 * Real.sqrt (HvdH.bpar n : ℝ) := by
  -- `b = ⌈log₂ n⌉ ≥ 1` for `n ≥ 2`.
  have hb : 1 ≤ HvdH.bpar n := by
    have : 0 < HvdH.bpar n := Nat.clog_pos (by norm_num) (by omega)
    omega
  -- `ppar n = 6 * bpar n`.
  have hcast : (HvdH.ppar n : ℝ) = 6 * (HvdH.bpar n : ℝ) := by
    simp [HvdH.ppar, Nat.cast_mul]
  -- The floor `Nat.sqrt` is bounded by the real square root.
  have hstep1 : (Nat.sqrt (HvdH.ppar n) : ℝ) ≤ Real.sqrt (6 * (HvdH.bpar n : ℝ)) := by
    have := Real.nat_sqrt_le_real_sqrt (a := HvdH.ppar n)
    rwa [hcast] at this
  have hbR : (1 : ℝ) ≤ (HvdH.bpar n : ℝ) := by exact_mod_cast hb
  have hr1 : 1 ≤ Real.sqrt (HvdH.bpar n : ℝ) := Real.one_le_sqrt.2 hbR
  have hsqrt6lt : Real.sqrt 6 < 3 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have hsqrt6nonneg : 0 ≤ Real.sqrt 6 := Real.sqrt_nonneg 6
  have hmul : Real.sqrt (6 * (HvdH.bpar n : ℝ))
      = Real.sqrt 6 * Real.sqrt (HvdH.bpar n : ℝ) :=
    Real.sqrt_mul (by norm_num) _
  -- `√6 * √b + 1 ≤ 4 * √b` since `√b ≥ 1` and `√6 < 3`.
  have hkey : Real.sqrt 6 * Real.sqrt (HvdH.bpar n : ℝ) + 1
      ≤ 4 * Real.sqrt (HvdH.bpar n : ℝ) := by
    nlinarith [hr1, hsqrt6lt, hsqrt6nonneg, Real.sqrt_nonneg (HvdH.bpar n : ℝ)]
  calc (Nat.sqrt (HvdH.ppar n) : ℝ) + 1
      ≤ Real.sqrt (6 * (HvdH.bpar n : ℝ)) + 1 := by linarith
    _ = Real.sqrt 6 * Real.sqrt (HvdH.bpar n : ℝ) + 1 := by rw [hmul]
    _ ≤ 4 * Real.sqrt (HvdH.bpar n : ℝ) := hkey

end Work.Recursion
