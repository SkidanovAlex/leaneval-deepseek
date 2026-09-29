import Mathlib
import Submission.Work.Fx.piDefs
import Submission.Work.Fx.piIter

/-!
# `Work.Fx.piDvalBound`

The final square-root step of the fixed-point computation of `π` (paper §2.8):
with `q = qq p`, `S = 2^(2q)`, `a = aval p p` and `Dval p = ⌊√(2S - a)⌋`, the
quotient `Dval p / 2^q` differs from `√(2 - a/S)` by at most `2^{-q}`.

Indeed `√(2 - a/S) = √(2S - a)/2^q` and `Nat.sqrt (2S-a) ≤ √(2S-a) < Nat.sqrt (2S-a) + 1`.
-/

set_option autoImplicit false

namespace Work.Fx

open HvdH

/-- The integer square root agrees with the real one up to the denominator. -/
theorem piDvalBound (p : ℕ) (ha0 : 0 ≤ Work.Fx.aval p p) (haC : Work.Fx.aval p p ≤ Work.Fx.C0c p) :
    |(Work.Fx.Dval p : ℝ) / (2 : ℝ) ^ Work.Fx.qq p
        - Real.sqrt (2 - (Work.Fx.aval p p : ℝ) / (2 : ℝ) ^ (2 * Work.Fx.qq p))|
      ≤ 1 / (2 : ℝ) ^ Work.Fx.qq p := by
  set r : ℝ := (2 : ℝ) ^ qq p with hrdef
  have hrpos : 0 < r := by rw [hrdef]; positivity
  have hrne : r ≠ 0 := ne_of_gt hrpos
  set ns : ℕ := (C0c p - aval p p).toNat with hnsdef
  -- `ns` is the nonnegative integer `2S - a`
  have hnsZ : (ns : ℤ) = C0c p - aval p p := by
    rw [hnsdef]
    exact Int.toNat_of_nonneg (by omega)
  -- `S = 2^(2q) = r^2`
  have h2q : ((2 : ℝ) ^ qq p) ^ 2 = (2 : ℝ) ^ (2 * qq p) := by
    rw [← pow_mul]; congr 1; ring
  have hC : ((C0c p : ℤ) : ℝ) = 2 * r ^ 2 := by
    rw [C0c, hrdef]
    push_cast
    rw [pow_succ, h2q]
    ring
  have hnsR : (ns : ℝ) = 2 * r ^ 2 - (aval p p : ℝ) := by
    have h1 : (ns : ℝ) = ((C0c p : ℤ) : ℝ) - (aval p p : ℝ) := by
      rw [← Int.cast_natCast, hnsZ]
      push_cast
      ring
    rw [h1, hC]
  -- the real square root equals `√ns / r`
  have harg : 2 - (aval p p : ℝ) / (2 : ℝ) ^ (2 * qq p) = (ns : ℝ) / r ^ 2 := by
    rw [← h2q, hnsR]
    field_simp
    ring
  have hsqrt : Real.sqrt (2 - (aval p p : ℝ) / (2 : ℝ) ^ (2 * qq p))
      = Real.sqrt (ns : ℝ) / r := by
    rw [harg, Real.sqrt_div (by positivity : (0 : ℝ) ≤ (ns : ℝ)) (r ^ 2),
      Real.sqrt_sq (le_of_lt hrpos)]
  have hDval : (Dval p : ℝ) = (ns.sqrt : ℝ) := by
    rw [Dval, ← hnsdef]
    push_cast
    ring
  rw [hDval, hsqrt, ← sub_div, abs_div, abs_of_pos hrpos,
    div_le_iff₀ hrpos, one_div, inv_mul_cancel₀ hrne]
  exact natSqrt_abs_sub_le_one ns

end Work.Fx
