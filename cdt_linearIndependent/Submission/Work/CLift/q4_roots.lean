import Mathlib
import Submission.Work.CLift.bridge

/-!
# Area CLift — the roots of the quartic `Q₄`

The order-4 operator of Theorem C has polynomial coefficient
`P₂ = (x−1)x(x+1)Q₄` with
`Q₄(x) = x⁴ − 4ab x³ + (4a² + 4b² − 2)x² − 4ab x + 1`, `a = 2m+1`, `b = 2n+1`.

`Q₄` is reciprocal (`Q₄(x) = x⁴ Q₄(1/x)`), so it splits over `ℝ` as
`Q₄(x) = (x² − 2(ab + st)x + 1)(x² − 2(ab − st)x + 1)`, where `s = √(a²−1)`,
`t = √(b²−1)`.  Since `(a+s)(b+t) · (a−s)(b−t) = (a²−s²)(b²−t²) = 1` and likewise for the
mixed products, the four roots are exactly
`x_{±±} = (a ± s)(b ± t)`, i.e. `xRoot m n (±1) (±1)`.

This module proves that statement: every complex root of `Q₄` is one of the four real numbers
`xRoot m n 1 1`, `xRoot m n 1 (-1)`, `xRoot m n (-1) 1`, `xRoot m n (-1) (-1)`.
-/

namespace Work.CLift

open Submission.CDTPlan

noncomputable section

/-- The complex cast of `xRoot`, written with the two inner factors separated. -/
lemma xRoot_cast (m n : ℕ) (sa sb : ℝ) :
    ((xRoot m n sa sb : ℝ) : ℂ)
      = (((2 * m + 1 : ℕ) : ℂ)
          + (sa : ℂ) * ((Real.sqrt ((2 * (m : ℝ) + 1) ^ 2 - 1) : ℝ) : ℂ))
        * (((2 * n + 1 : ℕ) : ℂ)
          + (sb : ℂ) * ((Real.sqrt ((2 * (n : ℝ) + 1) ^ 2 - 1) : ℝ) : ℂ)) := by
  rw [xRoot]
  push_cast
  ring

/-- `(2m+1)² − 1 ≥ 0`, so that `√((2m+1)² − 1)` squares back. -/
lemma sq_arg_nonneg (m : ℕ) : (0 : ℝ) ≤ (2 * (m : ℝ) + 1) ^ 2 - 1 := by
  have h : (0 : ℝ) ≤ (m : ℝ) := by exact_mod_cast Nat.zero_le m
  nlinarith [sq_nonneg ((m : ℝ))]

theorem q4_roots (m n : ℕ) (x : ℂ)
    (hx : x ^ 4 - 4 * ((2 * m + 1 : ℕ) : ℂ) * ((2 * n + 1 : ℕ) : ℂ) * x ^ 3
        + (4 * ((2 * m + 1 : ℕ) : ℂ) ^ 2 + 4 * ((2 * n + 1 : ℕ) : ℂ) ^ 2 - 2) * x ^ 2
        - 4 * ((2 * m + 1 : ℕ) : ℂ) * ((2 * n + 1 : ℕ) : ℂ) * x + 1 = 0) :
    x = (xRoot m n 1 1 : ℂ) ∨ x = (xRoot m n 1 (-1) : ℂ) ∨
      x = (xRoot m n (-1) 1 : ℂ) ∨ x = (xRoot m n (-1) (-1) : ℂ) := by
  set a : ℂ := ((2 * m + 1 : ℕ) : ℂ) with ha
  set b : ℂ := ((2 * n + 1 : ℕ) : ℂ) with hb
  set s : ℂ := ((Real.sqrt ((2 * (m : ℝ) + 1) ^ 2 - 1) : ℝ) : ℂ) with hsdef
  set t : ℂ := ((Real.sqrt ((2 * (n : ℝ) + 1) ^ 2 - 1) : ℝ) : ℂ) with htdef
  have hx' : x ^ 4 - 4 * a * b * x ^ 3 + (4 * a ^ 2 + 4 * b ^ 2 - 2) * x ^ 2
        - 4 * a * b * x + 1 = 0 := hx
  have hs2 : s ^ 2 = a ^ 2 - 1 := by
    rw [hsdef, ha, ← Complex.ofReal_pow, Real.sq_sqrt (sq_arg_nonneg m)]
    push_cast
    ring
  have ht2 : t ^ 2 = b ^ 2 - 1 := by
    rw [htdef, hb, ← Complex.ofReal_pow, Real.sq_sqrt (sq_arg_nonneg n)]
    push_cast
    ring
  have hst : (s * t) ^ 2 = (a ^ 2 - 1) * (b ^ 2 - 1) := by rw [mul_pow, hs2, ht2]
  -- the reciprocal factorisation of `Q₄` into two quadratics with constant term `1`
  have hQgen : x ^ 4 - 4 * a * b * x ^ 3 + (4 * a ^ 2 + 4 * b ^ 2 - 2) * x ^ 2
      - 4 * a * b * x + 1
      = (x ^ 2 - 2 * (a * b + s * t) * x + 1) * (x ^ 2 - 2 * (a * b - s * t) * x + 1) := by
    have h1 : (x ^ 2 - 2 * (a * b + s * t) * x + 1) * (x ^ 2 - 2 * (a * b - s * t) * x + 1)
        = x ^ 4 - 4 * a * b * x ^ 3 + (2 + 4 * a ^ 2 * b ^ 2 - 4 * (s * t) ^ 2) * x ^ 2
          - 4 * a * b * x + 1 := by ring
    rw [h1, hst]
    ring
  have hQ : (x ^ 2 - 2 * (a * b + s * t) * x + 1) * (x ^ 2 - 2 * (a * b - s * t) * x + 1) = 0 := by
    rw [← hQgen]; exact hx'
  -- each quadratic is the product of the two linear factors `(x − x_{±±})`
  have hfac1 : (x - (a + s) * (b + t)) * (x - (a - s) * (b - t))
      = x ^ 2 - 2 * (a * b + s * t) * x + 1 := by
    have hs1 : a ^ 2 - s ^ 2 = 1 := by rw [hs2]; ring
    have ht1 : b ^ 2 - t ^ 2 = 1 := by rw [ht2]; ring
    have hsum : (a + s) * (b + t) + (a - s) * (b - t) = 2 * (a * b + s * t) := by ring
    have hprod : (a + s) * (b + t) * ((a - s) * (b - t)) = 1 := by
      calc (a + s) * (b + t) * ((a - s) * (b - t)) = (a ^ 2 - s ^ 2) * (b ^ 2 - t ^ 2) := by ring
        _ = 1 := by rw [hs1, ht1]; ring
    have hexp : (x - (a + s) * (b + t)) * (x - (a - s) * (b - t))
        = x ^ 2 - ((a + s) * (b + t) + (a - s) * (b - t)) * x
          + (a + s) * (b + t) * ((a - s) * (b - t)) := by ring
    rw [hexp, hsum, hprod]
  have hfac2 : (x - (a + s) * (b - t)) * (x - (a - s) * (b + t))
      = x ^ 2 - 2 * (a * b - s * t) * x + 1 := by
    have hs1 : a ^ 2 - s ^ 2 = 1 := by rw [hs2]; ring
    have ht1 : b ^ 2 - t ^ 2 = 1 := by rw [ht2]; ring
    have hsum : (a + s) * (b - t) + (a - s) * (b + t) = 2 * (a * b - s * t) := by ring
    have hprod : (a + s) * (b - t) * ((a - s) * (b + t)) = 1 := by
      calc (a + s) * (b - t) * ((a - s) * (b + t)) = (a ^ 2 - s ^ 2) * (b ^ 2 - t ^ 2) := by ring
        _ = 1 := by rw [hs1, ht1]; ring
    have hexp : (x - (a + s) * (b - t)) * (x - (a - s) * (b + t))
        = x ^ 2 - ((a + s) * (b - t) + (a - s) * (b + t)) * x
          + (a + s) * (b - t) * ((a - s) * (b + t)) := by ring
    rw [hexp, hsum, hprod]
  -- identification of the four roots with the blueprint's `xRoot`
  have hroot1 : (a + s) * (b + t) = (xRoot m n 1 1 : ℂ) := by
    rw [xRoot_cast m n 1 1, ha, hb, hsdef, htdef]; push_cast; ring
  have hroot2 : (a + s) * (b - t) = (xRoot m n 1 (-1) : ℂ) := by
    rw [xRoot_cast m n 1 (-1), ha, hb, hsdef, htdef]; push_cast; ring
  have hroot3 : (a - s) * (b + t) = (xRoot m n (-1) 1 : ℂ) := by
    rw [xRoot_cast m n (-1) 1, ha, hb, hsdef, htdef]; push_cast; ring
  have hroot4 : (a - s) * (b - t) = (xRoot m n (-1) (-1) : ℂ) := by
    rw [xRoot_cast m n (-1) (-1), ha, hb, hsdef, htdef]; push_cast; ring
  rcases mul_eq_zero.mp hQ with h | h
  · rw [← hfac1] at h
    rcases mul_eq_zero.mp h with h1 | h1
    · left; rw [sub_eq_zero.mp h1, hroot1]
    · right; right; right; rw [sub_eq_zero.mp h1, hroot4]
  · rw [← hfac2] at h
    rcases mul_eq_zero.mp h with h1 | h1
    · right; left; rw [sub_eq_zero.mp h1, hroot2]
    · right; right; left; rw [sub_eq_zero.mp h1, hroot3]

end

end Work.CLift
