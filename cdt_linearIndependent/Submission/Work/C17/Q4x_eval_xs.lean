import Mathlib
import Submission.Work.C17.seventeen_defs

namespace Work.C17

open Polynomial

/-!
# The cusp `x_s` is a root of the quartic `Q₄`

`Q₄(X) = 1 − 4abX + (4a²+4b²−2)X² − 4abX³ + X⁴` is the palindromic quartic attached to the
order-2 operator `M` of the unlikely series; its four roots are the four products
`(a ± √(a²−1))·(b ± √(b²−1))`, and `x_s = (a+√(a²−1))·(b−√(b²−1))` is one of them.

The proof is elementary and division-free.  Write `s = √(a²−1)`, `t = √(b²−1)` (so `s² = a²−1`,
`t² = b²−1`) and `x = (a+s)(b−t)`.  Then `(a+s)(a−s) = 1` and `(b+t)(b−t) = 1`, so
`x·((a−s)(b+t)) = 1` and hence
`x² + 1 = x·((a+s)(b−t) + (a−s)(b+t)) = (2ab − 2st)·x`.
Writing `Q₄(X) = (X²+1)² − 4abX(X²+1) + (4a²+4b²−4)X²` and substituting `x²+1 = u x`, where
`u = 2ab − 2st`, gives `Q₄(x) = x²·(u² − 4abu + 4a²+4b²−4)`; the last factor is
`−4a²b² + 4s²t² + 4a²+4b²−4 = −4a²b² + 4(a²−1)(b²−1) + 4a²+4b²−4 = 0`. -/

theorem Q4x_eval_xs (a b : ℚ) (ha : 3 ≤ a) (hb : 3 ≤ b) (hab : a < b) :
    (Q4x a b).eval₂ (algebraMap ℚ ℂ) (((xs a b : ℝ)) : ℂ) = 0 := by
  have ha1 : (0 : ℝ) ≤ (a : ℝ) ^ 2 - 1 := by
    have : (3 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
    nlinarith
  have hb1 : (0 : ℝ) ≤ (b : ℝ) ^ 2 - 1 := by
    have : (3 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
    nlinarith
  have hs2R : Real.sqrt ((a : ℝ) ^ 2 - 1) ^ 2 = (a : ℝ) ^ 2 - 1 := Real.sq_sqrt ha1
  have ht2R : Real.sqrt ((b : ℝ) ^ 2 - 1) ^ 2 = (b : ℝ) ^ 2 - 1 := Real.sq_sqrt hb1
  set s : ℂ := ((Real.sqrt ((a : ℝ) ^ 2 - 1) : ℝ) : ℂ) with hs
  set t : ℂ := ((Real.sqrt ((b : ℝ) ^ 2 - 1) : ℝ) : ℂ) with ht
  set x : ℂ := ((xs a b : ℝ) : ℂ) with hx
  have hs2 : s ^ 2 = (a : ℂ) ^ 2 - 1 := by
    rw [hs, ← Complex.ofReal_pow, hs2R]; push_cast; ring
  have ht2 : t ^ 2 = (b : ℂ) ^ 2 - 1 := by
    rw [ht, ← Complex.ofReal_pow, ht2R]; push_cast; ring
  have hxs : x = ((a : ℂ) + s) * ((b : ℂ) - t) := by
    rw [hx, hs, ht, xs]; push_cast; ring
  have h1 : ((a : ℂ) + s) * ((a : ℂ) - s) = 1 := by
    ring_nf
    rw [hs2]
    ring
  have h2 : ((b : ℂ) + t) * ((b : ℂ) - t) = 1 := by
    ring_nf
    rw [ht2]
    ring
  have hxinv : x * (((a : ℂ) - s) * ((b : ℂ) + t)) = 1 := by
    rw [hxs]
    rw [show ((↑a + s) * (↑b - t)) * ((↑a - s) * (↑b + t))
          = ((↑a + s) * (↑a - s)) * ((↑b + t) * (↑b - t)) from by ring, h1, h2, mul_one]
  have hx1 : x ^ 2 + 1 = (2 * (a : ℂ) * (b : ℂ) - 2 * s * t) * x := by
    calc x ^ 2 + 1 = x * x + 1 := by ring
      _ = x * ((↑a + s) * (↑b - t)) + x * ((↑a - s) * (↑b + t)) := by rw [← hxs, ← hxinv]
      _ = x * (((↑a + s) * (↑b - t)) + ((↑a - s) * (↑b + t))) := by ring
      _ = x * (2 * ↑a * ↑b - 2 * s * t) := by ring
      _ = (2 * ↑a * ↑b - 2 * s * t) * x := by ring
  have hu : (2 * (a : ℂ) * (b : ℂ) - 2 * s * t) ^ 2
        - 4 * (a : ℂ) * (b : ℂ) * (2 * (a : ℂ) * (b : ℂ) - 2 * s * t)
        + (4 * (a : ℂ) ^ 2 + 4 * (b : ℂ) ^ 2 - 4) = 0 := by
    have hst : s ^ 2 * t ^ 2 = ((a : ℂ) ^ 2 - 1) * ((b : ℂ) ^ 2 - 1) := by rw [hs2, ht2]
    ring_nf
    rw [hst]
    ring
  simp only [Q4x, Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul,
    Polynomial.eval₂_pow, Polynomial.eval₂_one, Polynomial.eval₂_X, Polynomial.eval₂_C]
  have hc1 : (algebraMap ℚ ℂ) (4 * a * b) = 4 * (a : ℂ) * (b : ℂ) := by norm_num
  have hc2 : (algebraMap ℚ ℂ) (4 * a ^ 2 + 4 * b ^ 2 - 2)
      = 4 * (a : ℂ) ^ 2 + 4 * (b : ℂ) ^ 2 - 2 := by norm_num
  rw [hc1, hc2]
  have hQ : (1 - 4 * (a : ℂ) * (b : ℂ) * x + (4 * (a : ℂ) ^ 2 + 4 * (b : ℂ) ^ 2 - 2) * x ^ 2
        - 4 * (a : ℂ) * (b : ℂ) * x ^ 3 + x ^ 4 : ℂ)
      = (x ^ 2 + 1) ^ 2 - 4 * (a : ℂ) * (b : ℂ) * x * (x ^ 2 + 1)
        + (4 * (a : ℂ) ^ 2 + 4 * (b : ℂ) ^ 2 - 4) * x ^ 2 := by ring
  rw [hQ, hx1]
  rw [show ((2 * (a : ℂ) * (b : ℂ) - 2 * s * t) * x) ^ 2
          - 4 * (a : ℂ) * (b : ℂ) * x * ((2 * (a : ℂ) * (b : ℂ) - 2 * s * t) * x)
          + (4 * (a : ℂ) ^ 2 + 4 * (b : ℂ) ^ 2 - 4) * x ^ 2
        = x ^ 2 * ((2 * (a : ℂ) * (b : ℂ) - 2 * s * t) ^ 2
            - 4 * (a : ℂ) * (b : ℂ) * (2 * (a : ℂ) * (b : ℂ) - 2 * s * t)
            + (4 * (a : ℂ) ^ 2 + 4 * (b : ℂ) ^ 2 - 4)) from by ring,
    hu, mul_zero]

end Work.C17
