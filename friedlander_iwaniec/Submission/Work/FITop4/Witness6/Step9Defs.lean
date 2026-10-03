/-
# `Submission.Work.FITop4.Witness6.Step9Defs` — the `C⁴` clamped step of the round-6 majorant

The round-6 majorant `IsMajorant6` (`Work.FITop4.Defs6`) asks for a *real* function `F` that is
`C⁴` with compact support, restricts to a round-3 `IsMajorant` sequence at the integers, and obeys
`|F^{(j)}| ≤ C M^{-j}` for `j ≤ 4`.  The round-3 witness `Work.FITop3.majorant` is built from
`sm` (a clamped *quadratic*, only `C¹`), so it cannot be used as `F`; this file fixes the smooth
step that replaces it.

The step is the **clamped nonic** Hermite step

  `step9 t = 0` for `t ≤ 0`, `= 1` for `1 ≤ t`, `= p9 t` on `[0,1]`,
  `p9 t = 126t⁵ − 420t⁶ + 540t⁷ − 315t⁸ + 70t⁹ = 630∫₀ᵗ s⁴(1−s)⁴ ds`,

whose first four derivatives vanish at `0` and at `1` (`p9` has a five-fold zero at `0` and
`p9 − 1` has a five-fold zero at `1`), so the clamped function is `C⁴`.  Its derivatives are the
clamped polynomials `p8 = p9' = 630t⁴(1−t)⁴`, `p7 = p9'' = 2520t³(1−t)³(1−2t)`, `p6 = p9'''`,
`p5 = p9''''`, with the small explicit bounds

  `|p8| ≤ 630/256 < 5/2`,  `|p7| ≤ 20.17 < 25`

on `[0,1]` (`p8` is maximised at `t = 1/2`, `p7` at `t(1−t) = 3/14`).

The annulus majorant of the witness is the product of the two rescaled steps

  `G t = step9 ((t − 1/4)/(3/4)) · step9 ((4 − t)/2)`,

which is `0` off `[1/4,4]`, `1` on `[1,2]`, and has `|G'| ≤ (5/2)(4/3 + 1/2) = 55/12` and
`|G''| ≤ 25·(16/9) + 2·(5/2)²·(2/3) + 25·(1/4) = 2125/36 < 64`; scaling it by `M` gives the
witness `FM M x = G (x/M)`, whose unit differences at the integers are at most `8/M` and whose
second differences are at most `64/M²` — exactly the round-3 `IsMajorant` constants.

This module contains definitions only (no theorem, no `sorry`, no `axiom`), so that the analytic
facts about `step9` can be delegated to a colleague who imports just this file.
-/
import Mathlib

set_option autoImplicit false

namespace Work.FITop4.Witness6

noncomputable section

/-- `p9 t = 126t⁵ − 420t⁶ + 540t⁷ − 315t⁸ + 70t⁹`, the middle branch of `step9`; it is
`630∫₀ᵗ s⁴(1−s)⁴ ds`, hence has a five-fold zero at `0` and `p9 − 1` has a five-fold zero at
`1`. -/
def p9 (t : ℝ) : ℝ := 126 * t ^ 5 - 420 * t ^ 6 + 540 * t ^ 7 - 315 * t ^ 8 + 70 * t ^ 9

/-- `p8 = p9' = 630t⁴(1−t)⁴`. -/
def p8 (t : ℝ) : ℝ := 630 * t ^ 4 - 2520 * t ^ 5 + 3780 * t ^ 6 - 2520 * t ^ 7 + 630 * t ^ 8

/-- `p7 = p9'' = 2520t³(1−t)³(1−2t)`. -/
def p7 (t : ℝ) : ℝ := 2520 * t ^ 3 - 12600 * t ^ 4 + 22680 * t ^ 5 - 17640 * t ^ 6 + 5040 * t ^ 7

/-- `p6 = p9'''`. -/
def p6 (t : ℝ) : ℝ := 7560 * t ^ 2 - 50400 * t ^ 3 + 113400 * t ^ 4 - 105840 * t ^ 5
  + 35280 * t ^ 6

/-- `p5 = p9''''`. -/
def p5 (t : ℝ) : ℝ := 15120 * t - 151200 * t ^ 2 + 453600 * t ^ 3 - 529200 * t ^ 4
  + 211680 * t ^ 5

/-- The clamped nonic step: `0` on `(-∞,0]`, `1` on `[1,∞)`, `p9` in between. -/
def step9 (t : ℝ) : ℝ := if t ≤ 0 then 0 else if 1 ≤ t then 1 else p9 t

/-- The clamped first derivative `p8` of `step9`; this is `deriv step9`. -/
def st8 (t : ℝ) : ℝ := if t ≤ 0 then 0 else if 1 ≤ t then 0 else p8 t

/-- The clamped second derivative `p7` of `step9`; this is `deriv (deriv step9)`. -/
def st7 (t : ℝ) : ℝ := if t ≤ 0 then 0 else if 1 ≤ t then 0 else p7 t

/-- The clamped third derivative `p6` of `step9`. -/
def st6 (t : ℝ) : ℝ := if t ≤ 0 then 0 else if 1 ≤ t then 0 else p6 t

/-- The clamped fourth derivative `p5` of `step9`. -/
def st5 (t : ℝ) : ℝ := if t ≤ 0 then 0 else if 1 ≤ t then 0 else p5 t

/-- The annulus majorant of the round-6 witness: the product of the rescaled steps.  It is `0`
off `[1/4,4]` and `1` on `[1,2]`. -/
def G (t : ℝ) : ℝ := step9 ((t - 1 / 4) / (3 / 4)) * step9 ((4 - t) / 2)

/-- The round-6 witness at scale `M`: `FM M x = G (x/M)` (`= G ((1/M)·x)`). -/
def FM (M x : ℝ) : ℝ := G (M⁻¹ * x)

end

end Work.FITop4.Witness6
