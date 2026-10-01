/-
# ZeroFreeTables — XY/XySupLargeT

The large-`t` sup-estimates of Xylouris §2 (order-2 case, HB (9.16) with `λ* = 1`):

  `xySup1 lam t = 14900 Re F(-1+it) - 30480 Re F(lam-1+it)`,
  `xySup2 lam t =  1250 Re F(-1+it) -  6000 Re F(lam-1+it)`

are even in `t`, and satisfy `xySup1 ≤ 60`, `xySup2 ≤ 160` for
`518/1000 ≤ lam ≤ 628/1000` and `t ≥ 13`.

This file is a thin wrapper: the proof lives in `XY.XySupLargeTB`.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.XYDefs
import Submission.Work.ZeroFreeTables.XY.XySupLargeTB

namespace Work.ZeroFreeTables.XY

theorem XySupLargeT :
    (∀ (lam t : ℝ), xySup1 lam (-t) = xySup1 lam t)
  ∧ (∀ (lam t : ℝ), xySup2 lam (-t) = xySup2 lam t)
  ∧ (∀ (lam t : ℝ), 518/1000 ≤ lam → lam ≤ 628/1000 → 13 ≤ t → xySup1 lam t ≤ 60)
  ∧ (∀ (lam t : ℝ), 518/1000 ≤ lam → lam ≤ 628/1000 → 13 ≤ t → xySup2 lam t ≤ 160) :=
  XySupLargeTB

end Work.ZeroFreeTables.XY
