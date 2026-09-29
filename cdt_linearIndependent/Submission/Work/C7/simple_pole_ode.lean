import Mathlib
import Submission.Work.C7.deps

set_option linter.unusedVariables false

/-!
# `Work.C7.simple_pole_ode`

A rational function `b` cannot satisfy `dRat b = u + v` when `u` has the same order of vanishing
as `b` at `α` and `v` has a simple pole (`ordAt α v = -1`) there.

The two facts doing the work are the order calculus of `Submission.CDT`:

* `ordAt_dRat_eq_sub_one` — at a zero or a pole, differentiation lowers the order of vanishing by
  exactly one;
* `ordAt_dRat_ne_neg_one` — the derivative of a rational function never has a *simple* pole;
* `ordAt_add_of_lt` (strict dominance) and `min_ordAt_le_ordAt_add` (the ultrametric bound) for
  the order of a sum of two nonzero rational functions.

Let `n = ordAt α b`.  Since `ordAt α u = n` and `ordAt α v = -1`, we split on `n` versus `-1`.

* `n < -1`: then `ordAt α u = n < -1 = ordAt α v`, so strict dominance gives
  `ordAt α (u + v) = n`.  As `n ≠ 0`, the derivative formula gives `ordAt α (dRat b) = n - 1`,
  so `dRat b = u + v` forces `n - 1 = n`, absurd.
* `n = -1`: the derivative formula gives `ordAt α (dRat b) = -2`, hence `dRat b = u + v ≠ 0`;
  the `min` bound now gives `min (ordAt α u) (ordAt α v) = -1 ≤ ordAt α (u + v) = -2`.  Absurd.
* `-1 < n`: here `-1 = ordAt α v < ordAt α u`, so strict dominance gives
  `ordAt α (dRat b) = ordAt α (u + v) = -1`: a simple pole, contradicting
  `ordAt_dRat_ne_neg_one`.
-/

namespace Work.C7

open Submission.CDT

theorem simple_pole_ode {K : Type*} [Field K] [CharZero K] {α : K}
    {b u v : RatFunc K} (hb : b ≠ 0) (hu : u ≠ 0) (hv : v ≠ 0)
    (huord : Submission.CDT.ordAt α u = Submission.CDT.ordAt α b)
    (hvord : Submission.CDT.ordAt α v = -1)
    (h : Submission.CDT.dRat b = u + v) : False := by
  rcases lt_trichotomy (ordAt α b) (-1) with hlt | heq | hgt
  · -- `ordAt α b < -1` is the strict-dominance regime for `u + v`, and `ordAt α b ≠ 0`.
    have h1 : ordAt α (u + v) = ordAt α b := by
      rw [ordAt_add_of_lt α hu hv (by rw [huord, hvord]; exact hlt), huord]
    have hne : ordAt α b ≠ 0 := by omega
    have h2 : ordAt α (u + v) = ordAt α b - 1 := by
      rw [← h, ordAt_dRat_eq_sub_one b α hne]
    omega
  · -- `ordAt α b = -1`: both summands have order `-1`, so the sum has order `≥ -1`,
    -- but `dRat b = u + v` has order `-2`.
    have hne : ordAt α b ≠ 0 := by omega
    have h2 : ordAt α (u + v) = -2 := by
      rw [← h, ordAt_dRat_eq_sub_one b α hne, heq]
      norm_num
    have huv : u + v ≠ 0 := by
      intro h0
      rw [h0, ordAt_zero] at h2
      norm_num at h2
    have hm := min_ordAt_le_ordAt_add α huv
    rw [huord, hvord, heq] at hm
    rw [min_self, h2] at hm
    omega
  · -- `-1 < ordAt α b`: `dRat b = u + v` has a simple pole, which is impossible.
    have h1 : ordAt α (u + v) = -1 := by
      rw [add_comm u v, ordAt_add_of_lt α hv hu (by rw [hvord, huord]; exact hgt), hvord]
    exact ordAt_dRat_ne_neg_one α b (by rw [h]; exact h1)

end Work.C7
