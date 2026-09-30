import Mathlib
import Submission.Work.RTInstance.Models

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.RTInstance

/-- `posExt f c r > 0` under the hypotheses that `f` is positive on `[c, ∞)` and nonnegative on
`[0, c)`: for `r ≤ 0` the transition weight vanishes so `posExt f c r = c > 0`, for `0 ≤ r < c`
the value is a nonnegative combination of `f r` and of `c · (1 - smoothTransition (r / c)) > 0`,
and for `c ≤ r` it is `f r > 0`. -/
theorem posExt_pos (f : ℝ → ℝ) (c : ℝ) (hc : 0 < c)
    (hf : ∀ r, c ≤ r → 0 < f r) (hfnn : ∀ r, 0 ≤ r → r < c → 0 ≤ f r) (r : ℝ) :
    0 < posExt f c r := by
  rw [posExt]
  rcases le_or_gt r 0 with hr | hr
  · rw [Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg hr hc.le)]
    ring_nf
    exact hc
  · rcases lt_or_ge r c with hrc | hcr
    · have hT : Real.smoothTransition (r / c) < 1 :=
        Real.smoothTransition.lt_one_of_lt_one (by rw [div_lt_one hc]; exact hrc)
      have hTnn := Real.smoothTransition.nonneg (r / c)
      have hfr := hfnn r hr.le hrc
      have h1 : 0 < 1 - Real.smoothTransition (r / c) := by linarith
      nlinarith [mul_nonneg hfr hTnn, mul_pos hc h1]
    · rw [Real.smoothTransition.one_of_one_le (by rw [one_le_div hc]; exact hcr)]
      simpa using hf r hcr

end Work.RTInstance
