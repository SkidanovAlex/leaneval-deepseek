import Mathlib
import Submission.Work.FQC.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# `saw (x + 1/2) = -saw x`

The triangle wave `saw x = 1/2 - 2 |fract (x + 1/4) - 1/2|` of `Work.FQC.Defs` is
antiperiodic with period `1/2`: shifting the argument by a half period flips the sign.
This is what makes the MNS twist `ℓ_t` commute with the shift `w ↦ w + 1/2` composed with
conjugation, i.e. with the involution `ι w = conj w + 1/2` on the Écalle cylinder.

The proof reduces to the elementary fact that for `t ∈ [0,1)` the fractional part of
`t + 1/2` is `t + 1/2` when `t < 1/2` and `t - 1/2` otherwise.
-/

namespace Work.FQC

/-- Fractional part of `t + 1/2` for `t` in the first half-period. -/
lemma fract_add_half_of_lt {t : ℝ} (h0 : 0 ≤ t) (h : t < 1 / 2) :
    Int.fract (t + 1 / 2) = t + 1 / 2 := by
  rw [Int.fract_eq_self]
  constructor <;> linarith

/-- Fractional part of `t + 1/2` for `t` in the second half-period. -/
lemma fract_add_half_of_ge {t : ℝ} (h0 : 1 / 2 ≤ t) (h : t < 1) :
    Int.fract (t + 1 / 2) = t - 1 / 2 := by
  have h1 : t + 1 / 2 = (t - 1 / 2) + 1 := by ring
  rw [h1, Int.fract_add_one, Int.fract_eq_self]
  constructor <;> linarith

theorem saw_add_half (x : ℝ) : Work.FQC.saw (x + 1 / 2) = -Work.FQC.saw x := by
  have hA0 : 0 ≤ Int.fract (x + 1 / 4) := Int.fract_nonneg _
  have hA1 : Int.fract (x + 1 / 4) < 1 := Int.fract_lt_one _
  have key : Int.fract (Int.fract (x + 1 / 4) + 1 / 2) = Int.fract (x + 3 / 4) := by
    rw [Int.fract_fract_add]; congr 1; ring
  rw [saw_apply, saw_apply, show x + 1 / 2 + 1 / 4 = x + 3 / 4 by ring, key.symm]
  rcases lt_or_ge (Int.fract (x + 1 / 4)) (1 / 2) with h | h
  · have hB : Int.fract (Int.fract (x + 1 / 4) + 1 / 2) = Int.fract (x + 1 / 4) + 1 / 2 :=
      fract_add_half_of_lt hA0 h
    rw [hB, show Int.fract (x + 1 / 4) + 1 / 2 - 1 / 2 = Int.fract (x + 1 / 4) by ring,
      abs_of_nonneg hA0, abs_of_nonpos (by linarith : Int.fract (x + 1 / 4) - 1 / 2 ≤ 0)]
    ring
  · have hB : Int.fract (Int.fract (x + 1 / 4) + 1 / 2) = Int.fract (x + 1 / 4) - 1 / 2 :=
      fract_add_half_of_ge h hA1
    rw [hB, show Int.fract (x + 1 / 4) - 1 / 2 - 1 / 2 = Int.fract (x + 1 / 4) - 1 by ring,
      abs_of_nonpos (by linarith : Int.fract (x + 1 / 4) - 1 ≤ 0),
      abs_of_nonneg (by linarith : (0 : ℝ) ≤ Int.fract (x + 1 / 4) - 1 / 2)]
    ring

end Work.FQC
