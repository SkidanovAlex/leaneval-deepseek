import Mathlib
import Submission.Work.EQ.LocModelDefs

namespace Work.EQ

open Complex

/-- For a real point `P = x` and a real centre `c`, the chord involution acts on the real axis as
`chordMap c (x:ℂ) = (x - (x-c)/|x-c| : ℝ)`.  (Division by `0` is `0`, so this also holds at
`x = c`, but no hypothesis is needed either way.) -/
lemma chordMap_ofReal (c x : ℝ) :
    chordMap (c : ℂ) ((x : ℝ) : ℂ) = ((x - (x - c) / |x - c| : ℝ) : ℂ) := by
  unfold chordMap
  rw [show ((x : ℝ) : ℂ) - (c : ℂ) = ((x - c : ℝ) : ℂ) by push_cast; ring]
  rw [show ‖((x - c : ℝ) : ℂ)‖ = |x - c| from RCLike.norm_ofReal (K := ℂ) (x - c)]
  push_cast
  ring

/-- On the real interval `(-1 - a/2, a/2)` between the two "antipodes" `O₁ - 1` and `O₂ = a/2`,
the equichordal two-step map `eqT a` fixes the real axis pointwise: the two unit chord steps
about `O₂` and then about `O₁` compose to the identity. -/
theorem lmAxisFixed {a x : ℝ} (h1 : -1 - a/2 < x) (h2 : x < a/2) :
    Work.EQ.eqT a ((x : ℝ) : ℂ) = ((x : ℝ) : ℂ) := by
  have hO1 : O1_sym a = ((-(a / 2) : ℝ) : ℂ) := by rw [O1_sym]; push_cast; ring
  have hO2 : O2_sym a = ((a / 2 : ℝ) : ℂ) := rfl
  rw [eqT, hO1, hO2]
  -- first step: the chord through `O₂` sends `x` to `x + 1`
  rw [chordMap_ofReal (a / 2) x]
  have habs : |x - a / 2| = a / 2 - x := by rw [abs_of_neg (by linarith)]; ring
  rw [habs]
  have hdiv : (x - a / 2) / (a / 2 - x) = -1 := by
    rw [div_eq_iff (by linarith : a / 2 - x ≠ 0)]; ring
  rw [hdiv]
  -- second step: the chord through `O₁` sends `x + 1` back to `x`
  rw [show (x - -1 : ℝ) = x + 1 by ring]
  rw [chordMap_ofReal (-(a / 2)) (x + 1)]
  have habs2 : |x + 1 - -(a / 2)| = x + 1 + a / 2 := by
    rw [abs_of_pos (by linarith)]; ring
  rw [habs2]
  have hdiv2 : (x + 1 - -(a / 2)) / (x + 1 + a / 2) = 1 := by
    rw [div_eq_iff (by linarith : x + 1 + a / 2 ≠ 0)]; ring
  rw [hdiv2]
  push_cast
  ring

end Work.EQ
