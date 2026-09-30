import Mathlib
import Submission.Work.Cusp.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Cusp

/-- `off t` is nonnegative: it is the distance of `t` to the nearest half-integer, which is `≤ 1/2`
because `Int.fract t ∈ [0,1)`. -/
lemma off_nonneg (t : ℝ) : 0 ≤ off t := by
  rw [off, sub_nonneg, abs_le]
  exact ⟨by linarith [Int.fract_nonneg t], by linarith [Int.fract_lt_one t]⟩

/-- `off t ≤ 1/2`. -/
lemma off_le_half (t : ℝ) : off t ≤ 1/2 := by
  rw [off]
  have := abs_nonneg (Int.fract t - 1/2)
  linarith

/-- The square of `off t` is at most `1/4`. -/
lemma off_sq_le (t : ℝ) : (off t) ^ 2 ≤ 1/4 := by
  have h1 := off_nonneg t
  have h2 := off_le_half t
  nlinarith

/-- Each of the three coordinate offsets contributes at most `1/4`, so the sum inside `beta` is at
most `3/4`, and `9/4 - 3/4 = 3/2 > 0`.  Hence the ceiling `β` is strictly positive everywhere. -/
theorem beta_pos (x : E3) : 0 < beta x := by
  rw [beta]
  apply Real.sqrt_pos_of_pos
  rw [Fin.sum_univ_three]
  have h0 := off_sq_le (x 0)
  have h1 := off_sq_le (x 1)
  have h2 := off_sq_le (x 2)
  linarith

end Work.Cusp
