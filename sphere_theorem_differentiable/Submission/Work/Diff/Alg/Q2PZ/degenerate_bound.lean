import Mathlib
import Submission.Work.Diff.Alg.q2p_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The degenerate case of the `Q²` estimate

`R4 R x y z w` is multilinear in its four vector arguments, so it vanishes as soon as one of them
is the zero vector. On the other hand the bound

`(2 / 3) * (b - a) * (‖x‖ ‖y‖ ‖z‖ ‖w‖)`

also vanishes, because `dot 0 0 = 0` and hence one of the four square roots is `0`. So in the
degenerate case the inequality reduces to `0 ≤ 0`, with no hypothesis on `R`, `a` or `b`
(in particular `b - a` may have either sign).

This is the case that the "non-degenerate" proof of the `Q²` estimate discards.
-/

namespace Work.Diff.Alg.Q2PZ

/-- If one of the four vectors is zero, both sides of the `2/3 (b - a) ‖x‖‖y‖‖z‖‖w‖` bound are
zero. -/
theorem degenerate_bound {n : ℕ} (R : Submission.Diff.Alg.Curv4 n) (a b : ℝ)
    {x y z w : Fin n → ℝ} (h : x = 0 ∨ y = 0 ∨ z = 0 ∨ w = 0) :
    |Submission.Diff.Alg.R4 R x y z w| ≤ (2 / 3) * (b - a) *
      (Real.sqrt (Submission.Diff.Alg.dot x x) * Real.sqrt (Submission.Diff.Alg.dot y y) *
       Real.sqrt (Submission.Diff.Alg.dot z z) * Real.sqrt (Submission.Diff.Alg.dot w w)) := by
  rcases h with h | h | h | h <;> rw [h] <;> simp [Submission.Diff.Alg.R4, Submission.Diff.Alg.dot]

end Work.Diff.Alg.Q2PZ
