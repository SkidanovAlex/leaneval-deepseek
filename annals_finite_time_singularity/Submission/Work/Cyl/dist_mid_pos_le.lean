import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.Cyl.radial_sq_sub_coord_le_dist_sq

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option linter.unusedSimpArgs false

namespace Work.Cyl

/-!
# The "positive-side" midpoint estimate

For `a` with `a 2 < 0` and `b` with `0 ≤ b 2`, the projection `m = (b 0, b 1, 0)` of `b` onto the
plane `x₃ = 0` is closer to `b` and to the reflection `reflZ a = (a 0, a 1, -a 2)` than `a` and `b`
are to each other:

`dist (reflZ a) m ≤ dist a b`  and  `dist b m ≤ dist a b`.

Both are pure coordinate inequalities.  Writing `u = a 0 - b 0`, `v = a 1 - b 1`,

* `dist (reflZ a) m ^ 2 = u ^ 2 + v ^ 2 + (a 2) ^ 2 ≤ u ^ 2 + v ^ 2 + (a 2 - b 2) ^ 2 = dist a b ^ 2`,
  since the difference of the right and left sides is `b 2 * (b 2 - 2 * a 2) ≥ 0` (`b 2 ≥ 0` and
  `b 2 - 2 * a 2 > 0` because `a 2 < 0`);
* `dist b m ^ 2 = (b 2) ^ 2 ≤ u ^ 2 + v ^ 2 + (a 2 - b 2) ^ 2 = dist a b ^ 2`, since the difference
  is `u ^ 2 + v ^ 2 + (a 2) ^ 2 - 2 * a 2 * b 2 ≥ 0` (`-2 * a 2 * b 2 ≥ 0` as `a 2 < 0 ≤ b 2`).

-/

private lemma dist_sq_reflZ_mid (a b : R3) :
    dist (reflZ a) (!₂[b 0, b 1, (0:ℝ)]) ^ 2
      = (a 0 - b 0) ^ 2 + (a 1 - b 1) ^ 2 + (a 2) ^ 2 := by
  rw [dist_sq_coords]
  simp only [reflZ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]
  ring

private lemma dist_sq_mid (b : R3) :
    dist b (!₂[b 0, b 1, (0:ℝ)]) ^ 2 = (b 2) ^ 2 := by
  rw [dist_sq_coords]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]
  ring

private lemma dist_sq_ab (a b : R3) :
    dist a b ^ 2 = (a 0 - b 0) ^ 2 + (a 1 - b 1) ^ 2 + (a 2 - b 2) ^ 2 := by
  rw [dist_sq_coords]

theorem dist_mid_pos_le {a b : Work.Cyl.R3} (ha : a 2 < 0) (hb : 0 ≤ b 2) :
    dist (Work.Cyl.reflZ a) (!₂[b 0, b 1, (0:ℝ)]) ≤ dist a b ∧
      dist b (!₂[b 0, b 1, (0:ℝ)]) ≤ dist a b := by
  have h1 : dist (reflZ a) (!₂[b 0, b 1, (0:ℝ)]) ^ 2 ≤ dist a b ^ 2 := by
    rw [dist_sq_reflZ_mid, dist_sq_ab]
    have hmul : 0 ≤ b 2 * (b 2 - 2 * a 2) := mul_nonneg hb (by linarith)
    nlinarith [sq_nonneg (a 0 - b 0), sq_nonneg (a 1 - b 1)]
  have h2 : dist b (!₂[b 0, b 1, (0:ℝ)]) ^ 2 ≤ dist a b ^ 2 := by
    rw [dist_sq_mid, dist_sq_ab]
    have hmul : 0 ≤ 2 * (-a 2) * b 2 := mul_nonneg (by linarith) hb
    nlinarith [sq_nonneg (a 0 - b 0), sq_nonneg (a 1 - b 1), sq_nonneg (a 2)]
  constructor
  · have h := sq_le_sq.mp h1
    rwa [abs_of_nonneg dist_nonneg, abs_of_nonneg dist_nonneg] at h
  · have h := sq_le_sq.mp h2
    rwa [abs_of_nonneg dist_nonneg, abs_of_nonneg dist_nonneg] at h

end Work.Cyl
