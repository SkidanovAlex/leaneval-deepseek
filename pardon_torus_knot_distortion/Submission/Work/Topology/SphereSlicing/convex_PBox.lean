import Mathlib
import Submission.Work.Topology.SphereSlicing.Defs

/-!
# `PBox` is convex

`Submission.PBox r c σ` is the open box
`{y | ∀ i, |y (σ i) - c (σ i)| < boxSide i * r}`, the intersection of the six open coordinate
slabs of Pardon's box.  It is convex for every `r : ℝ`: no positivity of `r` is needed (an empty
box is convex), because convexity is a coordinatewise statement.  Concretely, for a convex
combination `a • x + b • y` of two members, each coordinate is the corresponding combination of
the coordinates of `x` and `y`, and the triangle inequality plus the coordinate bounds gives

`|a (x_i - c_i) + b (y_i - c_i)| ≤ a |x_i - c_i| + b |y_i - c_i| < a A + b A = A`

with `A = boxSide i * r`, using `a + b = 1` in the last step.
-/

namespace Work.Topology.SphereSlicing

/-- A convex-combination bound for two coordinates: if `|u| < A` and `|v| < A` then any convex
combination of `|u|` and `|v|` is strictly below the same convex combination of `A` with `A`.
The strictness comes from the coefficient which is positive (one of `a`, `b` is, since they are
nonnegative and sum to one). -/
private theorem abs_convex_combo_lt {u v A a b : ℝ} (hu : |u| < A) (hv : |v| < A)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    a * |u| + b * |v| < a * A + b * A := by
  rcases eq_or_lt_of_le ha with h | h
  · -- `a = 0`, hence `b = 1` and the second term gives strictness
    have hb1 : b = 1 := by linarith
    subst h
    rw [hb1]
    simpa using hv
  · -- `a > 0`, so the first term gives strictness
    exact add_lt_add_of_lt_of_le (mul_lt_mul_of_pos_left hu h)
      (mul_le_mul_of_nonneg_left (le_of_lt hv) hb)

theorem convex_PBox (r : ℝ) (c : LeanEval.KnotTheory.PardonDistortion.R3) (σ : Equiv.Perm (Fin 3)) :
    Convex ℝ (Submission.PBox r c σ) := by
  intro x hx y hy a b ha hb hab i
  -- the coordinate bounds for `x` and `y`
  have hu : |x.ofLp (σ i) - c.ofLp (σ i)| < Submission.boxSide i * r := hx i
  have hv : |y.ofLp (σ i) - c.ofLp (σ i)| < Submission.boxSide i * r := hy i
  -- the coordinate of a convex combination is the convex combination of the coordinates
  have hid : (a • x + b • y).ofLp (σ i) - c.ofLp (σ i)
      = a * (x.ofLp (σ i) - c.ofLp (σ i)) + b * (y.ofLp (σ i) - c.ofLp (σ i)) := by
    calc (a • x + b • y).ofLp (σ i) - c.ofLp (σ i)
        = a * x.ofLp (σ i) + b * y.ofLp (σ i) - c.ofLp (σ i) := by simp
      _ = a * x.ofLp (σ i) + b * y.ofLp (σ i) - (a + b) * c.ofLp (σ i) := by
            rw [hab, one_mul]
      _ = a * (x.ofLp (σ i) - c.ofLp (σ i)) + b * (y.ofLp (σ i) - c.ofLp (σ i)) := by ring
  rw [hid]
  -- triangle inequality, then the coordinate bounds
  have htri : |a * (x.ofLp (σ i) - c.ofLp (σ i)) + b * (y.ofLp (σ i) - c.ofLp (σ i))|
      ≤ a * |x.ofLp (σ i) - c.ofLp (σ i)| + b * |y.ofLp (σ i) - c.ofLp (σ i)| := by
    calc _ ≤ |a * (x.ofLp (σ i) - c.ofLp (σ i))|
            + |b * (y.ofLp (σ i) - c.ofLp (σ i))| := abs_add_le _ _
      _ = a * |x.ofLp (σ i) - c.ofLp (σ i)| + b * |y.ofLp (σ i) - c.ofLp (σ i)| := by
            rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
  have hsum : a * |x.ofLp (σ i) - c.ofLp (σ i)| + b * |y.ofLp (σ i) - c.ofLp (σ i)|
      < a * (Submission.boxSide i * r) + b * (Submission.boxSide i * r) :=
    abs_convex_combo_lt hu hv ha hb hab
  have heq : a * (Submission.boxSide i * r) + b * (Submission.boxSide i * r)
      = Submission.boxSide i * r := by rw [← add_mul, hab, one_mul]
  linarith [htri, hsum, heq]

end Work.Topology.SphereSlicing
