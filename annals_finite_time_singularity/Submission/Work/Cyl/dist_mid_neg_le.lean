import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.Cyl.radial_sq_sub_coord_le_dist_sq

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Cyl

/-- Coordinates of the base point `(b₀, b₁, 0)` of the `x₃ = 0` plane. -/
lemma mid_apply_zero (b : R3) : (!₂[b 0, b 1, (0:ℝ)] : R3) 0 = b 0 := by simp

lemma mid_apply_one (b : R3) : (!₂[b 0, b 1, (0:ℝ)] : R3) 1 = b 1 := by simp

lemma mid_apply_two (b : R3) : (!₂[b 0, b 1, (0:ℝ)] : R3) 2 = 0 := by simp

/-- Coordinates of the reflection `reflZ b`. -/
lemma reflZ_apply_zero (b : R3) : (reflZ b) 0 = b 0 := by simp [reflZ]

lemma reflZ_apply_one (b : R3) : (reflZ b) 1 = b 1 := by simp [reflZ]

lemma reflZ_apply_two (b : R3) : (reflZ b) 2 = - b 2 := by simp [reflZ]

/-- If `a` lies in the closed upper half space and `b` in the open lower half space, then both
`a` and the reflection `reflZ b` are at least as close to the orthogonal projection
`m = (b₀, b₁, 0)` of `b` onto the plane `x₃ = 0` as `a` and `b` are to each other. -/
theorem dist_mid_neg_le {a b : Work.Cyl.R3} (ha : 0 ≤ a 2) (hb : b 2 < 0) :
    dist a (!₂[b 0, b 1, (0:ℝ)]) ≤ dist a b ∧
      dist (Work.Cyl.reflZ b) (!₂[b 0, b 1, (0:ℝ)]) ≤ dist a b := by
  set m : Work.Cyl.R3 := !₂[b 0, b 1, (0:ℝ)] with hm
  have hm0 : m 0 = b 0 := by simp [hm]
  have hm1 : m 1 = b 1 := by simp [hm]
  have hm2 : m 2 = 0 := by simp [hm]
  have hr0 : (Work.Cyl.reflZ b) 0 = b 0 := by simp [Work.Cyl.reflZ]
  have hr1 : (Work.Cyl.reflZ b) 1 = b 1 := by simp [Work.Cyl.reflZ]
  have hr2 : (Work.Cyl.reflZ b) 2 = - b 2 := by simp [Work.Cyl.reflZ]
  constructor
  · -- `(a₂)² ≤ (a₂ - b₂)²` because `a₂ ≥ 0 > b₂`; the remaining coordinates are unchanged.
    have h1 : dist a m ^ 2 ≤ dist a b ^ 2 := by
      rw [Work.Cyl.dist_sq_coords, Work.Cyl.dist_sq_coords, hm0, hm1, hm2]
      nlinarith [ha, hb, sq_nonneg (b 2), sq_nonneg (a 2)]
    nlinarith [dist_nonneg (x := a) (y := m), dist_nonneg (x := a) (y := b), h1]
  · -- Here the distances to `m` only differ in the third coordinate: `(b₂)² ≤ (a₂ - b₂)²`.
    have h1 : dist (Work.Cyl.reflZ b) m ^ 2 ≤ dist a b ^ 2 := by
      rw [Work.Cyl.dist_sq_coords, Work.Cyl.dist_sq_coords, hr0, hr1, hr2, hm0, hm1, hm2]
      nlinarith [ha, hb, sq_nonneg (a 0 - b 0), sq_nonneg (a 1 - b 1)]
    nlinarith [dist_nonneg (x := Work.Cyl.reflZ b) (y := m), dist_nonneg (x := a) (y := b), h1]

end Work.Cyl
