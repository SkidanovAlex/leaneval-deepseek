import Mathlib
import Submission.Work.RPCore.Saddle.descent_defs

/-!
# The coordinate identity for a continuous linear functional on `D k l`

For `L : D k l →L[ℝ] ℝ` and `w : ℝ × (EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin l))` we
prove the expansion used throughout the continuous descent-direction construction:

`L w = cval L * w.1 + ⟪g1 L, w.2.1⟫ + ⟪g2 L, w.2.2⟫`.

The point is the canonical decomposition `w = d0 w.1 + d1 w.2.1 + d2 w.2.2` together with the
definition of `cval`, `g1`, `g2` (the latter two as Fréchet–Riesz representatives of the
restrictions of `L` to the two Euclidean blocks).
-/

namespace Work.RPCore.Saddle

open scoped RealInnerProductSpace

noncomputable section

/-- `g1 L` represents the restriction of `L` to the `k`-block. -/
theorem inner_g1 {k l : ℕ} (L : D k l →L[ℝ] ℝ) (x : EuclideanSpace ℝ (Fin k)) :
    inner ℝ (g1 L) x = L (d1 k l x) := by
  rw [g1, InnerProductSpace.toDual_symm_apply]
  rfl

/-- `g2 L` represents the restriction of `L` to the `l`-block. -/
theorem inner_g2 {k l : ℕ} (L : D k l →L[ℝ] ℝ) (y : EuclideanSpace ℝ (Fin l)) :
    inner ℝ (g2 L) y = L (d2 k l y) := by
  rw [g2, InnerProductSpace.toDual_symm_apply]
  rfl

/-- `cval L` is the value of `L` on the unit vector of the first coordinate. -/
theorem apply_d0 {k l : ℕ} (L : D k l →L[ℝ] ℝ) (a : ℝ) :
    L (d0 k l a) = cval L * a := by
  rw [show d0 k l a = a • d0 k l 1 from by simp [d0], map_smul, cval]
  simp [smul_eq_mul, mul_comm]

/-- The canonical decomposition of a point of `D k l` into its three components. -/
theorem self_eq_d0_d1_d2 {k l : ℕ} (w : D k l) :
    w = d0 k l w.1 + d1 k l w.2.1 + d2 k l w.2.2 := by
  ext <;> simp [d0, d1, d2]

theorem descent_identity {k l : ℕ} (L : D k l →L[ℝ] ℝ) (w : D k l) :
    L w = cval L * w.1 + inner ℝ (g1 L) w.2.1 + inner ℝ (g2 L) w.2.2 := by
  conv_lhs => rw [self_eq_d0_d1_d2 w]
  rw [map_add, map_add, apply_d0, inner_g1, inner_g2]

end

end Work.RPCore.Saddle
