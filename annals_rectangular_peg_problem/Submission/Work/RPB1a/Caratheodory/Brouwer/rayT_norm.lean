import Mathlib
import Submission.Work.RPB1a.Caratheodory.Brouwer.RetractDefs

namespace Work.RPB1a.Caratheodory.Brouwer

/-- `rayT p d` is a genuine root of the ray equation `‖p + t • d‖ = 1`: the point `p + rayT p d • d`
of the ray from `p` in direction `d` lies on the unit sphere.  Needs `d ≠ 0` (so that the formula
does not divide by zero) and `‖p‖ ≤ 1` (so that the ray really reaches the sphere). -/
lemma rayT_norm {N : ℕ} (p d : EuclideanSpace ℝ (Fin N)) (hd : d ≠ 0) (hp : ‖p‖ ≤ 1) :
    ‖p + rayT p d • d‖ = 1 := by
  have hd2 : 0 < ‖d‖ ^ 2 := pow_pos (norm_pos_iff.mpr hd) 2
  have hpc : ‖p‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg p, hp]
  -- The discriminant is nonnegative, so the square root is genuine.
  have hΔ : 0 ≤ (inner ℝ p d) ^ 2 + ‖d‖ ^ 2 * (1 - ‖p‖ ^ 2) := by
    have h1 : 0 ≤ ‖d‖ ^ 2 * (1 - ‖p‖ ^ 2) :=
      mul_nonneg (by positivity) (by linarith)
    nlinarith [sq_nonneg (inner ℝ p d), h1]
  have hs2 : (Real.sqrt ((inner ℝ p d) ^ 2 + ‖d‖ ^ 2 * (1 - ‖p‖ ^ 2))) ^ 2
      = (inner ℝ p d) ^ 2 + ‖d‖ ^ 2 * (1 - ‖p‖ ^ 2) := Real.sq_sqrt hΔ
  -- `‖d‖² · rayT p d` is exactly the (nonnegative) root `-⟪p,d⟫ + √Δ`.
  have hbt : ‖d‖ ^ 2 * rayT p d
      = -(inner ℝ p d) + Real.sqrt ((inner ℝ p d) ^ 2 + ‖d‖ ^ 2 * (1 - ‖p‖ ^ 2)) := by
    rw [rayT]
    field_simp
  have hkey : (‖d‖ ^ 2 * rayT p d + inner ℝ p d) ^ 2
      = (inner ℝ p d) ^ 2 + ‖d‖ ^ 2 * (1 - ‖p‖ ^ 2) := by
    rw [hbt, show -(inner ℝ p d)
        + Real.sqrt ((inner ℝ p d) ^ 2 + ‖d‖ ^ 2 * (1 - ‖p‖ ^ 2)) + inner ℝ p d
        = Real.sqrt ((inner ℝ p d) ^ 2 + ‖d‖ ^ 2 * (1 - ‖p‖ ^ 2)) by ring, hs2]
  -- Squaring out gives the quadratic relation solved by `rayT`.
  have h1 : ‖d‖ ^ 2 * (‖d‖ ^ 2 * (rayT p d) ^ 2 + 2 * inner ℝ p d * rayT p d)
      = ‖d‖ ^ 2 * (1 - ‖p‖ ^ 2) := by
    nlinarith [hkey]
  have hquad : ‖d‖ ^ 2 * (rayT p d) ^ 2 + 2 * inner ℝ p d * rayT p d = 1 - ‖p‖ ^ 2 :=
    mul_left_cancel₀ (ne_of_gt hd2) h1
  -- Hence the norm squared of the point on the ray is `1`.
  have hns : ‖p + rayT p d • d‖ ^ 2 = 1 := by
    rw [norm_add_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    nlinarith [hquad]
  have hnn : (0 : ℝ) ≤ ‖p + rayT p d • d‖ := norm_nonneg _
  rcases sq_eq_one_iff.mp hns with h | h
  · exact h
  · rw [h] at hnn
    norm_num at hnn

end Work.RPB1a.Caratheodory.Brouwer
