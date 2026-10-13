import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.FTS.FireFix.Defs
import Submission.Work.Cyl.fderiv_angularVec_apply
import Submission.Work.Cyl.fderiv_radial_apply

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.FireFix.Clauses

/-- Off the axis, `e_r, e_θ, e₃` is an orthonormal frame, hence it *determines* a continuous
linear operator: every `u` writes as `⟪u, e_r⟫ • e_r + ⟪u, e_θ⟫ • e_θ + ⟪u, e₃⟫ • e₃`
(`Work.Cyl.decomposition`), so `‖L u‖ ≤ ‖u‖ (‖L e_r‖ + ‖L e_θ‖ + ‖L e₃‖)` by Cauchy–Schwarz.
The bound on the operator norm follows. -/
theorem opNorm_le_frame (L : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3))
    (x : EuclideanSpace ℝ (Fin 3)) (hr : 0 < Work.Cyl.radial x) :
    ‖L‖ ≤ ‖L (Work.Cyl.eR x)‖ + ‖L (Work.Cyl.eTheta x)‖ + ‖L Work.Cyl.eZ‖ := by
  have hrne : Work.Cyl.radial x ≠ 0 := ne_of_gt hr
  have heZ : ‖(Work.Cyl.eZ : Work.Cyl.R3)‖ = 1 := by
    simp [Work.Cyl.eZ, FiniteTimeSingularity.e]
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun u => ?_
  -- the frame at `x` is a basis, so `u` is the sum of its projections on it
  have hdecE : inner ℝ u (Work.Cyl.eR x) • Work.Cyl.eR x
      + inner ℝ u (Work.Cyl.eTheta x) • Work.Cyl.eTheta x
      + inner ℝ u Work.Cyl.eZ • Work.Cyl.eZ = u := by
    have h := Work.Cyl.decomposition (fun _ : Work.Cyl.R3 => u) x hrne
    simpa [Work.Cyl.compR, Work.Cyl.compT, Work.Cyl.compZ] using h.symm
  have hLu : L u = inner ℝ u (Work.Cyl.eR x) • L (Work.Cyl.eR x)
      + inner ℝ u (Work.Cyl.eTheta x) • L (Work.Cyl.eTheta x)
      + inner ℝ u (Work.Cyl.eZ : Work.Cyl.R3) • L Work.Cyl.eZ := by
    conv_lhs => rw [← hdecE]
    simp only [map_add, map_smul]
  -- Cauchy–Schwarz on the frame (which is orthonormal)
  have hcS : |inner ℝ u (Work.Cyl.eR x)| ≤ ‖u‖ := by
    have h := abs_real_inner_le_norm u (Work.Cyl.eR x)
    rwa [Work.Cyl.norm_eR x hrne, mul_one] at h
  have hcT : |inner ℝ u (Work.Cyl.eTheta x)| ≤ ‖u‖ := by
    have h := abs_real_inner_le_norm u (Work.Cyl.eTheta x)
    rwa [Work.Cyl.norm_eTheta x hrne, mul_one] at h
  have hcZ : |inner ℝ u (Work.Cyl.eZ : Work.Cyl.R3)| ≤ ‖u‖ := by
    have h := abs_real_inner_le_norm u (Work.Cyl.eZ : Work.Cyl.R3)
    rwa [heZ, mul_one] at h
  have hA : |inner ℝ u (Work.Cyl.eR x)| * ‖L (Work.Cyl.eR x)‖ ≤ ‖u‖ * ‖L (Work.Cyl.eR x)‖ :=
    mul_le_mul_of_nonneg_right hcS (norm_nonneg _)
  have hB : |inner ℝ u (Work.Cyl.eTheta x)| * ‖L (Work.Cyl.eTheta x)‖
      ≤ ‖u‖ * ‖L (Work.Cyl.eTheta x)‖ :=
    mul_le_mul_of_nonneg_right hcT (norm_nonneg _)
  have hC : |inner ℝ u (Work.Cyl.eZ : Work.Cyl.R3)| * ‖L Work.Cyl.eZ‖
      ≤ ‖u‖ * ‖L Work.Cyl.eZ‖ :=
    mul_le_mul_of_nonneg_right hcZ (norm_nonneg _)
  calc ‖L u‖
      = ‖inner ℝ u (Work.Cyl.eR x) • L (Work.Cyl.eR x)
          + inner ℝ u (Work.Cyl.eTheta x) • L (Work.Cyl.eTheta x)
          + inner ℝ u (Work.Cyl.eZ : Work.Cyl.R3) • L Work.Cyl.eZ‖ := by rw [hLu]
    _ ≤ ‖inner ℝ u (Work.Cyl.eR x) • L (Work.Cyl.eR x)
          + inner ℝ u (Work.Cyl.eTheta x) • L (Work.Cyl.eTheta x)‖
        + ‖inner ℝ u (Work.Cyl.eZ : Work.Cyl.R3) • L Work.Cyl.eZ‖ :=
        norm_add_le _ _
    _ ≤ (‖inner ℝ u (Work.Cyl.eR x) • L (Work.Cyl.eR x)‖
          + ‖inner ℝ u (Work.Cyl.eTheta x) • L (Work.Cyl.eTheta x)‖)
        + ‖inner ℝ u (Work.Cyl.eZ : Work.Cyl.R3) • L Work.Cyl.eZ‖ := by
        gcongr 1
        exact norm_add_le _ _
    _ = |inner ℝ u (Work.Cyl.eR x)| * ‖L (Work.Cyl.eR x)‖
        + |inner ℝ u (Work.Cyl.eTheta x)| * ‖L (Work.Cyl.eTheta x)‖
        + |inner ℝ u (Work.Cyl.eZ : Work.Cyl.R3)| * ‖L Work.Cyl.eZ‖ := by
        simp only [norm_smul, Real.norm_eq_abs]
    _ ≤ ‖u‖ * ‖L (Work.Cyl.eR x)‖ + ‖u‖ * ‖L (Work.Cyl.eTheta x)‖
        + ‖u‖ * ‖L Work.Cyl.eZ‖ := by
        linarith
    _ = (‖L (Work.Cyl.eR x)‖ + ‖L (Work.Cyl.eTheta x)‖ + ‖L Work.Cyl.eZ‖) * ‖u‖ := by
        ring

end Work.FTS.FireFix.Clauses
