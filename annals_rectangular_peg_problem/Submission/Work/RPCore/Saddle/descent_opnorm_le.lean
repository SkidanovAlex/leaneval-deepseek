import Mathlib
import Submission.Work.RPCore.Saddle.descent_defs

/-!
# Operator-norm bound for the coordinates of a functional on `D k l`

For `L : D k l →L[ℝ] ℝ` the coordinates `cval L`, `g1 L`, `g2 L` are defined in
`descent_defs`.  Here we show that the coordinate decomposition

`L w = cval L * w.1 + ⟪g1 L, w.2.1⟫ + ⟪g2 L, w.2.2⟫`

entails the operator-norm bound

`‖L‖ ≤ |cval L| + ‖g1 L‖ + ‖g2 L‖`.
-/

namespace Work.RPCore.Saddle

open scoped RealInnerProductSpace

noncomputable section

/-- The coordinate decomposition of a continuous linear functional on `D k l`: it splits
according to the `a`-coordinate and the Riesz vectors of the two blocks. -/
private theorem descent_apply {k l : ℕ} (L : D k l →L[ℝ] ℝ) (w : D k l) :
    L w = cval L * w.1 + inner ℝ (g1 L) w.2.1 + inner ℝ (g2 L) w.2.2 := by
  have hL0 : L (d0 k l w.1) = cval L * w.1 := by
    have h : d0 k l w.1 = w.1 • d0 k l 1 := by simp [d0]
    rw [h, map_smul, smul_eq_mul]
    rw [mul_comm, cval]
  have hL1 : L (d1 k l w.2.1) = inner ℝ (g1 L) w.2.1 := by
    rw [g1, InnerProductSpace.toDual_symm_apply]; rfl
  have hL2 : L (d2 k l w.2.2) = inner ℝ (g2 L) w.2.2 := by
    rw [g2, InnerProductSpace.toDual_symm_apply]; rfl
  have hdec : w = d0 k l w.1 + d1 k l w.2.1 + d2 k l w.2.2 := by
    obtain ⟨a, x, y⟩ := w
    simp [d0, d1, d2]
  conv_lhs => rw [hdec]
  rw [map_add, map_add, hL0, hL1, hL2]

theorem descent_opnorm_le {k l : ℕ} (L : D k l →L[ℝ] ℝ) :
    ‖L‖ ≤ |cval L| + ‖g1 L‖ + ‖g2 L‖ := by
  refine ContinuousLinearMap.opNorm_le_bound L (by positivity) ?_
  intro w
  rw [descent_apply L w, Real.norm_eq_abs]
  have htri : |cval L * w.1 + inner ℝ (g1 L) w.2.1 + inner ℝ (g2 L) w.2.2|
      ≤ |cval L * w.1| + |inner ℝ (g1 L) w.2.1| + |inner ℝ (g2 L) w.2.2| := by
    have h1 := abs_add_le (cval L * w.1 + inner ℝ (g1 L) w.2.1) (inner ℝ (g2 L) w.2.2)
    have h2 := abs_add_le (cval L * w.1) (inner ℝ (g1 L) w.2.1)
    linarith
  have hA : |cval L * w.1| ≤ |cval L| * ‖w‖ := by
    rw [abs_mul]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    rw [← Real.norm_eq_abs]
    exact norm_fst_le w
  have hB : |inner ℝ (g1 L) w.2.1| ≤ ‖g1 L‖ * ‖w‖ := by
    have h := norm_inner_le_norm (𝕜 := ℝ) (g1 L) w.2.1
    rw [Real.norm_eq_abs] at h
    refine le_trans h (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
    exact le_trans (norm_fst_le w.2) (norm_snd_le w)
  have hC : |inner ℝ (g2 L) w.2.2| ≤ ‖g2 L‖ * ‖w‖ := by
    have h := norm_inner_le_norm (𝕜 := ℝ) (g2 L) w.2.2
    rw [Real.norm_eq_abs] at h
    refine le_trans h (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
    exact le_trans (norm_snd_le w.2) (norm_snd_le w)
  calc |cval L * w.1 + inner ℝ (g1 L) w.2.1 + inner ℝ (g2 L) w.2.2|
      ≤ |cval L * w.1| + |inner ℝ (g1 L) w.2.1| + |inner ℝ (g2 L) w.2.2| := htri
    _ ≤ |cval L| * ‖w‖ + ‖g1 L‖ * ‖w‖ + ‖g2 L‖ * ‖w‖ := by linarith
    _ = (|cval L| + ‖g1 L‖ + ‖g2 L‖) * ‖w‖ := by ring

end

end Work.RPCore.Saddle
